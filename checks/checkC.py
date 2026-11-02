"""Claim C2/C3: are concurrent histories representable by precedence and weak precedence alone?

For each start state s (configuration (s,{})), enumerate the complete valid runs in which each
action begins at most once.  Group them by (set of actions X, final state s'): a history H.
  IO(H)   = set of interval orders (as the precedence relation <, a<b iff E_a before B_b) of runs in H
  inv(H)  = (<_H, weak_H): <_H = pairs ordered in every run; weak_H = pairs (a,b) with b<a in no run
  ext(H)  = all interval orders o on X with <_H within <_o and no b<_o a for (a,b) in weak_H
  REP(H)  : ext(H) == IO(H)      (H is the set of maximal extensions of its invariant structure)
  IOC(H)  : every word of X^{BE} whose interval order is in IO(H) is a run of H
            (the interval order abstraction loses nothing: swap closure within H)
Per system: REP = all histories representable; IOC = all histories io-closed.
Also recorded: whether the run set from (s,{}) is swap-closed (JR) and transparency T1 of start.
"""
import sys, random, itertools, pickle, collections
import os
OUT = os.environ.get('CHECK_OUT', os.path.dirname(os.path.abspath(__file__)))  # where result pickles are written
from gas import *
from checkA2 import run_from


def io_of(word, X):
    """precedence relation of a complete word over X: a<b iff E_a before B_b."""
    posB = {}; posE = {}
    for i, (k, a) in enumerate(word):
        (posB if k == 'B' else posE)[a] = i
    return frozenset((a, b) for a in X for b in X if a != b and posE[a] < posB[b])


_all_words_cache = {}
def all_words(X):
    X = tuple(sorted(X))
    if X in _all_words_cache:
        return _all_words_cache[X]
    evs = [('B', a) for a in X] + [('E', a) for a in X]
    out = []
    for p in itertools.permutations(evs):
        ok = True
        seen = set()
        for k, a in p:
            if k == 'E' and a not in seen:
                ok = False; break
            if k == 'B': seen.add(a)
        if ok:
            out.append(p)
    _all_words_cache[X] = out
    return out


GROUPING = 'diamond'   # 'diamond' (equivalence under adjacent swaps that are valid both ways) or 'final'


def histories(S, s):
    """complete valid runs from (s,{}) with each action beginning at most once, grouped into
    concurrent histories.  GROUPING='final': by (action set, final state).  GROUPING='diamond':
    equivalence classes under swapping two adjacent events of distinct actions when both orders
    are valid runs (the same final configuration is then automatic)."""
    runs = {}
    stack = [((), (s, 0), 0)]
    while stack:
        w, c, begun = stack.pop()
        if c[1] == 0 and w:
            X = frozenset(a for a in range(S.NA) if (begun >> a) & 1)
            runs[w] = (X, c[0])
        for a in range(S.NA):
            if not (begun >> a) & 1 and not (c[1] >> a) & 1:
                c2 = S.fire(c, ('B', a))
                if c2 is not None:
                    stack.append((w + (('B', a),), c2, begun | (1 << a)))
            if (c[1] >> a) & 1:
                c2 = S.fire(c, ('E', a))
                if c2 is not None:
                    stack.append((w + (('E', a),), c2, begun))
    H = collections.defaultdict(set)
    if GROUPING == 'final':
        for w, key in runs.items():
            H[key].add(w)
        return H
    # union-find over runs
    parent = {w: w for w in runs}
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for w in runs:
        for i in range(len(w) - 1):
            if w[i][1] != w[i + 1][1]:
                w2 = w[:i] + (w[i + 1], w[i]) + w[i + 2:]
                if w2 in runs and runs[w2] == runs[w]:
                    ra, rb = find(w), find(w2)
                    if ra != rb: parent[ra] = rb
    for w, key in runs.items():
        H[(key[0], key[1], find(w))].add(w)
    return H


def analyse_history(S, X, runs):
    X = tuple(sorted(X))
    IO = set(io_of(w, X) for w in runs)
    prec = frozenset.intersection(*IO)
    # weak_H: (a,b) such that b<a in no run
    weak = frozenset((a, b) for a in X for b in X if a != b and all((b, a) not in o for o in IO))
    words = all_words(X)
    allIO = {}
    for w in words:
        allIO.setdefault(io_of(w, X), []).append(w)
    ext = set(o for o in allIO if prec <= o and all((b, a) not in o for (a, b) in weak))
    REP = (ext == IO)
    IOC = all(all(w in runs for w in allIO[o]) for o in IO)
    return REP, IOC, len(IO), len(ext)


def props4(S):
    REP = IOC = True
    nh = 0
    bad = []
    for s in range(NS):
        H = histories(S, s)
        for key, runs in H.items():
            X, s2 = key[0], key[1]
            if len(X) < 2:
                continue
            nh += 1
            rep, ioc, nio, next_ = analyse_history(S, X, runs)
            if not rep:
                REP = False
                if len(bad) < 3: bad.append((s, X, s2, nio, next_, sorted(runs)[:4]))
            if not ioc:
                IOC = False
    return {'REP': REP, 'IOC': IOC, 'nhist': nh, 'bad': bad}


if __name__ == '__main__':
    NA = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    disc = sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] != 'any' else None
    reading = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != 'any' else None
    rng = random.Random(seed)
    rows, systems = [], []
    for i in range(N):
        S = rand_system(rng, NA=NA, disc=disc, reading=reading)
        r = props4(S)
        # transparency of start and swap closure from (s,{})
        st, acq = S.start, S.acq
        pairs = [(a, b) for a in range(NA) for b in range(NA) if S.indep(a, b)]
        r['T1'] = all(not bit(st[a], t) or (bit(st[b], t) == bit(st[b], acq[a][t])) for a, b in pairs for t in range(NS))
        JR = True
        for s in range(NS):
            valid = set(w for w, _ in all_runs(S, s))
            for w in valid:
                if len(w) >= 2 and w[-1][0] == w[-2][0] and w[-1][1] != w[-2][1] and (w[:-2] + (w[-1], w[-2])) not in valid:
                    JR = False
        r['JR'] = JR
        rows.append(r); systems.append(S)
    def cnt(f): return sum(1 for r in rows if f(r))
    print("systems:", N, " NA=", NA, " disc=", disc, " reading=", reading)
    print("  REP:", cnt(lambda r: r['REP']), " IOC:", cnt(lambda r: r['IOC']), " JR:", cnt(lambda r: r['JR']), " T1:", cnt(lambda r: r['T1']),
          " systems with >=1 history of size>=2:", cnt(lambda r: r['nhist'] > 0))
    print("  T1 -> REP viol:", cnt(lambda r: r['T1'] and not r['REP']), " JR -> REP viol:", cnt(lambda r: r['JR'] and not r['REP']),
          " REP -> JR viol:", cnt(lambda r: r['REP'] and not r['JR']), " IOC -> REP viol:", cnt(lambda r: r['IOC'] and not r['REP']),
          " REP -> IOC viol:", cnt(lambda r: r['REP'] and not r['IOC']), " JR -> IOC viol:", cnt(lambda r: r['JR'] and not r['IOC']))
    with open(os.path.join(OUT, 'resC_%d_%s_%s.pkl' % (NA, disc, reading)), 'wb') as f:
        pickle.dump([(S.__dict__, r) for S, r in zip(systems, rows)], f)
