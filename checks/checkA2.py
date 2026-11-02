"""Claim A, configuration-level version.

A configuration is (t, F) with F a set of pairwise independent actions in flight;
it is coherent if over_a(t) holds for every a in F.  Every coherent configuration
is a legitimate start (as every marking of the double-arc or split net is).

Event enabledness at a coherent (t,F) (blocking semantics):
  B_b: b not in F, b independent of F, start_b(t), over_b(acq_b t), over_d(acq_b t) for d in F
  E_b: b in F, end_b(t), over_d(rel_b t) for d in F - {b}

Global properties:
  GI   : event independence is valid (Godefroid): for coherent c, independent a != b,
         e in {B_a,E_a} enabled at c with c -e-> c', f in {B_b,E_b}:
         f enabled at c  <->  f enabled at c'.   (commutation of results is structural; checked too)
  GI1  : GI restricted to |F| <= 1;  GI2: |F| <= 2
  ESC  : event-step conservativity: for coherent c and every event step X (pairwise
         independent underlying actions, one event per action, B for actions not in F,
         E for actions in F): X fires a priori at c (every event enabled at c)
         <-> every linearisation of X is a valid run from c.
  cOC  : block conservativity from coherent configurations (U^BE words only).
  sOC  : the same from (s, {}) only  (= OC2 of checkA.py).
  JR   : swap closure of the valid-run set from (s,{}) (Janicki-soundness), each action at most once.
Local clauses (all t, independent a != b), forward (f) and backward (b):
  Oacq_f: over_a(t) & en0_b(t) -> over_a(acq_b t)        en0_b(t) := start_b(t) & over_b(acq_b t)
  Oacq_b: en0_b(t) & over_a(acq_b t) -> over_a(t)
  Orel_f: over_a(t) & over_b(t) & end_b(t) -> over_a(rel_b t)
  Orel_b: over_b(t) & end_b(t) & over_a(rel_b t) -> over_a(t)
  Eacq_f/b, Erel_f/b : the same for end_a in place of over_a, with over_a(t) added as hypothesis
  Sacq_f: en0_a(t) & en0_b(t) -> start_b(acq_a t);  Sacq_b: en0_a(t) & en0_b(acq_a t) -> en0_b(t) [as T2-like]
  T0   : en0_a(t) -> (en0_b(t) <-> en0_b(acq_a t))
"""
import sys, random, itertools, collections, pickle
import os
OUT = os.environ.get('CHECK_OUT', os.path.dirname(os.path.abspath(__file__)))  # where result pickles are written
from gas import *


def coherent_configs(S):
    out = []
    subsets = []
    for k in range(S.NA + 1):
        for F in itertools.combinations(range(S.NA), k):
            if S.pairwise_indep(F):
                subsets.append(sum(1 << a for a in F))
    for t in range(NS):
        for Fm in subsets:
            if all(bit(S.over[a], t) for a in range(S.NA) if (Fm >> a) & 1):
                out.append((t, Fm))
    return out


def events_at(S, c):
    """Candidate events at c (underlying action admissible), with enabledness."""
    t, F = c
    ev = []
    for a in range(S.NA):
        if (F >> a) & 1:
            ev.append((('E', a), S.fire(c, ('E', a)) is not None))
        else:
            if all(not (F >> d) & 1 or S.indep(a, d) for d in range(S.NA)):
                ev.append((('B', a), S.fire(c, ('B', a)) is not None))
    return ev


def props2(S):
    NA = S.NA
    P = {}
    cfgs = coherent_configs(S)
    GI = GI1 = GI2 = True
    ESC = True
    cOC = True
    for c in cfgs:
        t, F = c
        popF = bin(F).count('1')
        ev = events_at(S, c)
        # --- GI
        for (e, ee) in ev:
            if not ee:
                continue
            c1 = S.fire(c, e)
            for (f, fe) in ev:
                if f == e or f[1] == e[1] or not S.indep(e[1], f[1]):
                    continue
                fe1 = S.fire(c1, f) is not None
                if fe != fe1:
                    GI = False
                    if popF <= 1: GI1 = False
                    if popF <= 2: GI2 = False
                if fe and fe1:
                    # commutation of results, when both orders are runnable
                    c2 = S.fire(c1, f)
                    cf = S.fire(c, f)
                    c3 = S.fire(cf, e) if cf is not None else None
                    assert c3 is None or c2 == c3, "commutation failed"
        # --- ESC: event steps
        admissible = [e for (e, _) in ev]
        en = dict(ev)
        acts = sorted(set(e[1] for e in admissible))
        # choose for each action: nothing or its unique admissible event
        byact = {a: [e for e in admissible if e[1] == a] for a in acts}
        for k in range(1, len(acts) + 1):
            for A in itertools.combinations(acts, k):
                if not S.pairwise_indep(A):
                    continue
                X = [byact[a][0] for a in A]
                fires = all(en[e] for e in X)
                lins = list(itertools.permutations(X))
                res = [S.run_from(c, list(w)) for w in lins]
                allok = all(r is not None for r in res)
                anyok = any(r is not None for r in res)
                if fires != allok or (not fires and anyok):
                    ESC = False
                if fires and allok and len(set(res)) != 1:
                    ESC = False
        # --- cOC: blocks U^BE from c
        free = [a for a in range(NA) if not (F >> a) & 1 and all(not (F >> d) & 1 or S.indep(a, d) for d in range(NA))]
        for k in range(1, len(free) + 1):
            for U in itertools.combinations(free, k):
                if not S.pairwise_indep(U):
                    continue
                enU = all(S.run_from(c, [('B', b), ('E', b)]) is not None for b in U)
                res = [S.run_from(c, w) for w in S.block_words(U)]
                allok = all(r is not None for r in res)
                anyok = any(r is not None for r in res)
                if enU != allok or (not enU and anyok):
                    cOC = False
    P.update(GI=GI, GI1=GI1, GI2=GI2, ESC=ESC, cOC=cOC)
    # --- sOC and JR from (s, {})
    sOC = True
    for k in range(1, NA + 1):
        for U in itertools.combinations(range(NA), k):
            if not S.pairwise_indep(U):
                continue
            words = S.block_words(U)
            for s in range(NS):
                e2 = all(bit(S.en2[a], s) for a in U)
                res = [S.run(s, w) for w in words]
                allok = all(r is not None for r in res)
                anyok = any(r is not None for r in res)
                if e2 != allok or (not e2 and anyok):
                    sOC = False
    JR = True
    for s in range(NS):
        runs = all_runs(S, s)
        valid = set(w for w, _ in runs)
        for w in valid:
            if len(w) >= 2 and w[-1][0] == w[-2][0] and w[-1][1] != w[-2][1]:
                sw = w[:-2] + (w[-1], w[-2])
                if sw not in valid:
                    JR = False
    P.update(sOC=sOC, JR=JR)
    # --- local clauses
    st, ov, en_, acq, rel = S.start, S.over, S.end, S.acq, S.rel
    en0 = [0] * NA
    for a in range(NA):
        m = 0
        for t in range(NS):
            if bit(st[a], t) and bit(ov[a], acq[a][t]):
                m |= 1 << t
        en0[a] = m
    pairs = [(a, b) for a in range(NA) for b in range(NA) if S.indep(a, b)]
    R = range(NS)
    def allt(f):
        return all(f(a, b, t) for a, b in pairs for t in R)
    P['Oacq_f'] = allt(lambda a, b, t: not (bit(ov[a], t) and bit(en0[b], t)) or bit(ov[a], acq[b][t]))
    P['Oacq_b'] = allt(lambda a, b, t: not (bit(en0[b], t) and bit(ov[a], acq[b][t])) or bit(ov[a], t))
    P['Orel_f'] = allt(lambda a, b, t: not (bit(ov[a], t) and bit(ov[b], t) and bit(en_[b], t)) or bit(ov[a], rel[b][t]))
    P['Orel_b'] = allt(lambda a, b, t: not (bit(ov[b], t) and bit(en_[b], t) and bit(ov[a], rel[b][t])) or bit(ov[a], t))
    P['Eacq_f'] = allt(lambda a, b, t: not (bit(ov[a], t) and bit(en_[a], t) and bit(en0[b], t)) or bit(en_[a], acq[b][t]))
    P['Eacq_b'] = allt(lambda a, b, t: not (bit(ov[a], t) and bit(en0[b], t) and bit(en_[a], acq[b][t])) or bit(en_[a], t))
    P['Erel_f'] = allt(lambda a, b, t: not (bit(ov[a], t) and bit(en_[a], t) and bit(ov[b], t) and bit(en_[b], t)) or bit(en_[a], rel[b][t]))
    P['Erel_b'] = allt(lambda a, b, t: not (bit(ov[a], t) and bit(ov[b], t) and bit(en_[b], t) and bit(en_[a], rel[b][t])) or bit(en_[a], t))
    P['Sacq_f'] = allt(lambda a, b, t: not (bit(en0[a], t) and bit(en0[b], t)) or bit(st[b], acq[a][t]))
    P['T0'] = allt(lambda a, b, t: not bit(en0[a], t) or (bit(en0[b], t) == bit(en0[b], acq[a][t])))
    P['T2'] = allt(lambda a, b, t: not bit(S.en2[a], t) or (bit(S.en2[b], t) == bit(S.en2[b], acq[a][t])))
    return P


def run_from(self, c, word):
    for e in word:
        c = self.fire(c, e)
        if c is None:
            return None
    return c
Sys.run_from = run_from


if __name__ == '__main__':
    NA = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    disc = sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] != 'any' else None
    reading = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != 'any' else None
    rng = random.Random(seed)
    rows, systems = [], []
    for i in range(N):
        S = rand_system(rng, NA=NA, disc=disc, reading=reading)
        rows.append(props2(S)); systems.append(S)
    names = list(rows[0].keys())
    print("systems:", N, " NA=", NA, " disc=", disc, " reading=", reading)
    for nm in names:
        print("  %-7s true in %d" % (nm, sum(r[nm] for r in rows)))
    print("implications X -> Y holding on all systems:")
    for x in names:
        for y in names:
            if x != y and all((not r[x]) or r[y] for r in rows):
                print("   %s -> %s   (%d)" % (x, y, sum(1 for r in rows if r[x])))
    loc_f = ['Oacq_f', 'Orel_f', 'Eacq_f', 'Erel_f', 'Sacq_f']
    loc_all = loc_f + ['Oacq_b', 'Orel_b', 'Eacq_b', 'Erel_b', 'T0']
    def cnt(f): return sum(1 for r in rows if f(r))
    LF = lambda r: all(r[k] for k in loc_f)
    LA = lambda r: all(r[k] for k in loc_all)
    print("GI <-> ESC mismatches:", cnt(lambda r: r['GI'] != r['ESC']))
    print("GI <-> GI1 mismatches:", cnt(lambda r: r['GI'] != r['GI1']), " GI <-> GI2:", cnt(lambda r: r['GI'] != r['GI2']))
    print("GI <-> all local clauses mismatches:", cnt(lambda r: r['GI'] != LA(r)), " (LA true:", cnt(LA), ")")
    print("   GI & not LA:", cnt(lambda r: r['GI'] and not LA(r)), "  LA & not GI:", cnt(lambda r: LA(r) and not r['GI']))
    print("GI -> cOC viol:", cnt(lambda r: r['GI'] and not r['cOC']), " cOC -> GI viol:", cnt(lambda r: r['cOC'] and not r['GI']))
    print("GI -> JR viol:", cnt(lambda r: r['GI'] and not r['JR']), " JR -> GI viol:", cnt(lambda r: r['JR'] and not r['GI']))
    print("cOC -> sOC viol:", cnt(lambda r: r['cOC'] and not r['sOC']), " sOC -> cOC viol:", cnt(lambda r: r['sOC'] and not r['cOC']))
    print("cOC <-> T2&LF? mism:", cnt(lambda r: r['cOC'] != (r['T2'] and LF(r))))
    print("cOC & not T2:", cnt(lambda r: r['cOC'] and not r['T2']))
    for k in loc_all:
        print("  GI & not %s: %d ;  (all other clauses) & not %s & not GI: %d" % (k, cnt(lambda r: r['GI'] and not r[k]), k,
              cnt(lambda r: all(r[j] for j in loc_all if j != k) and not r[k] and not r['GI'])))
    wit = [(S.__dict__, r) for S, r in zip(systems, rows) if r['GI'] != LA(r)]
    with open(os.path.join(OUT, 'witA2_%d_%s_%s.pkl' % (NA, disc, reading)), 'wb') as f:
        pickle.dump(wit[:20], f)
