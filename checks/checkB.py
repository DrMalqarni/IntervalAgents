"""Part B properties at the configuration level (all coherent configurations are starts).

Event transparency, split by event kinds (e then f, independent actions, e enabled at c):
  GI_BB: f = B_b after e = B_a      GI_BE: f = E_b after e = B_a
  GI_EB: f = B_b after e = E_a      GI_EE: f = E_b after e = E_a
  each: f enabled at c <-> f enabled after e.
Swap conditions (Janicki-soundness, two events): J_BB: B_a B_b valid -> B_b B_a valid; J_EE likewise.
Global:
  HSC : homogeneous step conservativity: for every coherent c, every B-step U (pairwise independent,
        disjoint from and independent of F): all B_b enabled at c <-> all orders valid (and none valid
        otherwise); every E-step D within F likewise.
  cJS : swap closure (adjacent BB or EE, distinct actions) of the set of valid runs from every coherent
        configuration, each action beginning at most once per run.
  cOC : atomic-rule block conservativity (singleton block B_b E_b valid for all b in U <-> all words of
        U^BE valid, none otherwise).
  cOC2: two-phase-rule block conservativity (all B_b enabled at c and all E_b enabled at (acq_U t, F+U)
        <-> all words of U^BE valid, none otherwise).
  EqR : interval reachability equals sequential reachability from every state (claim B1).
  NGs, NGw: no temporal gap (syntactic / weak), as in checkA.py.
"""
import sys, random, itertools, pickle
import os
OUT = os.environ.get('CHECK_OUT', os.path.dirname(os.path.abspath(__file__)))  # where result pickles are written
from gas import *
from checkA2 import coherent_configs, events_at, run_from


def props3(S):
    NA = S.NA
    P = {}
    cfgs = coherent_configs(S)
    GI = {'BB': True, 'BE': True, 'EB': True, 'EE': True}
    J = {'BB': True, 'EE': True}
    HSC = cOC = cOC2 = cJS = True
    for c in cfgs:
        t, F = c
        ev = events_at(S, c)
        en = dict(ev)
        # --- GI and J, two events
        for (e, ee) in ev:
            if not ee:
                continue
            c1 = S.fire(c, e)
            for (f, fe) in ev:
                if f == e or f[1] == e[1] or not S.indep(e[1], f[1]):
                    continue
                fe1 = S.fire(c1, f) is not None
                key = e[0] + f[0]
                if fe != fe1:
                    GI[key] = False
                if key in ('BB', 'EE') and fe1:
                    # e f valid; need f e valid
                    cf = S.fire(c, f)
                    if cf is None or S.fire(cf, e) is None:
                        J[key] = False
        # --- HSC
        Bs = [e for e, _ in ev if e[0] == 'B']
        Es = [e for e, _ in ev if e[0] == 'E']
        for group in (Bs, Es):
            for k in range(2, len(group) + 1):
                for X in itertools.combinations(group, k):
                    if not S.pairwise_indep([e[1] for e in X]):
                        continue
                    fires = all(en[e] for e in X)
                    res = [S.run_from(c, list(w)) for w in itertools.permutations(X)]
                    allok = all(r is not None for r in res)
                    anyok = any(r is not None for r in res)
                    if fires != allok or (not fires and anyok) or (allok and len(set(res)) != 1):
                        HSC = False
        # --- cOC, cOC2
        free = [a for a in range(NA) if not (F >> a) & 1 and all(not (F >> d) & 1 or S.indep(a, d) for d in range(NA))]
        for k in range(1, len(free) + 1):
            for U in itertools.combinations(free, k):
                if not S.pairwise_indep(U):
                    continue
                res = [S.run_from(c, w) for w in S.block_words(U)]
                allok = all(r is not None for r in res)
                anyok = any(r is not None for r in res)
                enU = all(S.run_from(c, [('B', b), ('E', b)]) is not None for b in U)
                if enU != allok or (not enU and anyok):
                    cOC = False
                # two-phase
                tU = t
                for b in U: tU = S.acq[b][tU]
                FU = F | sum(1 << b for b in U)
                fires2 = all(en[('B', b)] for b in U) and all(S.fire((tU, FU), ('E', b)) is not None for b in U)
                if fires2 != allok or (not fires2 and anyok):
                    cOC2 = False
        # --- cJS: swap closure of valid runs from c (each action begins at most once)
        stack = [((), c, 0)]
        valid = set()
        while stack:
            w, cc, begun = stack.pop()
            valid.add(w)
            for a in range(NA):
                if not (begun >> a) & 1 and not (cc[1] >> a) & 1:
                    c2 = S.fire(cc, ('B', a))
                    if c2 is not None:
                        stack.append((w + (('B', a),), c2, begun | (1 << a)))
                if (cc[1] >> a) & 1:
                    c2 = S.fire(cc, ('E', a))
                    if c2 is not None:
                        stack.append((w + (('E', a),), c2, begun))
        for w in valid:
            if len(w) >= 2 and w[-1][0] == w[-2][0] and w[-1][1] != w[-2][1]:
                if w[:-2] + (w[-1], w[-2]) not in valid:
                    cJS = False
    P.update({'GI_' + k: v for k, v in GI.items()})
    P.update({'J_' + k: v for k, v in J.items()})
    P.update(HSC=HSC, cOC=cOC, cOC2=cOC2, cJS=cJS)
    # --- reachability (claim B)
    EqR = True
    for s in range(NS):
        # interval reachability: BFS over configurations from (s,0), complete runs
        seen = {(s, 0)}
        stack = [(s, 0)]
        while stack:
            cc = stack.pop()
            for a in range(NA):
                for e in (('B', a), ('E', a)):
                    c2 = S.fire(cc, e)
                    if c2 is not None and c2 not in seen:
                        seen.add(c2); stack.append(c2)
        intR = {cc[0] for cc in seen if cc[1] == 0}
        # sequential reachability
        seq = {s}; st = [s]
        while st:
            u = st.pop()
            for a in range(NA):
                r = S.run(u, [('B', a), ('E', a)])
                if r is not None and r[0] not in seq:
                    seq.add(r[0]); st.append(r[0])
        if intR != seq:
            EqR = False
            break
    P['EqR'] = EqR
    acq, rel, st_, ov, en_ = S.acq, S.rel, S.start, S.over, S.end
    def ng(a, weak):
        acq_id = all(acq[a][t] == t for t in range(NS))
        rel_id = all(rel[a][t] == t for t in range(NS))
        if weak:
            c1 = acq_id and all(not (bit(ov[a], t) and bit(en_[a], t)) or bit(st_[a], t) for t in range(NS))
            c2 = rel_id and all(not (bit(st_[a], t) and bit(ov[a], acq[a][t])) or bit(en_[a], acq[a][t]) for t in range(NS))
        else:
            c1 = acq_id and all(not bit(ov[a], t) or bit(st_[a], t) for t in range(NS))
            c2 = rel_id and all(not bit(ov[a], t) or bit(en_[a], t) for t in range(NS))
        return c1 or c2
    P['NGs'] = all(ng(a, False) for a in range(NA))
    P['NGw'] = all(ng(a, True) for a in range(NA))
    return P


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
        rows.append(props3(S)); systems.append(S)
    names = list(rows[0].keys())
    print("systems:", N, " NA=", NA, " disc=", disc, " reading=", reading)
    for nm in names:
        print("  %-7s true in %d" % (nm, sum(r[nm] for r in rows)))
    def cnt(f): return sum(1 for r in rows if f(r))
    print("implications X -> Y holding on all systems:")
    for x in names:
        for y in names:
            if x != y and all((not r[x]) or r[y] for r in rows):
                print("   %s -> %s   (%d)" % (x, y, cnt(lambda r: r[x])))
    print("HSC <-> GI_BB&GI_EE mismatches:", cnt(lambda r: r['HSC'] != (r['GI_BB'] and r['GI_EE'])))
    print("cJS <-> J_BB&J_EE mismatches:", cnt(lambda r: r['cJS'] != (r['J_BB'] and r['J_EE'])))
    print("cOC2 <-> HSC mismatches:", cnt(lambda r: r['cOC2'] != r['HSC']), "  cOC2 <-> GI_BB&GI_EE:", cnt(lambda r: r['cOC2'] != (r['GI_BB'] and r['GI_EE'])))
    print("cOC <-> HSC&GI_BE mismatches:", cnt(lambda r: r['cOC'] != (r['HSC'] and r['GI_BE'])), "  cOC&notGI_BE:", cnt(lambda r: r['cOC'] and not r['GI_BE']), "  HSC&GI_BE&notcOC:", cnt(lambda r: r['HSC'] and r['GI_BE'] and not r['cOC']))
    print("cOC -> HSC viol:", cnt(lambda r: r['cOC'] and not r['HSC']), " cOC -> GI_BB viol:", cnt(lambda r: r['cOC'] and not r['GI_BB']), " cOC -> GI_EE viol:", cnt(lambda r: r['cOC'] and not r['GI_EE']))
    print("NGs -> EqR viol:", cnt(lambda r: r['NGs'] and not r['EqR']), " NGs:", cnt(lambda r: r['NGs']))
    print("NGw -> EqR viol:", cnt(lambda r: r['NGw'] and not r['EqR']), " NGw:", cnt(lambda r: r['NGw']))
    print("EqR & not NGw:", cnt(lambda r: r['EqR'] and not r['NGw']))
    with open(os.path.join(OUT, 'resB_%d_%s_%s.pkl' % (NA, disc, reading)), 'wb') as f:
        pickle.dump([(S.__dict__, r) for S, r in zip(systems, rows)], f)
