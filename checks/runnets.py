"""Reading x discipline table on net-like systems: soundness, consistency, reachability, structures."""
import sys, random, itertools, pickle
import os
OUT = os.environ.get('CHECK_OUT', os.path.dirname(os.path.abspath(__file__)))  # where result pickles are written
from gas import *
from nets import rand_net
from checkA2 import coherent_configs, events_at, run_from
from checkC import histories, analyse_history, all_words, io_of
import checkC


def netprops(S):
    NA = S.NA
    P = {}
    cfgs = coherent_configs(S)
    GI = {'BB': True, 'BE': True, 'EB': True, 'EE': True}
    J = {'BB': True, 'EE': True}
    HSC = cJS = True
    for c in cfgs:
        ev = events_at(S, c)
        en = dict(ev)
        for (e, ee) in ev:
            if not ee: continue
            c1 = S.fire(c, e)
            for (f, fe) in ev:
                if f == e or f[1] == e[1] or not S.indep(e[1], f[1]): continue
                fe1 = S.fire(c1, f) is not None
                key = e[0] + f[0]
                if fe != fe1: GI[key] = False
                if key in ('BB', 'EE') and fe1:
                    cf = S.fire(c, f)
                    if cf is None or S.fire(cf, e) is None: J[key] = False
        Bs = [e for e, _ in ev if e[0] == 'B']; Es = [e for e, _ in ev if e[0] == 'E']
        for group in (Bs, Es):
            for k in range(2, len(group) + 1):
                for X in itertools.combinations(group, k):
                    if not S.pairwise_indep([e[1] for e in X]): continue
                    fires = all(en[e] for e in X)
                    res = [S.run_from(c, list(w)) for w in itertools.permutations(X)]
                    allok = all(r is not None for r in res); anyok = any(r is not None for r in res)
                    if fires != allok or (not fires and anyok) or (allok and len(set(res)) != 1): HSC = False
        stack = [((), c, 0)]; valid = set()
        while stack:
            w, cc, begun = stack.pop()
            valid.add(w)
            for a in range(NA):
                if not (begun >> a) & 1 and not (cc[1] >> a) & 1:
                    c2 = S.fire(cc, ('B', a))
                    if c2 is not None: stack.append((w + (('B', a),), c2, begun | (1 << a)))
                if (cc[1] >> a) & 1:
                    c2 = S.fire(cc, ('E', a))
                    if c2 is not None: stack.append((w + (('E', a),), c2, begun))
        for w in valid:
            if len(w) >= 2 and w[-1][0] == w[-2][0] and w[-1][1] != w[-2][1] and (w[:-2] + (w[-1], w[-2])) not in valid:
                cJS = False
    P.update({'GI_' + k: v for k, v in GI.items()}); P.update({'J_' + k: v for k, v in J.items()})
    P.update(HSC=HSC, cJS=cJS)
    # reachability
    EqR = True
    for s in range(NS):
        seen = {(s, 0)}; stack = [(s, 0)]
        while stack:
            cc = stack.pop()
            for a in range(NA):
                for e in (('B', a), ('E', a)):
                    c2 = S.fire(cc, e)
                    if c2 is not None and c2 not in seen: seen.add(c2); stack.append(c2)
        intR = {cc[0] for cc in seen if cc[1] == 0}
        seq = {s}; st = [s]
        while st:
            u = st.pop()
            for a in range(NA):
                r = S.run(u, [('B', a), ('E', a)])
                if r is not None and r[0] not in seq: seq.add(r[0]); st.append(r[0])
        if intR != seq: EqR = False; break
    P['EqR'] = EqR
    # structures
    REP = IOC = True; nh = 0; bad = []
    for s in range(NS):
        H = histories(S, s)
        for key, runs in H.items():
            X = key[0]
            if len(X) < 2: continue
            nh += 1
            rep, ioc, nio, next_ = analyse_history(S, X, runs)
            if not rep:
                REP = False
                if len(bad) < 2: bad.append((s, X, key[1], sorted(runs)[:3]))
            if not ioc: IOC = False
    P.update(REP=REP, IOC=IOC, nhist=nh, bad=bad)
    return P


if __name__ == '__main__':
    NA = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    discs = sys.argv[4].split(',') if len(sys.argv) > 4 else ['committed', 'consuming', 'startonly']
    readings = sys.argv[5].split(',') if len(sys.argv) > 5 else ['atstart', 'overall', 'closed']
    keys = ['GI_BB', 'GI_BE', 'GI_EB', 'GI_EE', 'J_BB', 'J_EE', 'HSC', 'cJS', 'EqR', 'REP', 'IOC']
    print("%-22s" % "disc/reading" + "".join("%7s" % k for k in keys))
    allres = {}
    for d in discs:
        for r in readings:
            rng = random.Random(seed)
            rows = []; systems = []
            for i in range(N):
                S = rand_net(rng, NA=NA, disc=d, reading=r)
                rows.append(netprops(S)); systems.append(S)
            print("%-22s" % (d + "/" + r) + "".join("%7d" % sum(1 for x in rows if x[k]) for k in keys), flush=True)
            allres[(d, r)] = [(S.__dict__, x) for S, x in zip(systems, rows)]
    with open(os.path.join(OUT, 'resNets_%d.pkl' % NA), 'wb') as f:
        pickle.dump(allres, f)
