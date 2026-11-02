"""Claim A: over-all soundness on step-shaped runs.

Global properties (semantic, computed by running every block word from every state):
  OS1  : for every s and pairwise independent U with start_a(s) for all a in U,
         every word of U^BE is a valid run from s.
  OS2  : same, with en2_a(s) (the singleton block B_a E_a is valid from s) in place of start_a.
  OC2  : OS2 and, when some a in U has not en2_a(s), no word of U^BE is valid from s.
  POS2, POC2 : OS2, OC2 restricted to |U| <= 2.
Local conditions (quantified over ALL states t, independent a, b):
  Self : start_a(t) -> over_a(acq_a t) and end_a(acq_a t)          (en1 = en2)
  T1   : start_a(t) -> (start_b(t) <-> start_b(acq_a t))           (Part A transparency)
  T2   : en2_a(t)   -> (en2_b(t)   <-> en2_b(acq_a t))
  Sacq : start_a(t) and start_b(t) -> start_b(acq_a t)             (forward half of T1)
  Oacq : over_a(t) and start_b(t) -> over_a(acq_b t)
  Orel : over_a(t) -> over_a(rel_b t)
  Eacq : end_a(t) and start_b(t) -> end_a(acq_b t)
  Erel : end_a(t) -> end_a(rel_b t)
  NGs  : every action has no temporal gap, syntactic form:
         (acq_a = id and over_a -> start_a) or (rel_a = id and over_a -> end_a)
  NGw  : weak form: (acq_a = id and over_a and end_a -> start_a) or
         (rel_a = id and start_a(t) and over_a(acq_a t) -> end_a(acq_a t))
"""
import sys, random, itertools, collections
import os
OUT = os.environ.get('CHECK_OUT', os.path.dirname(os.path.abspath(__file__)))  # where result pickles are written
from gas import *


def props(S):
    NA = S.NA
    P = {}
    # ---- global
    OS1 = OS2 = OC2 = POS2 = POC2 = True
    for k in range(1, NA + 1):
        for U in itertools.combinations(range(NA), k):
            if not S.pairwise_indep(U):
                continue
            words = S.block_words(U)
            for s in range(NS):
                e1 = all(bit(S.start[a], s) for a in U)
                e2 = all(bit(S.en2[a], s) for a in U)
                if not (e1 or e2):
                    # neither enabledness: only the "no word valid" clause matters, and it
                    # needs e2 false, which holds; check it below
                    pass
                res = [S.run(s, w) for w in words]
                allok = all(r is not None for r in res)
                anyok = any(r is not None for r in res)
                if e1 and not allok:
                    OS1 = False
                if e2 and not allok:
                    OS2 = False
                    if k <= 2: POS2 = False
                if (e2 and not allok) or (not e2 and anyok):
                    OC2 = False
                    if k <= 2: POC2 = False
    P.update(OS1=OS1, OS2=OS2, OC2=OC2, POS2=POS2, POC2=POC2)
    # ---- local
    st, ov, en, acq, rel, en2 = S.start, S.over, S.end, S.acq, S.rel, S.en2
    Self = all(not bit(st[a], t) or (bit(ov[a], acq[a][t]) and bit(en[a], acq[a][t]))
               for a in range(NA) for t in range(NS))
    pairs = [(a, b) for a in range(NA) for b in range(NA) if S.indep(a, b)]
    T1 = all(not bit(st[a], t) or (bit(st[b], t) == bit(st[b], acq[a][t])) for a, b in pairs for t in range(NS))
    T2 = all(not bit(en2[a], t) or (bit(en2[b], t) == bit(en2[b], acq[a][t])) for a, b in pairs for t in range(NS))
    Sacq = all(not (bit(st[a], t) and bit(st[b], t)) or bit(st[b], acq[a][t]) for a, b in pairs for t in range(NS))
    Oacq = all(not (bit(ov[a], t) and bit(st[b], t)) or bit(ov[a], acq[b][t]) for a, b in pairs for t in range(NS))
    Orel = all(not bit(ov[a], t) or bit(ov[a], rel[b][t]) for a, b in pairs for t in range(NS))
    Eacq = all(not (bit(en[a], t) and bit(st[b], t)) or bit(en[a], acq[b][t]) for a, b in pairs for t in range(NS))
    Erel = all(not bit(en[a], t) or bit(en[a], rel[b][t]) for a, b in pairs for t in range(NS))
    def ng(a, weak):
        acq_id = all(acq[a][t] == t for t in range(NS))
        rel_id = all(rel[a][t] == t for t in range(NS))
        if weak:
            c1 = acq_id and all(not (bit(ov[a], t) and bit(en[a], t)) or bit(st[a], t) for t in range(NS))
            c2 = rel_id and all(not (bit(st[a], t) and bit(ov[a], acq[a][t])) or bit(en[a], acq[a][t]) for t in range(NS))
        else:
            c1 = acq_id and all(not bit(ov[a], t) or bit(st[a], t) for t in range(NS))
            c2 = rel_id and all(not bit(ov[a], t) or bit(en[a], t) for t in range(NS))
        return c1 or c2
    NGs = all(ng(a, False) for a in range(NA))
    NGw = all(ng(a, True) for a in range(NA))
    P.update(Self=Self, T1=T1, T2=T2, Sacq=Sacq, Oacq=Oacq, Orel=Orel, Eacq=Eacq, Erel=Erel, NGs=NGs, NGw=NGw)
    return P


def analyse(rows, names):
    n = len(rows)
    print("systems:", n)
    for nm in names:
        print("  %-5s true in %d" % (nm, sum(r[nm] for r in rows)))
    # implications between single properties
    print("implications X -> Y that hold on all systems (and are not trivial):")
    for x in names:
        for y in names:
            if x == y: continue
            if all((not r[x]) or r[y] for r in rows):
                # count informative cases
                k = sum(1 for r in rows if r[x])
                print("   %s -> %s   (%d witnesses of X)" % (x, y, k))
    return


if __name__ == '__main__':
    NA = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    disc = sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] != 'any' else None
    reading = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != 'any' else None
    rng = random.Random(seed)
    rows = []
    systems = []
    for i in range(N):
        S = rand_system(rng, NA=NA, disc=disc, reading=reading)
        P = props(S)
        rows.append(P); systems.append(S)
    names = ['OS1', 'OS2', 'OC2', 'POS2', 'POC2', 'Self', 'T1', 'T2', 'Sacq', 'Oacq', 'Orel', 'Eacq', 'Erel', 'NGs', 'NGw']
    analyse(rows, names)
    # conjunctions of interest
    def cnt(f):
        return sum(1 for r in rows if f(r))
    Strong = lambda r: r['Sacq'] and r['Self'] and r['Oacq'] and r['Orel'] and r['Eacq'] and r['Erel']
    print("Strong(all six local clauses) -> OS2 violations:", cnt(lambda r: Strong(r) and not r['OS2']), " Strong true:", cnt(Strong))
    print("Strong -> OS1 violations:", cnt(lambda r: Strong(r) and not r['OS1']))
    print("OS2 & not Strong:", cnt(lambda r: r['OS2'] and not Strong(r)))
    print("POS2 -> OS2 violations:", cnt(lambda r: r['POS2'] and not r['OS2']), " POS2 true:", cnt(lambda r: r['POS2']))
    print("POC2 -> OC2 violations:", cnt(lambda r: r['POC2'] and not r['OC2']), " POC2 true:", cnt(lambda r: r['POC2']))
    print("POS2 & NGs -> OS2 violations:", cnt(lambda r: r['POS2'] and r['NGs'] and not r['OS2']), " POS2&NGs true:", cnt(lambda r: r['POS2'] and r['NGs']))
    print("POS2 & NGw -> OS2 violations:", cnt(lambda r: r['POS2'] and r['NGw'] and not r['OS2']), " POS2&NGw true:", cnt(lambda r: r['POS2'] and r['NGw']))
    print("T2 & POS2 -> OS2 violations:", cnt(lambda r: r['T2'] and r['POS2'] and not r['OS2']))
    print("T2 & POC2 -> OC2 violations:", cnt(lambda r: r['T2'] and r['POC2'] and not r['OC2']))
    print("OC2 -> T2 violations:", cnt(lambda r: r['OC2'] and not r['T2']))
    print("OS2 -> T2 violations:", cnt(lambda r: r['OS2'] and not r['T2']))
    # save witnesses for POS2 & not OS2
    import pickle
    wit = [(S, r) for S, r in zip(systems, rows) if r['POS2'] and not r['OS2']]
    print("witnesses POS2 & not OS2:", len(wit))
    with open(os.path.join(OUT, 'witA_%d_%s_%s.pkl' % (NA, disc, reading)), 'wb') as f:
        pickle.dump([(S.__dict__, r) for S, r in wit[:20]], f)
