"""Lean version of checkB for 4 actions: ET (GI_*), J_*, HSC, cJS, EqR, NG."""
import sys, random, itertools, pickle
import os
OUT = os.environ.get('CHECK_OUT', os.path.dirname(os.path.abspath(__file__)))  # where result pickles are written
from gas import *
from checkA2 import coherent_configs, events_at, run_from
from runnets import netprops   # computes GI, J, HSC, cJS, EqR, REP, IOC

if __name__ == '__main__':
    NA = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    disc = sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] != 'any' else None
    reading = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != 'any' else None
    rng = random.Random(seed)
    rows, systems = [], []
    for i in range(N):
        S = rand_system(rng, NA=NA, disc=disc, reading=reading)
        rows.append(netprops(S)); systems.append(S)
        if (i + 1) % 10 == 0: print("done", i + 1, flush=True)
    keys = ['GI_BB', 'GI_BE', 'GI_EB', 'GI_EE', 'J_BB', 'J_EE', 'HSC', 'cJS', 'EqR', 'REP', 'IOC']
    print("systems:", N, " NA=", NA, " disc=", disc, " reading=", reading)
    print("".join("%7s" % k for k in keys))
    print("".join("%7d" % sum(1 for x in rows if x[k]) for k in keys))
    def cnt(f): return sum(1 for r in rows if f(r))
    print("HSC <-> GI_BB&GI_EE mismatches:", cnt(lambda r: r['HSC'] != (r['GI_BB'] and r['GI_EE'])))
    print("cJS <-> J_BB&J_EE mismatches:", cnt(lambda r: r['cJS'] != (r['J_BB'] and r['J_EE'])))
    print("HSC -> cJS viol:", cnt(lambda r: r['HSC'] and not r['cJS']), " cJS -> IOC viol:", cnt(lambda r: r['cJS'] and not r['IOC']), " IOC -> cJS viol:", cnt(lambda r: r['IOC'] and not r['cJS']))
    with open(os.path.join(OUT, 'resB4_%d_%s_%s.pkl' % (NA, disc, reading)), 'wb') as f:
        pickle.dump([(S.__dict__, r) for S, r in zip(systems, rows)], f)
