"""Print a system and the first GI violation / local-clause violation."""
import sys, pickle, itertools
from gas import *
from checkA2 import coherent_configs, events_at, props2


def fmt_pred(m, name):
    if m == ALL: return name + "=T"
    # describe as set of (relevant var values) : find dependent vars
    deps = [v for v in range(NV) if any(bit(m, s) != bit(m, s ^ (1 << v)) for s in range(NS))]
    rows = []
    for vals in itertools.product([0, 1], repeat=len(deps)):
        s = sum(val << v for v, val in zip(deps, vals))
        rows.append("".join(str(x) for x in vals) + ("+" if bit(m, s) else "-"))
    return "%s(%s)={%s}" % (name, ",".join("v%d" % v for v in deps), " ".join(rows))


def fmt_eff(f, name):
    ch = []
    for v in range(NV):
        sets = all(bit(f[s], v) for s in range(NS)); clears = all(not bit(f[s], v) for s in range(NS))
        if sets: ch.append("v%d:=1" % v)
        elif clears: ch.append("v%d:=0" % v)
        elif any(bit(f[s], v) != bit(s, v) for s in range(NS)): ch.append("v%d:=?" % v)
    return "%s[%s]" % (name, ",".join(ch) if ch else "id")


def show(S):
    for a in range(S.NA):
        print(" action %d (%s): %s %s %s %s %s" % (a, S.mode[a], fmt_pred(S.start[a], "start"), fmt_pred(S.over[a], "over"),
              fmt_pred(S.end[a], "end"), fmt_eff(S.acq[a], "acq"), fmt_eff(S.rel[a], "rel")))
    print(" conflicts:", sorted(p for p in S.conflict if p[0] < p[1]))


def first_GI_violation(S):
    for c in coherent_configs(S):
        ev = events_at(S, c)
        for (e, ee) in ev:
            if not ee: continue
            c1 = S.fire(c, e)
            for (f, fe) in ev:
                if f == e or f[1] == e[1] or not S.indep(e[1], f[1]): continue
                fe1 = S.fire(c1, f) is not None
                if fe != fe1:
                    return c, e, f, fe, fe1
    return None


def tostate(t):
    return "".join(str(bit(t, v)) for v in range(NV))


if __name__ == '__main__':
    fn = sys.argv[1]
    want = sys.argv[2] if len(sys.argv) > 2 else 'both'
    wit = pickle.load(open(fn, 'rb'))
    loc_all = ['Oacq_f', 'Orel_f', 'Eacq_f', 'Erel_f', 'Sacq_f', 'Oacq_b', 'Orel_b', 'Eacq_b', 'Erel_b', 'T0']
    for d, r in wit:
        S = Sys.__new__(Sys); S.__dict__.update(d)
        LA = all(r[k] for k in loc_all)
        kind = "GI&notLA" if r['GI'] and not LA else ("LA&notGI" if LA and not r['GI'] else "?")
        if want != 'both' and want != kind: continue
        print("=====", kind, " failing clauses:", [k for k in loc_all if not r[k]])
        show(S)
        v = first_GI_violation(S)
        if v:
            c, e, f, fe, fe1 = v
            print(" GI violation at t=%s F=%s : after %s, %s enabled %s -> %s" % (tostate(c[0]), bin(c[1]), e, f, fe, fe1))
