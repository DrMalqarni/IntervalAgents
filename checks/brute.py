from itertools import combinations
# A GAS: actions dict name -> (pre(s), guard(s), eff(s), acq(s), rel(s)); conflict set of frozensets
def committed_runs(acts, conflict, s0, maxlen):
    out=[]
    def go(s,F,run):
        if not F and run: out.append((tuple(run),s))
        if len(run)>=maxlen: return
        for a,(pre,guard,eff,acq,rel) in acts.items():
            if a not in F and pre(s) and guard(s) and all(frozenset({a,b}) not in conflict for b in F) and ('B'+a) not in run:
                go(s,F|{a},run+['B'+a])
            if a in F:
                go(eff(s),F-{a},run+['E'+a])
    go(s0,frozenset(),[]); return out
def dirty_runs(acts, conflict, s0, maxlen):
    out=[]
    def go(s,F,run):
        if not F and run: out.append((tuple(run),s))
        if len(run)>=maxlen: return
        for a,(pre,guard,eff,acq,rel) in acts.items():
            if a not in F and pre(s) and guard(s) and all(frozenset({a,b}) not in conflict for b in F) and ('B'+a) not in run:
                go(acq(s),F|{a},run+['B'+a])
            if a in F:
                go(rel(s),F-{a},run+['E'+a])
    go(s0,frozenset(),[]); return out
def step_reach(acts, conflict, s0, maxsteps=6):
    seen={(s0,())}; frontier=[(s0,())]; res=[]
    names=list(acts)
    for _ in range(maxsteps):
        nf=[]
        for s,seq in frontier:
            for k in range(1,len(names)+1):
                for U in combinations(names,k):
                    if any(frozenset({x,y}) in conflict for x,y in combinations(U,2)): continue
                    if all(acts[a][0](s) and acts[a][1](s) for a in U):
                        t=s
                        for a in U: t=acts[a][2](t)
                        nf.append((t,seq+(U,))); res.append((t,seq+(U,)))
        frontier=nf
    return res
# ---- Fig 5.1 net as GAS: state = frozenset of marked places
def net(pre,post,inh):
    def P(s): return pre<=s and not ((post-pre)&s)
    def G(s): return not (inh & s)
    def E(s): return (s-pre)|post
    def A(s): return s-pre
    def R(s): return s|post
    return (P,G,E,A,R)
acts={'a':net({'s1'},{'s3'},set()),'b':net({'s3'},{'s5'},set()),'c':net({'s2'},{'s4'},{'s3'})}
nb=lambda t:None
conf={frozenset({'a','b'})}
s0=frozenset({'s1','s2'})
cr=[r for r,s in committed_runs(acts,conf,s0,6) if len(r)==6]
print("committed complete runs with a,b,c:",len(cr))
thesis="BaEaBbEbBcEc BcEcBaEaBbEb BaBcEcEaBbEb BaBcEaEcBbEb BcBaEcEaBbEb BcBaEaEcBbEb BaBcEaBbEbEc BaBcEaBbEcEb BcBaEaBbEbEc BcBaEaBbEcEb".split()
mine={''.join(r) for r in cr}
print("matches thesis list exactly:", mine==set(thesis), sorted(mine-set(thesis)), sorted(set(thesis)-mine))
dr=[''.join(r) for r,s in dirty_runs(acts,conf,s0,6) if len(r)==6]
print("dirty extra runs:", sorted(set(dr)-mine))
s1=frozenset({'s3','s2'})
print("step {b,c} enabled after a:", all(acts[x][0](s1) and acts[x][1](s1) for x in 'bc'))
# ---- Theorem 2 witness: vars da,db,dc
def mk(var,pre_extra,guard_forbid):
    P=lambda s: var not in s and pre_extra<=s
    G=lambda s: not (guard_forbid & s)
    E=lambda s: s|{var}
    return (P,G,E,lambda s:s,E)
acts2={'a':mk('da',set(),{'dc'}),'b':mk('db',{'da'},{'dc'}),'c':mk('dc',set(),{'da'})}
tgt=frozenset({'da','db','dc'})
st=step_reach(acts2,set(),frozenset())
print("Thm2: step runs reaching all-done:", [q for t,q in st if t==tgt])
ir=[''.join(r) for r,s in committed_runs(acts2,set(),frozenset(),6) if s==tgt]
print("Thm2: committed runs reaching all-done:", ir)
