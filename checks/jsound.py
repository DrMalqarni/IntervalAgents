import random, itertools
# Random GAS as in charac.py; test three properties over ALL states:
#  T  = acquire-transparency (en_a t -> (en_b t <-> en_b (acq_a t)))
#  J  = Janicki-soundness local condition: en_a t & en_b(acq_a t) -> en_b t & en_a(acq_b t)   (BB-swap closure)
#  C  = step-conservativity (as in charac.py)
#  Jrun = direct check that the run set (each action at most once, any start state) is closed under adjacent BB/EE swaps
def rand_system(rng, NA=3, NV=6):
    vars_=list(range(NV)); rng.shuffle(vars_)
    own={a:vars_[2*a:2*a+2] for a in range(NA)}
    states=list(itertools.product([0,1],repeat=NV))
    acts={}
    for a in range(NA):
        v1,v2=own[a]; av=rng.randint(0,1); rv=rng.randint(0,1); mode=rng.choice(['committed','dirty'])
        def acq(s,v1=v1,val=av,mode=mode):
            if mode=='committed': return s
            s=list(s); s[v1]=val; return tuple(s)
        def rel(s,v1=v1,v2=v2,val=av,rv=rv,mode=mode):
            s=list(s)
            if mode=='committed': s[v1]=val
            s[v2]=rv; return tuple(s)
        dep=rng.sample(range(NV),2); tab={k:rng.random()<0.6 for k in itertools.product([0,1],repeat=2)}
        en=lambda s,dep=dep,tab=tab: tab[(s[dep[0]],s[dep[1]])]
        acts[a]=(en,acq,rel)
    conf=set()
    for a,b in itertools.combinations(range(NA),2):
        if rng.random()<0.25: conf|={(a,b),(b,a)}
    return states,acts,conf
def indep(conf,a,b): return a!=b and (a,b) not in conf
def T(states,acts,conf):
    return all(not(acts[a][0](t)) or (acts[b][0](t)==acts[b][0](acts[a][1](t))) for a,b in itertools.permutations(acts,2) if indep(conf,a,b) for t in states)
def J(states,acts,conf):
    return all(not(acts[a][0](t) and acts[b][0](acts[a][1](t))) or (acts[b][0](t) and acts[a][0](acts[b][1](t))) for a,b in itertools.permutations(acts,2) if indep(conf,a,b) for t in states)
def step_ok(acts,conf,s,U):
    return all(indep(conf,a,b) for a,b in itertools.combinations(U,2)) and all(acts[a][0](s) for a in U)
def run(acts,conf,s,word):
    F=set()
    for ev,a in word:
        en,acq,rel=acts[a]
        if ev=='B':
            if a in F or not en(s) or any((a,b) in conf for b in F): return None
            s=acq(s); F.add(a)
        else:
            if a not in F: return None
            s=rel(s); F.discard(a)
    return (s,frozenset(F))
def Jrun(states,acts,conf):
    NA=len(acts); evs=[(e,a) for a in acts for e in 'BE']
    for s in states:
        # enumerate runs with each action at most once, DFS
        stack=[((),s,frozenset())]
        while stack:
            w,t,F=stack.pop()
            for ev,a in evs:
                if ev=='B' and a in F or ev=='E' and a not in F: continue
                if ev=='B' and any(x==('B',a) for x in w): continue
                r=run(acts,conf,s,w+((ev,a),))
                if r is None: continue
                w2=w+((ev,a),)
                # check swap of last two if same kind
                if len(w2)>=2 and w2[-1][0]==w2[-2][0] and w2[-1][1]!=w2[-2][1]:
                    sw=w2[:-2]+(w2[-1],w2[-2])
                    r2=run(acts,conf,s,sw)
                    if r2 is None or r2!=r: return False
                stack.append((w2,r[0],r[1]))
    return True
def C(states,acts,conf):
    NA=len(acts)
    for s in states:
        for k in range(1,NA+1):
            for U in itertools.combinations(range(NA),k):
                st=step_ok(acts,conf,s,U)
                t=s
                for a in U: t=acts[a][2](acts[a][1](t))
                words=[[('B',x) for x in p]+[('E',y) for y in q] for p in itertools.permutations(U) for q in itertools.permutations(U)]
                res=[run(acts,conf,s,w) for w in words]
                ok=[r for r in res if r is not None]
                if st and (len(ok)!=len(words) or any(r[0]!=t for r in ok)): return False
                if not st and ok: return False
    return True
rng=random.Random(11); cnt={}
for i in range(1500):
    st,ac,cf=rand_system(rng)
    key=(T(st,ac,cf),J(st,ac,cf),Jrun(st,ac,cf),C(st,ac,cf))
    cnt[key]=cnt.get(key,0)+1
for k,v in sorted(cnt.items()): print("T=%s J=%s Jrun=%s C=%s : %d"%(k+(v,)))
