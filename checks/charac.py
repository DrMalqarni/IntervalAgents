import random, itertools
# States: tuples of NV bits. Each action owns disjoint variables; acq writes some owned vars, rel writes the rest -> all pieces of independent actions commute.
def rand_system(rng, NA=3, NV=6):
    vars_=list(range(NV)); rng.shuffle(vars_)
    own={a:vars_[2*a:2*a+2] for a in range(NA)}
    states=list(itertools.product([0,1],repeat=NV))
    acts={}
    for a in range(NA):
        v1,v2=own[a]
        acq_val=rng.randint(0,1); rel_val=rng.randint(0,1)
        mode=rng.choice(['committed','dirty'])
        def acq(s,v1=v1,val=acq_val,mode=mode):
            if mode=='committed': return s
            s=list(s); s[v1]=val; return tuple(s)
        def rel(s,v1=v1,v2=v2,val=acq_val,rv=rel_val,mode=mode):
            s=list(s); 
            if mode=='committed': s[v1]=val
            s[v2]=rv; return tuple(s)
        # random pre/grd: depend on few random vars
        dep=rng.sample(range(NV),2); tab={k:rng.random()<0.6 for k in itertools.product([0,1],repeat=2)}
        en=lambda s,dep=dep,tab=tab: tab[(s[dep[0]],s[dep[1]])]
        acts[a]=(en,acq,rel)
    conf=set()
    for a,b in itertools.combinations(range(NA),2):
        if rng.random()<0.25: conf|={(a,b),(b,a)}
    return states,acts,conf
def eff(acts,a,s): return acts[a][2](acts[a][1](s))
def run_word(acts,conf,s,word):
    F=set()
    for ev,a in word:
        en,acq,rel=acts[a]
        if ev=='B':
            if a in F or not en(s) or any((a,b) in conf for b in F): return None
            s=acq(s); F.add(a)
        else:
            if a not in F: return None
            s=rel(s); F.discard(a)
    return s if not F else None
def conservative(states,acts,conf):
    NA=len(acts)
    for s in states:
        for k in range(1,NA+1):
            for U in itertools.combinations(range(NA),k):
                indep=all((a,b) not in conf for a,b in itertools.combinations(U,2))
                step = indep and all(acts[a][0](s) for a in U)
                t=s
                for a in U: t=eff(acts,a,t)
                words=[[('B',x) for x in p]+[('E',y) for y in q] for p in itertools.permutations(U) for q in itertools.permutations(U)]
                res=[run_word(acts,conf,s,w) for w in words]
                all2 = all(r==t for r in res) if step else None
                some3 = [r for r in res if r is not None]
                if step and not all2: return False
                if not step and some3: return False
                if step and any(r!=t for r in some3): return False
    return True
def transparent(states,acts,conf):
    NA=len(acts)
    for a,b in itertools.permutations(range(NA),2):
        if (a,b) in conf: continue
        for t in states:
            if acts[a][0](t) and (acts[b][0](t) != acts[b][0](acts[a][1](t))): return False
    return True
rng=random.Random(7); agree=0; counts={}
for i in range(3000):
    st,ac,cf=rand_system(rng)
    c=conservative(st,ac,cf); tr=transparent(st,ac,cf)
    counts[(c,tr)]=counts.get((c,tr),0)+1
print(counts)
