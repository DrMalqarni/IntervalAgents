import random, itertools
# Elementary inhibitor nets; state = frozenset over places P plus markers ('m',t).
def mk(net):
    P,T=net['P'],net['T']
    pre,post,inh=net['pre'],net['post'],net['inh']
    cons={p:[t for t in T if p in pre[t]] for p in P}
    def en(t,M): return pre[t]<=M and not ((post[t]-pre[t])&M) and not (inh[t]&M) and not any(('m',r) in M for p in inh[t] for r in cons[p])
    def acq(t,M): return (M-pre[t])|{('m',t)}
    def rel(t,M): return (M-{('m',t)})|post[t]
    def indep(t,u): return t!=u and not ((pre[t]|post[t])&(pre[u]|post[u]))
    return en,acq,rel,indep
def transparent(net,states):
    en,acq,rel,indep=mk(net)
    for a,b in itertools.permutations(net['T'],2):
        if not indep(a,b): continue
        for s in states:
            if en(a,s) and en(b,s)!=en(b,acq(a,s)): return False
    return True
rng=random.Random(3); bad=0
for i in range(2000):
    P=[f'p{i}' for i in range(5)]; T=['t0','t1','t2']
    net={'P':P,'T':T,'pre':{},'post':{},'inh':{}}
    for t in T:
        net['pre'][t]=frozenset(rng.sample(P,rng.randint(1,2)))
        net['post'][t]=frozenset(rng.sample([p for p in P if p not in net['pre'][t]],1))
        net['inh'][t]=frozenset(rng.sample(P,rng.randint(0,2)))-net['pre'][t]
    marks=[('m',t) for t in T]
    # states with no marker of a transition whose preset is still marked is irrelevant; test all subsets of P plus markers
    states=[frozenset(c)|frozenset(m) for c in itertools.chain.from_iterable(itertools.combinations(P,k) for k in range(6)) for m in itertools.chain.from_iterable(itertools.combinations(marks,k) for k in range(4))]
    if not transparent(net,states): bad+=1
print("random ENIs where the double-arc discipline is NOT transparent:", bad, "of 2000")
# naive dirty (no markers) on same random nets: how often non-transparent

# Fig 5.1 with the marker (double-arc) discipline: complete runs with one occurrence each
net={'P':['s1','s2','s3','s4','s5'],'T':['a','b','c'],
     'pre':{'a':frozenset({'s1'}),'b':frozenset({'s3'}),'c':frozenset({'s2'})},
     'post':{'a':frozenset({'s3'}),'b':frozenset({'s5'}),'c':frozenset({'s4'})},
     'inh':{'a':frozenset(),'b':frozenset(),'c':frozenset({'s3'})}}
en,acq,rel,indep=mk(net)
runs=[]
def go(M,F,w):
    if len(w)==6:
        if not F: runs.append(''.join(w))
        return
    for t in net['T']:
        if t not in F and ('B'+t) not in w and en(t,M) and all(indep(t,u) for u in F): go(acq(t,M),F|{t},w+['B'+t])
        if t in F: go(rel(t,M),F-{t},w+['E'+t])
go(frozenset({'s1','s2'}),frozenset(),[])
thesis=set("BaEaBbEbBcEc BcEcBaEaBbEb BaBcEcEaBbEb BaBcEaEcBbEb BcBaEcEaBbEb BcBaEaEcBbEb BaBcEaBbEbEc BaBcEaBbEcEb BcBaEaBbEbEc BcBaEaBbEcEb".split())
print("marker discipline on Fig 5.1 == thesis 10 runs:", set(runs)==thesis, len(runs))
