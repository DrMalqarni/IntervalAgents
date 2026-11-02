"""Net-like guarded action systems: places are the variables, each action has disjoint
pre (consumed), post (produced), read (positive context) and inh (negative context) sets.
Conflict: shared pre or post place (EN-system structural conflict).  Contexts never conflict.
Start condition: pre marked, post empty (contact-freeness), read marked, inh empty.
Readings: 'atstart'  : contexts checked at the beginning only
          'overall'  : contexts checked at the beginning and throughout (over = read marked & inh empty)
          'closed'   : as 'overall' and also at the end
Disciplines: 'committed' (consume and produce at the end), 'consuming' (consume at the beginning,
produce at the end), 'startonly' (consume and produce at the beginning).
"""
import random, itertools
from gas import *


def pred_from(cond):
    """cond: list of (var, value). Mask of states satisfying all."""
    m = 0
    for s in range(NS):
        if all(bit(s, v) == val for v, val in cond):
            m |= 1 << s
    return m


def rand_net(rng, NA=3, disc='committed', reading='atstart', p_ctx=0.6):
    start, over, end, acq, rel, mode = [], [], [], [], [], []
    places = list(range(NV))
    pres, posts = [], []
    for a in range(NA):
        k_pre = rng.choice([0, 1, 1, 2]); k_post = rng.choice([0, 1, 1, 2])
        pool = places[:]
        rng.shuffle(pool)
        pre = pool[:k_pre]; post = pool[k_pre:k_pre + k_post]
        rest = pool[k_pre + k_post:]
        ctx = [v for v in rest if rng.random() < p_ctx / 2]
        read = [v for v in ctx if rng.random() < 0.5]
        inh = [v for v in ctx if v not in read]
        pres.append(set(pre)); posts.append(set(post))
        m = disc if isinstance(disc, str) else disc[a]
        mode.append(m)
        own = [(v, 1) for v in pre] + [(v, 0) for v in post]
        ctxc = [(v, 1) for v in read] + [(v, 0) for v in inh]
        st = pred_from(own + ctxc)
        if reading == 'atstart':
            ov, en = ALL, ALL
        elif reading == 'overall':
            ov, en = pred_from(ctxc), ALL
        elif reading == 'closed':
            ov, en = pred_from(ctxc), pred_from(ctxc)
        else:
            raise ValueError(reading)
        start.append(st); over.append(ov); end.append(en)
        def consume(s, pre=pre):
            for v in pre: s = set_var(s, v, 0)
            return s
        def produce(s, post=post):
            for v in post: s = set_var(s, v, 1)
            return s
        if m == 'committed':
            acq.append([s for s in range(NS)]); rel.append([produce(consume(s)) for s in range(NS)])
        elif m == 'consuming':
            acq.append([consume(s) for s in range(NS)]); rel.append([produce(s) for s in range(NS)])
        elif m == 'startonly':
            acq.append([produce(consume(s)) for s in range(NS)]); rel.append([s for s in range(NS)])
        else:
            raise ValueError(m)
    conflict = set()
    for a, b in itertools.combinations(range(NA), 2):
        if (pres[a] | posts[a]) & (pres[b] | posts[b]):
            conflict |= {(a, b), (b, a)}
    S = Sys(NA, start, over, end, acq, rel, conflict, mode)
    S.pres, S.posts = pres, posts
    return S
