"""Hand-made 3-action witness: pairwise sound but not sound.
Variables: x (bit 0, written by b), y (bit 1, written by c), others unused.
a: start = not y, over = not (x and y), end = True, committed, effect none (writes bit 2).
b: start = True, committed, rel sets x.      (start_b = not x would also do)
c: start = not x, committed, rel sets y.
All pairwise independent.
"""
from gas import *
from checkA import props

def pred(f):
    m = 0
    for s in range(NS):
        if f(s): m |= 1 << s
    return m
x = lambda s: (s >> 0) & 1
y = lambda s: (s >> 1) & 1
ident = [s for s in range(NS)]
start = [pred(lambda s: not y(s)), ALL, pred(lambda s: not x(s))]
over  = [pred(lambda s: not (x(s) and y(s))), ALL, ALL]
end   = [ALL, ALL, ALL]
acq   = [ident, ident, ident]
rel   = [[set_var(s, 2, 1) for s in range(NS)], [set_var(s, 0, 1) for s in range(NS)], [set_var(s, 1, 1) for s in range(NS)]]
S = Sys(3, start, over, end, acq, rel, set(), ['committed'] * 3)
P = props(S)
print(P)
# show the failing block
U = (0, 1, 2); s = 0
for w in S.block_words(U):
    if S.run(s, w) is None:
        print("invalid block word from state 0:", w)
        break
