"""Guarded action systems with a visibility discipline and three condition sets
(start, over, end), as fixed in the plan doc ("Formal statements to test").

States are bit vectors packed into ints (NV bits).  Predicates are int masks:
bit s set iff the predicate holds in state s.  Effects are lists state -> state.

Semantics (blocking = validation, see note in checkA.py):
  B_a at (s,F): a not in F, start_a(s), no conflict with F; s' = acq_a(s);
                over_b(s') for all b in F+{a}.
  E_a at (s,F): a in F, end_a(s); s' = rel_a(s); over_b(s') for all b in F-{a}.
Plain generation (fire0) ignores over/end; a generated run is valid iff it is a
blocking run, so the two notions define the same set of valid runs.
"""
import random, itertools

NV = 6
NS = 1 << NV
ALL = (1 << NS) - 1   # predicate mask: true in every state


def bit(m, s):
    return (m >> s) & 1


class Sys:
    def __init__(self, NA, start, over, end, acq, rel, conflict, mode):
        self.NA = NA
        self.start, self.over, self.end = start, over, end
        self.acq, self.rel = acq, rel
        self.conflict = conflict
        self.mode = mode
        self.acts = list(range(NA))
        # effect of a complete action
        self.eff = [[rel[a][acq[a][s]] for s in range(NS)] for a in range(NA)]
        # en2: the singleton block B_a E_a is valid from s
        self.en2 = [0] * NA
        for a in range(NA):
            m = 0
            for s in range(NS):
                if bit(start[a], s) and bit(over[a], acq[a][s]) and bit(end[a], acq[a][s]):
                    m |= 1 << s
            self.en2[a] = m

    def indep(self, a, b):
        return a != b and (a, b) not in self.conflict

    def pairwise_indep(self, U):
        return all(self.indep(a, b) for a, b in itertools.combinations(U, 2))

    # ---- interval semantics -------------------------------------------------
    def fire(self, c, e):
        """Blocking semantics: one event.  c = (s, F) with F a bitmask."""
        s, F = c
        kind, a = e
        if kind == 'B':
            if (F >> a) & 1 or not bit(self.start[a], s):
                return None
            for b in range(self.NA):
                if (F >> b) & 1 and (a, b) in self.conflict:
                    return None
            s2 = self.acq[a][s]
            F2 = F | (1 << a)
            for b in range(self.NA):
                if (F2 >> b) & 1 and not bit(self.over[b], s2):
                    return None
            return (s2, F2)
        else:
            if not (F >> a) & 1 or not bit(self.end[a], s):
                return None
            s2 = self.rel[a][s]
            F2 = F & ~(1 << a)
            for b in range(self.NA):
                if (F2 >> b) & 1 and not bit(self.over[b], s2):
                    return None
            return (s2, F2)

    def fire0(self, c, e):
        """Plain generation: over and end ignored."""
        s, F = c
        kind, a = e
        if kind == 'B':
            if (F >> a) & 1 or not bit(self.start[a], s):
                return None
            for b in range(self.NA):
                if (F >> b) & 1 and (a, b) in self.conflict:
                    return None
            return (self.acq[a][s], F | (1 << a))
        else:
            if not (F >> a) & 1:
                return None
            return (self.rel[a][s], F & ~(1 << a))

    def run(self, s, word, plain=False):
        c = (s, 0)
        f = self.fire0 if plain else self.fire
        for e in word:
            c = f(c, e)
            if c is None:
                return None
        return c

    # ---- step semantics ----------------------------------------------------
    def effU(self, U, s):
        for a in U:
            s = self.eff[a][s]
        return s

    @staticmethod
    def block_words(U):
        U = list(U)
        return [[('B', x) for x in p] + [('E', y) for y in q]
                for p in itertools.permutations(U) for q in itertools.permutations(U)]


# ---- random systems ---------------------------------------------------------

def rand_pred(rng, p_true=0.3):
    """A random predicate over two variables, or True."""
    if rng.random() < p_true:
        return ALL
    d0, d1 = rng.sample(range(NV), 2)
    tab = {k: rng.random() < 0.6 for k in itertools.product([0, 1], repeat=2)}
    m = 0
    for s in range(NS):
        if tab[((s >> d0) & 1, (s >> d1) & 1)]:
            m |= 1 << s
    return m


def set_var(s, v, val):
    return (s | (1 << v)) if val else (s & ~(1 << v))


def rand_system(rng, NA=3, disc=None, reading=None, p_conf=0.25, p_true=0.3):
    """disc: None (random per action), or one of 'committed', 'consuming', 'startonly',
    or a list per action.  reading: None (three independent random condition sets),
    'atstart' (over = end = True), 'overall' (over = start, end = True),
    'closed' (start = over = end), 'atend' (start = over = True)."""
    vars_ = list(range(NV))
    rng.shuffle(vars_)
    if 2 * NA <= NV:
        own = {a: vars_[2 * a:2 * a + 2] for a in range(NA)}
    else:
        assert NA <= NV
        own = {a: [vars_[a], vars_[a]] for a in range(NA)}   # one variable per action
    start, over, end, acq, rel, mode = [], [], [], [], [], []
    for a in range(NA):
        v1, v2 = own[a]
        av, rv = rng.randint(0, 1), rng.randint(0, 1)
        if disc is None:
            m = rng.choice(['committed', 'consuming', 'startonly'])
        elif isinstance(disc, str):
            m = disc
        else:
            m = disc[a]
        mode.append(m)
        if m == 'committed':
            acq.append([s for s in range(NS)])
            rel.append([set_var(set_var(s, v1, av), v2, rv) for s in range(NS)])
        elif m == 'consuming':
            acq.append([set_var(s, v1, av) for s in range(NS)])
            rel.append([set_var(s, v2, rv) for s in range(NS)])
        elif m == 'startonly':
            acq.append([set_var(set_var(s, v1, av), v2, rv) for s in range(NS)])
            rel.append([s for s in range(NS)])
        else:
            raise ValueError(m)
        st = rand_pred(rng, p_true)
        if reading is None:
            ov, en = rand_pred(rng, p_true), rand_pred(rng, p_true)
        elif reading == 'atstart':
            ov, en = ALL, ALL
        elif reading == 'overall':
            ov, en = st, ALL
        elif reading == 'closed':
            ov, en = st, st
        elif reading == 'atend':
            en = st
            st, ov = ALL, ALL
        else:
            raise ValueError(reading)
        start.append(st); over.append(ov); end.append(en)
    conflict = set()
    for a, b in itertools.combinations(range(NA), 2):
        if rng.random() < p_conf:
            conflict |= {(a, b), (b, a)}
    return Sys(NA, start, over, end, acq, rel, conflict, mode)


# ---- enumeration of valid runs, each action at most once --------------------

def all_runs(S, s, max_once=True):
    """All valid runs from (s, 0) in which each action begins at most once.
    Returns list of (word, final config)."""
    out = []
    stack = [((), (s, 0), 0)]   # word, config, begun-mask
    while stack:
        w, c, begun = stack.pop()
        out.append((w, c))
        for a in range(S.NA):
            if not (begun >> a) & 1:
                c2 = S.fire(c, ('B', a))
                if c2 is not None:
                    stack.append((w + (('B', a),), c2, begun | (1 << a)))
            if (c[1] >> a) & 1:
                c2 = S.fire(c, ('E', a))
                if c2 is not None:
                    stack.append((w + (('E', a),), c2, begun))
    return out
