from dataclasses import dataclass

@dataclass(frozen=True)
class Id:
    i: int

    def __lt__(self, other: Id):
        return self.i < other.i

    def __repr__(self):
        return "id" + str(self.i)

@dataclass(frozen=True)
class UF_Node: # node using uninterpreted function
    f: str
    args: tuple[Id]

    def __repr__(self):
        if len(self.args) > 0:
            return self.f + "(" + ", ".join(map(str, self.args)) + ")"
        return self.f

@dataclass(frozen=True)
class AC_Node: # node using AC function
    args: tuple[Id]

    def __post_init__(self):
        assert(isinstance(self.args, tuple))
        for v in self.args:
            assert(isinstance(v, Id))
        assert(self.args == tuple(sorted(self.args)))

    def mk(it) -> AC_Node:
        it = tuple(sorted(list(it)))
        return AC_Node(it)

    def __add__(self, other: AC_Node):
        out = list(self.args) + list(other.args)
        out = sorted(out)
        return AC_Node(tuple(out))

    # monomial ordering.
    def __gt__(self, other: AC_Node):
        if len(self.args) > len(other.args): return True
        if len(self.args) < len(other.args): return False

        for (x, y) in zip(self.args[::-1], other.args[::-1]):
            if x > y: return True
            if x < y: return False

        assert(self == other)
        return False

    def __repr__(self):
        return "{" + " + ".join(map(str, self.args)) + "}"

type Node = UF_Node | AC_Node

@dataclass
class ACEGraph:
    unionfind: dict[Id, Id]
    uf_hashcons: dict[UF_Node, Id]
    ac_hashcons: list[(AC_Node, AC_Node)] # should be a dict too

    def __init__(self):
        self.unionfind = {}
        self.uf_hashcons = {}
        self.ac_hashcons = []

    def add_uf_node(self, f: str, args) -> Id:
        n = UF_Node(f, tuple(map(self.find, args)))

        if n in self.uf_hashcons:
            return self.uf_hashcons[n]

        i = Id(len(self.unionfind))
        self.unionfind[i] = i
        self.uf_hashcons[n] = i
        return i

    def add_ac_node(self, args) -> Id:
        n = AC_Node.mk(args)
        n = self.canon_ac_node(n)
        if len(n.args) == 1: return n.args[0]

        i = Id(len(self.unionfind))
        self.unionfind[i] = i
        self.ac_hashcons.append((n, AC_Node((i,))))
        return i

    def find(self, x: Id) -> Id:
        while self.unionfind[x] != x:
            x = self.unionfind[x]
        return x

    def dump(self):
        for (n, i) in self.unionfind.items():
            print(f"unionfind: {n} -> {i}")
        for (n, i) in self.uf_hashcons.items():
            print(f"uf_hashcons: {n} -> {i}")
        for (n, i) in self.ac_hashcons:
            print(f"ac_hashcons: {n} -> {i}")

    def is_equal(self, x: Id, y: Id) -> bool:
        self.rebuild()
        self.dump()
        return self.find(x) == self.find(y)

    def union(self, x: Id, y: Id):
        x = self.find(x)
        y = self.find(y)
        if x == y: return
        if x < y:
            self.unionfind[y] = x
        elif y < x:
            self.unionfind[x] = y

    def rebuild(self):
        while True:
            if self.rebuild_uf_step(): continue
            if self.rebuild_ac_step(): continue
            break

    def rebuild_ac_step(self):
        changed = False

        # canon rules via unionfind
        ac_hashcons = []
        for (lhs, rhs) in self.ac_hashcons:
            lhs = self.weak_canon_ac_node(lhs)
            rhs = self.canon_ac_node(rhs) # We want the actual normal form in the rhs.
            e = (lhs, rhs)
            if e not in ac_hashcons:
                ac_hashcons.append(e)
        self.ac_hashcons = ac_hashcons

        # compute CPs of rules
        L = list(self.ac_hashcons)
        for (al, ar) in L:
            for (bl, br) in L:
                (s1, s2) = unify(al, bl)
                lhs = s1+ar
                rhs = s2+br
                lhs = self.canon_ac_node(lhs)
                rhs = self.canon_ac_node(rhs)

                if lhs == rhs: continue
                changed = True

                if len(lhs.args) == len(rhs.args) == 1:
                    self.union(lhs.args[0], rhs.args[0])
                elif lhs < rhs:
                    self.ac_hashcons.append((rhs, lhs))
                elif lhs > rhs:
                    self.ac_hashcons.append((lhs, rhs))
                else:
                    assert(False)

    def rebuild_uf_step(self):
        changed = False
        h = {}
        for (n, i) in self.uf_hashcons.items():
            n = UF_Node(n.f, tuple(map(self.find, n.args)))
            i = self.find(i)

            # Storing this is redundant
            if n == AC_Node((i,)): continue

            if n in h:
                changed = True
                self.union(h[n], i)
            else:
                h[n] = i
        self.uf_hashcons = h
        return changed

    # respects the unionfind, but not the ac_hashcons.
    def weak_canon_ac_node(self, n: AC_Node) -> AC_Node:
        args = list(map(self.find, n.args))
        args = sorted(args)
        n = AC_Node(tuple(args))
        return n

    def canon_ac_node(self, n: AC_Node) -> AC_Node:
        n = self.weak_canon_ac_node(n)

        while True:
            changed = False
            for (lhs, rhs) in self.ac_hashcons:
                x = ac_match(lhs, n)
                if x is not None:
                    n = rhs+x
                    changed = True
            if not changed:
                break
        return n

# (x, y) = unify(a, b)
# ->
# x+a = y+b
def unify(a: AC_Node, b: AC_Node) -> (AC_Node, AC_Node):
    i_a = 0
    i_b = 0

    x = AC_Node(())
    y = AC_Node(())
    while i_a < len(a.args) and i_b < len(b.args):
        v_a = a.args[i_a]
        v_b = b.args[i_b]
        if v_a == v_b:
            i_a += 1
            i_b += 1
        elif v_a < v_b:
            y = y + AC_Node((v_a,))
            i_a += 1
        elif v_a > v_b:
            x = x + AC_Node((v_b,))
            i_b += 1
    x += AC_Node(tuple(b.args[i_b:]))
    y += AC_Node(tuple(a.args[i_a:]))
    return (x, y)

# returns x, s.t. pat+x = t, or None if such x does not exist.
def ac_match(pat: AC_Node, t: AC_Node) -> AC_Node | None:
    (x, y) = unify(pat, t)
    if y != AC_Node(()): return
    return x

# Example:

eg = ACEGraph()

# hack to allow adding Ids
Id.__add__ = lambda slf, other: eg.add_ac_node((slf, other))

const = lambda a: eg.add_uf_node(a, ())
f = lambda x, y: eg.add_uf_node("f", (x, y))
g = lambda x, y: eg.add_uf_node("g", (x, y))

a = const("a")
b = const("b")

eg.union(b+b, a+a)
assert(eg.is_equal(a+b+a+b, a+a+a+a))
