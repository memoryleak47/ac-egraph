from dataclasses import dataclass

@dataclass(frozen=True)
class Id:
    i: int

    def __lt__(self, other: Id):
        return self.i < other.i

@dataclass(frozen=True)
class UF_Node: # node using uninterpreted function
    f: str
    args: tuple[Id]

@dataclass(frozen=True)
class AC_Node: # node using AC function
    args: tuple[Id]

    def __add__(self, other: AC_Node):
        out = list(self.args) + list(other.args)
        out = sorted(out)
        return AC_Node(tuple(out))

    # monomial ordering.
    def __gt__(self, other: AC_Node):
        if len(self.args) > len(other.args): return True
        if len(self.args) < len(other.args): return False

        for (x, y) in zip(self.args, other.args):
            if x > y: return True
            if x < y: return False

        assert(self == other)
        return False

type Node = UF_Node | AC_Node

@dataclass
class ACEGraph:
    uf: dict[Id, Id]
    hashcons: dict[Node, Id]
    ac_eqs: list[(AC_Node, AC_Node)]

    def __init__(self):
        self.uf = {}
        self.hashcons = {}
        self.ac_eqs = []

    def canon_node(self, n: Node) -> Id:
        if isinstance(n, UF_Node):
            n = UF_Node(n.f, tuple(map(self.find, n.args)))
        elif isinstance(n, AC_Node):
            n = self.simplify_ac_node(n)
        return n

    def add(self, n: Node) -> Id:
        n = self.canon_node(n)
        if n in self.hashcons:
            return self.hashcons[n]
        i = Id(len(self.uf))
        self.uf[i] = i
        self.hashcons[n] = i
        if isinstance(n, AC_Node):
            self.ac_eqs.append((n, AC_Node((i,))))
        return i

    def find(self, x: Id) -> Id:
        while self.uf[x] != x:
            x = self.uf[x]
        return x

    def union(self, x: Id, y: Id):
        x = self.find(x)
        y = self.find(y)
        if x == y: return
        self.uf[x] = y
        self.ac_eqs.append((AC_Node((x,)), AC_Node((y,))))

    def rebuild(self):
        while True:
            if self.rebuild_uf_step(): continue
            if self.rebuild_ac_step(): continue
            break

    def rebuild_ac_step(self):
        changed = False
        for (al, ar) in self.ac_eqs:
            for (bl, br) in self.ac_eqs:
                (s1, s2) = unify(al, bl)
                lhs = s1+al
                rhs = s2+bl
                lhs = self.simplify_ac_node(lhs)
                rhs = self.simplify_ac_node(rhs)

                if lhs == rhs: continue
                changed = True

                if len(lhs.args) == len(rhs.args) == 1:
                    self.union(lhs.args[0], rhs.args[0])

                if lhs < rhs:
                    self.ac_eqs.append((rhs, lhs))
                elif lhs > rhs:
                    self.ac_eqs.append((lhs, rhs))
                else:
                    assert(False)

    def rebuild_eg_step(self):
        changed = False
        new_h = {}
        for (n, i) in self.hashcons.items():
            n = self.canon_node(n)
            i = self.find(i)
            if n in h:
                changed = True
                self.union(n[h], i)
            else:
                new_h[n] = i
        self.hashcons = new_h
        return changed

    def simplify_ac_node(self, n: AC_Node) -> AC_Node:
        args = list(map(self.find, n.args))
        args = sorted(args)
        n = AC_Node(tuple(args))

        while True:
            changed = False
            for (lhs, rhs) in self.ac_eqs:
                x = ac_match(lhs, n)
                if x is not None:
                    n = rhs+x
                    changed = True
            if not changed:
                break


# (x, y) = unify(a, b)
# ->
# x+a = y+b
def unify(a: AC_Node, b: AC_Node) -> (AC_Node, AC_Node):
    i_a = 0
    i_b = 0

    x = AC_Node(())
    y = AC_Node(())
    while True:
        if a.args[i_a] == b.args[i_b]:
            i_a += 1
            i_b += 1
            continue
        if a.args[i_a] < b.args[i_b]:
            y = y + AC_Node()
            i_a += 1
    return (x, y)

# returns x, s.t. pat+x = t, or None if such x does not exist.
def ac_match(pat: AC_Node, t: AC_Node) -> AC_Node | None:
    (x, y) = unify(pat, t)
    if y != AC_Node(()): return
    return x

# Example:
eg = ACEGraph()
a = eg.add(UF_Node("a", ()))
b = eg.add(UF_Node("b", ()))

c = eg.add(AC_Node((a, b)))
d = eg.add(AC_Node((b, a)))
print(eg.find(c))
print(eg.find(d))
