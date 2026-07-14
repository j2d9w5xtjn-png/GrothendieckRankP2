#!/usr/bin/env python3
r"""Exact classification of residue-F2 principal rings of length six.

For a uniformizer t, every element has a unique expansion

    a0 + a1*t + ... + a5*t^5,  ai in {0,1}.

In mixed characteristic, if e=ord_m(2), then uniquely

    2 = t^e + c_{e+1} t^(e+1) + ... + c_5 t^5,  c_i in {0,1}.

This gives 16+8+4+2+1 mixed-characteristic coordinate presentations,
plus F2[t]/t^6.  The script constructs all 32 exact 64-element tables,
checks their complete arithmetic independently, and quotients them by all
possible changes of uniformizer.  A unital isomorphism is determined by the
image q of t; q must be one of the 16 elements of m-m^2.  Every such q is
tested, and every successful map is independently checked on all 64^2
addition and multiplication pairs.
"""

from __future__ import annotations

import itertools
import time


N = 6
ALL = tuple(range(1 << N))


def bits(x):
    return [(x >> i) & 1 for i in range(N)]


def encode(cs):
    return sum((int(c) & 1) << i for i, c in enumerate(cs[:N]))


class CarryRing:
    def __init__(self, e, tail):
        self.e = e
        self.tail = tuple(tail)
        if e is None:
            assert not tail
            self.label = "eqchar"
            self.support = ()
        else:
            assert 1 <= e <= 5 and len(tail) == 5 - e
            self.label = f"e{e}_" + ("".join(map(str, tail)) or "-")
            self.support = (e,) + tuple(
                e + 1 + i for i, c in enumerate(tail) if c
            )
        self.zero = 0
        self.one = 1
        self.t = 2
        self._add = self._sub = self._mul = None

    def reduce(self, coeffs):
        cs = list(coeffs[:N]) + [0] * max(0, N - len(coeffs))
        for i in range(N):
            q, cs[i] = divmod(cs[i], 2)
            if q and self.e is not None:
                for d in self.support:
                    if i + d < N:
                        cs[i + d] += q
        return encode(cs)

    def raw_add(self, a, b):
        aa, bb = bits(a), bits(b)
        return self.reduce([x + y for x, y in zip(aa, bb)])

    def raw_sub(self, a, b):
        aa, bb = bits(a), bits(b)
        return self.reduce([x - y for x, y in zip(aa, bb)])

    def raw_mul(self, a, b):
        aa, bb = bits(a), bits(b)
        cs = [0] * N
        for i in range(N):
            for j in range(N - i):
                cs[i + j] += aa[i] * bb[j]
        return self.reduce(cs)

    def build_tables(self):
        if self._add is not None:
            return
        self._add = [[self.raw_add(a, b) for b in ALL] for a in ALL]
        self._sub = [[self.raw_sub(a, b) for b in ALL] for a in ALL]
        self._mul = [[self.raw_mul(a, b) for b in ALL] for a in ALL]

    def add(self, a, b):
        return self._add[a][b] if self._add is not None else self.raw_add(a, b)

    def sub(self, a, b):
        return self._sub[a][b] if self._sub is not None else self.raw_sub(a, b)

    def mul(self, a, b):
        return self._mul[a][b] if self._mul is not None else self.raw_mul(a, b)

    def pow(self, a, n):
        out = self.one
        for _ in range(n):
            out = self.mul(out, a)
        return out

    def sum(self, xs):
        out = self.zero
        for x in xs:
            out = self.add(out, x)
        return out

    def relation_rhs(self, q):
        if self.e is None:
            return self.zero
        out = self.pow(q, self.e)
        for i, c in enumerate(self.tail, start=self.e + 1):
            if c:
                out = self.add(out, self.pow(q, i))
        return out

    def ideal_power(self, k):
        return {x for x in ALL if x & ((1 << k) - 1) == 0}

    def uniformizers(self):
        return sorted(self.ideal_power(1) - self.ideal_power(2))

    def characteristic(self):
        x = self.zero
        for n in range(1, 65):
            x = self.add(x, self.one)
            if x == self.zero:
                return n
        raise AssertionError("characteristic exceeds 64")


def presentations():
    out = [CarryRing(None, ())]
    for e in range(1, 6):
        out.extend(CarryRing(e, tail)
                   for tail in itertools.product((0, 1), repeat=5 - e))
    assert len(out) == 32 and len({R.label for R in out}) == 32
    return out


def additive_closure(R, seed):
    span = {R.zero}
    changed = True
    while changed:
        changed = False
        for a in list(span):
            for b in seed:
                c = R.add(a, b)
                if c not in span:
                    span.add(c)
                    changed = True
    return span


def validate_ring(R):
    R.build_tables()
    z, o, t = R.zero, R.one, R.t
    assert len(ALL) == 64
    assert R.pow(t, 5) != z and R.pow(t, 6) == z
    assert R.add(o, o) == R.relation_rhs(t)

    for a in ALL:
        assert R.add(a, z) == a
        assert R.sub(a, a) == z
        assert R.mul(a, o) == a
        assert R.mul(a, z) == z
    for a, b in itertools.product(ALL, repeat=2):
        assert R.add(a, b) == R.add(b, a)
        assert R.mul(a, b) == R.mul(b, a)
        assert R.add(R.sub(a, b), b) == a
    for a, b, c in itertools.product(ALL, repeat=3):
        assert R.add(R.add(a, b), c) == R.add(a, R.add(b, c))
        assert R.mul(R.mul(a, b), c) == R.mul(a, R.mul(b, c))
        assert R.mul(a, R.add(b, c)) == R.add(R.mul(a, b), R.mul(a, c))

    powers = [R.ideal_power(k) for k in range(1, 7)]
    assert [len(x) for x in powers] == [32, 16, 8, 4, 2, 1]
    for k, ideal in enumerate(powers, start=1):
        generated = {R.mul(R.pow(t, k), a) for a in ALL}
        assert generated == ideal
    m = powers[0]
    assert all(R.add(a, b) in m for a in m for b in m)
    assert all(R.mul(a, b) in m for a in m for b in ALL)
    units = {a for a in ALL if any(R.mul(a, b) == o for b in ALL)}
    assert units == set(ALL) - m
    soc = {a for a in ALL if all(R.mul(a, b) == z for b in m)}
    assert soc == powers[4] and len(soc) == 2
    assert len(R.uniformizers()) == 16
    assert additive_closure(R, [R.pow(t, i) for i in range(6)]) == set(ALL)

    expected_char = 2 if R.e is None else 1 << ((N + R.e - 1) // R.e)
    assert R.characteristic() == expected_char
    if R.e is None:
        assert R.add(o, o) == z
    else:
        assert R.add(o, o) in powers[R.e - 1]
        assert R.add(o, o) not in powers[R.e] if R.e < 6 else True


def evaluate_source_at(source, target, a, q):
    aa = bits(a)
    powers = [target.one]
    for _ in range(1, N):
        powers.append(target.mul(powers[-1], q))
    return target.sum(p for bit, p in zip(aa, powers) if bit)


def source_relation_at(source, target, q):
    if source.e is None:
        return target.zero
    out = target.pow(q, source.e)
    for i, c in enumerate(source.tail, start=source.e + 1):
        if c:
            out = target.add(out, target.pow(q, i))
    return out


def isomorphism_witnesses(source, target):
    # Deliberately test all target uniformizers even when characteristic or
    # ord_m(2) already rules out an isomorphism.  Thus the reported orbit
    # audit does not depend on pre-filtering by those invariants.
    two = target.add(target.one, target.one)
    witnesses = []
    for q in target.uniformizers():
        if source.e is None:
            if two != target.zero:
                continue
        elif source_relation_at(source, target, q) != two:
            continue
        image = [evaluate_source_at(source, target, a, q) for a in ALL]
        if len(set(image)) != 64:
            continue
        # Independent full table validation of every accepted presentation
        # map, rather than relying only on the defining relation.
        for a, b in itertools.product(ALL, repeat=2):
            assert image[source.add(a, b)] == target.add(image[a], image[b])
            assert image[source.mul(a, b)] == target.mul(image[a], image[b])
        assert image[source.one] == target.one and image[source.t] == q
        witnesses.append(q)
    return witnesses


class DSU:
    def __init__(self, xs):
        self.p = {x: x for x in xs}
    def find(self, x):
        if self.p[x] != x:
            self.p[x] = self.find(self.p[x])
        return self.p[x]
    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[b] = a


def main():
    started = time.monotonic()
    rings = presentations()
    by_label = {R.label: R for R in rings}
    print("PRINCIPAL RESIDUE-F2 LENGTH-SIX CHAIN-RING CLASSIFICATION")
    print("RAW_PRESENTATIONS 32 = equal-char 1 + e1 16 + e2 8 + e3 4 + e4 2 + e5 1")
    for R in rings:
        validate_ring(R)
    print(f"[64-element arithmetic gates] 32/32 PASS ({time.monotonic()-started:.2f}s)")

    iso = {}
    dsu = DSU(by_label)
    for A in rings:
        for B in rings:
            ws = isomorphism_witnesses(A, B)
            iso[(A.label, B.label)] = ws
            if ws:
                dsu.union(A.label, B.label)
    for A in rings:
        for B in rings:
            assert bool(iso[(A.label, B.label)]) == bool(iso[(B.label, A.label)])

    # Every one of the 16 uniformizers of every target has one and only one
    # induced binary carry presentation.  The independently validated maps
    # above must partition those uniformizers without omission or overlap.
    for B in rings:
        seen = []
        for A in rings:
            seen.extend((A.label, q) for q in iso[(A.label, B.label)])
        assert len(seen) == 16
        assert {q for _, q in seen} == set(B.uniformizers())
        assert len({q for _, q in seen}) == 16
    print("[uniformizer relation partition] every target's 16 uniformizers occur exactly once")

    groups = {}
    for label in by_label:
        groups.setdefault(dsu.find(label), []).append(label)
    orbits = sorted((sorted(v) for v in groups.values()),
                    key=lambda orbit: (99 if by_label[orbit[0]].e is None
                                       else by_label[orbit[0]].e, orbit))

    print(f"[uniformizer audit] checked 32^2 presentation pairs and all 16 target uniformizers")
    print(f"ISOMORPHISM_CLASSES {len(orbits)}")
    print("orbit_id\te\tcharacteristic\trepresentative\tcoordinate_presentations\taut_uniformizers")
    for i, orbit in enumerate(orbits, start=1):
        rep = by_label[orbit[0]]
        aut = len(iso[(rep.label, rep.label)])
        e = "inf" if rep.e is None else str(rep.e)
        print(f"C{i:02d}\t{e}\t{rep.characteristic()}\t{rep.label}\t"
              f"{','.join(orbit)}\t{aut}")

    # Each equivalence class must be a complete clique of witnessed maps;
    # different classes must have none.  This guards against DSU hiding a
    # non-transitive implementation error.
    orbit_of = {x: i for i, orbit in enumerate(orbits) for x in orbit}
    for A in rings:
        for B in rings:
            assert bool(iso[(A.label, B.label)]) == (orbit_of[A.label] == orbit_of[B.label])

    print(f"DONE principal_length6_chain_classification_evidence_map_20260710 "
          f"({time.monotonic()-started:.2f}s)")


if __name__ == "__main__":
    main()
