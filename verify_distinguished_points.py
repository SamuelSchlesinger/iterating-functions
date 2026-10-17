#!/usr/bin/env python3
"""Finite checks of the distinguished-point construction, not gate-count proofs.

For small n this samples the 2n-wise independent hash of the hashed-checkpoint
lemma, checks the size and hitting conditions, and runs the scan / lookup /
correction / period / cycle-walk phases against direct iteration.
"""

from random import Random


def irreducible(n):
    """Least irreducible polynomial of degree n over F_2, as an int bit mask."""
    for p in range(1 << n, 1 << (n + 1)):
        if p & 1 and all(poly_mod(p, q) for q in range(2, 1 << (n // 2 + 1))):
            return p
    raise ValueError(n)


def poly_mod(a, b):
    db = b.bit_length()
    while a.bit_length() >= db:
        a ^= b << (a.bit_length() - db)
    return a


def gf_mul(a, b, p, n):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> n:
            a ^= p
    return r


def hash_set(n, l, coeffs, p):
    mask = (1 << l) - 1
    members = set()
    for x in range(1 << n):
        g = 0
        for a in reversed(coeffs):  # Horner's rule
            g = gf_mul(g, x, p, n) ^ a
        if g & mask == 0:
            members.add(x)
    return members


def hits_or_repeats(f, members, length):
    for x in range(len(f)):
        seen, y = set(), x
        for _ in range(length):
            if y in members or y in seen:
                break
            seen.add(y)
            y = f[y]
        else:
            return False
    return True


def direct_power(f, x, t):
    positions, path = {}, []
    while x not in positions and len(path) <= t:
        positions[x] = len(path)
        path.append(x)
        x = f[x]
    if t < len(path):
        return path[t]
    mu = positions[x]
    return path[mu + (t - mu) % (len(path) - mu)]


def construction(f, members, n, l, t):
    """The phases of the distinguished-point theorem, evaluated on every input."""
    big_l = 1 << l
    k = 16 * n * big_l - 1
    if t < k:
        return [direct_power(f, x, t) for x in range(len(f))]
    payload = {h: direct_power(f, h, t - k) for h in members}
    residue = {lam: (t - k) % lam for lam in range(1, k + 1)}
    out = []
    for x in range(len(f)):
        u, found, d, c = x, False, 0, 0
        for i in range(k + 1):  # scan
            if not found and u in members:
                found, d, c = True, i, u
            if i < k:
                u = f[u]
        v = payload.get(c, 0) if found else 0  # lookup
        for i in range(k):  # correction
            if i >= d:
                v = f[v]
        w, lam = u, 1  # period walk from x_K
        for j in range(1, k + 1):
            w = f[w]
            if w == u:
                lam = j
                break
        r, w = residue[lam], u  # residue and cycle walk
        for i in range(k):
            if i < r:
                w = f[w]
        out.append(v if found else w)
    return out


def sample_maps(n, rng):
    size = 1 << n
    cycle = list(range(size))
    rng.shuffle(cycle)
    long_cycle = [0] * size
    for i, x in enumerate(cycle):
        long_cycle[x] = cycle[(i + 1) % size]
    mapping = [rng.randrange(size) for _ in range(size)]
    # A long tail of length size/2 into a cycle of length size/2.
    tail = [0] * size
    half = size // 2
    for i in range(size):
        tail[cycle[i]] = cycle[i + 1] if i + 1 < size else cycle[half]
    return {"single cycle": long_cycle, "random map": mapping, "long tail": tail}


def main():
    rng = Random(20261017)
    checks = 0
    for n in (6, 8, 10):
        p = irreducible(n)
        size = 1 << n
        for name, f in sample_maps(n, rng).items():
            for l in range(0, n):
                big_l = 1 << l
                length = 16 * n * big_l
                if l > 0 and length > 2 * size:
                    break  # hitting condition vacuous; size bound alone
                for tries in range(1, 50):
                    coeffs = [rng.randrange(size) for _ in range(2 * n)]
                    members = hash_set(n, l, coeffs, p)
                    if len(members) <= 2 * size // big_l and hits_or_repeats(f, members, length):
                        break
                else:
                    raise AssertionError(f"no good hash for n={n} l={l} {name}")
                for t in (0, 1, length - 2, length - 1, length + 5, 10**30 + 7, rng.randrange(10**40)):
                    expect = [direct_power(f, x, t) for x in range(size)]
                    assert construction(f, members, n, l, t) == expect, (n, l, name, t)
                    checks += 1
                print(f"n={n:2d} L={big_l:3d} {name:12s} |H|={len(members):4d} "
                      f"bound={2 * size // big_l:4d} hash tries={tries}")
    print(f"distinguished-point checks passed: {checks} fixed powers")


if __name__ == "__main__":
    main()
