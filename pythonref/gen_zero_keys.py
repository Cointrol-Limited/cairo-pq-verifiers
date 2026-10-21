#!/usr/bin/env python3
"""Genuine Falcon-512 keys whose packed public key has chosen all-zero halves or slots.

The public key is h = g / f, so h's NTT vanishes wherever g's does. For a target set Z of
NTT positions (for example the high half of key slot j, positions 18j+9..18j+17) this
script takes a Gaussian g0 and adds a short correction d on a random support S of about
48 coefficients with NTT(g0 + d) = 0 on Z: d is a closest vector (LLL + Babai) in the
lattice {x on S : A x = -NTT(g0)|Z mod q}. A Gaussian f and falcon.py's NTRU solver
complete the key; every signature is checked against the reference verifier.

Cases: zero high half of slots 0, 13, 27; zero low half of slot 5; whole slot 9 zero;
the last slot (8 coefficients) zero; high halves of slots 2 and 20 together.
Writes tests/zk_fixtures.cairo + bench_zk.cairo (expected: valid).
"""
import random
import sys
from fractions import Fraction  # noqa: F401  (exactness checks below use ints)
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_edge_fixtures as ge  # noqa: E402

gm, ref = ge.gm, ge.ref
from ntrugen import gen_poly, ntru_solve, gs_norm  # noqa: E402
from ntt import ntt as fntt  # noqa: E402

Q, N = ref.Q, ref.N


def unit_ntts():
    cols = []
    for k in range(N):
        e = [0] * N
        e[k] = 1
        cols.append(ref.ntt(e))
    return cols  # cols[k][i] = NTT(e_k)[i]


def inv_mod_matrix(A):
    """Inverse of a square matrix mod Q, or None."""
    n = len(A)
    M = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] % Q), None)
        if p is None:
            return None
        M[c], M[p] = M[p], M[c]
        iv = pow(M[c][c], Q - 2, Q)
        M[c] = [x * iv % Q for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]
                M[r] = [(a - f * b) % Q for a, b in zip(M[r], M[c])]
    return [row[n:] for row in M]


def pivots(A):
    """Indices of m independent columns of the m x k matrix A mod Q, or None."""
    M = [row[:] for row in A]
    m, k = len(M), len(M[0])
    piv, r = [], 0
    for c in range(k):
        p = next((i for i in range(r, m) if M[i][c] % Q), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        iv = pow(M[r][c], Q - 2, Q)
        M[r] = [x * iv % Q for x in M[r]]
        for i in range(m):
            if i != r and M[i][c]:
                fct = M[i][c]
                M[i] = [(a - fct * b) % Q for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == m:
            return piv
    return None


def lll(B, delta=0.99):
    B = [row[:] for row in B]
    n = len(B)

    def dot(a, b):
        return sum(x * y for x, y in zip(a, b))

    def gso():
        Bs, mu, nrm = [], [[0.0] * n for _ in range(n)], []
        for i in range(n):
            v = [float(x) for x in B[i]]
            for j in range(i):
                mu[i][j] = dot(B[i], Bs[j]) / nrm[j]
                v = [a - mu[i][j] * b for a, b in zip(v, Bs[j])]
            Bs.append(v)
            nrm.append(dot(v, v))
        return Bs, mu, nrm

    Bs, mu, nrm = gso()
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            r = round(mu[k][j])
            if r:
                B[k] = [a - r * b for a, b in zip(B[k], B[j])]
                Bs, mu, nrm = gso() if n < 8 else (Bs, mu, nrm)
                for t in range(j + 1):
                    mu[k][t] -= r * (mu[j][t] if t < j else 1)
        if nrm[k] >= (delta - mu[k][k - 1] ** 2) * nrm[k - 1]:
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            Bs, mu, nrm = gso()
            k = max(k - 1, 1)
    return B


def babai(B, t):
    """Lattice vector of the LLL-reduced basis B close to t (nearest plane)."""
    n = len(B)
    Bs, nrm = [], []
    for i in range(n):
        v = [float(x) for x in B[i]]
        for j in range(i):
            m = sum(a * b for a, b in zip(B[i], Bs[j])) / nrm[j]
            v = [a - m * b for a, b in zip(v, Bs[j])]
        Bs.append(v)
        nrm.append(sum(x * x for x in v))
    b = [float(x) for x in t]
    v = [0] * len(t)
    for i in range(n - 1, -1, -1):
        c = round(sum(x * y for x, y in zip(b, Bs[i])) / nrm[i])
        if c:
            b = [x - c * y for x, y in zip(b, B[i])]
            v = [x + c * y for x, y in zip(v, B[i])]
    return v


def zero_g(Z, cols, ksup=48, tries=50):
    m = len(Z)
    for _ in range(tries):
        g0 = gen_poly(N)
        S = random.sample(range(N), ksup)
        piv = pivots([[cols[s][z] for s in S] for z in Z])
        if piv is None:
            continue
        S = [S[i] for i in piv] + [S[i] for i in range(ksup) if i not in piv]
        A = [[cols[s][z] for s in S] for z in Z]
        A1inv = inv_mod_matrix([row[:m] for row in A])
        if A1inv is None:
            continue
        y = [(-sum(cols[k][z] * g0[k] for k in range(N))) % Q for z in Z]
        # particular solution on the first m support coords
        part = [sum(A1inv[i][j] * y[j] for j in range(m)) % Q for i in range(m)] + [0] * (ksup - m)
        basis = []
        for i in range(m):
            row = [0] * ksup
            row[i] = Q
            basis.append(row)
        for j in range(m, ksup):
            col = [A[i][j] for i in range(m)]
            x1 = [(-sum(A1inv[i][t] * col[t] for t in range(m))) % Q for i in range(m)]
            row = x1 + [0] * (ksup - m)
            row[j] = 1
            basis.append(row)
        R = lll(basis)
        d = [a - b for a, b in zip(part, babai(R, part))]
        g = g0[:]
        for s, x in zip(S, d):
            g[s] += x
        gn = ref.ntt([c % Q for c in g])
        assert all(gn[z] == 0 for z in Z), "correction failed"
        return g, sum(x * x for x in d)
    raise SystemExit("no invertible support")


def make_key(Z, cols):
    while True:
        g, dn = zero_g(Z, cols)
        f = gen_poly(N)
        if any(x == 0 for x in fntt(f)):
            continue
        if gs_norm(f, g, Q) > (1.17 ** 2) * Q * 1.5:
            continue
        try:
            F, G = ntru_solve(f, g)
        except ValueError:
            continue
        return [f, g, [int(c) for c in F], [int(c) for c in G]], dn


def main():
    cols = unit_ntts()
    cases = {
        "hi0": list(range(9, 18)), "hi13": list(range(18 * 13 + 9, 18 * 13 + 18)),
        "hi27": list(range(18 * 27 + 9, 18 * 27 + 18)), "lo5": list(range(90, 99)),
        "slot9": list(range(162, 180)), "last": list(range(504, 512)),
        "hi2_20": list(range(45, 54)) + list(range(369, 378)),
    }
    scheme = gm.fpy.Falcon(512)
    vectors = []
    for name, Z in cases.items():
        polys, dn = make_key(Z, cols)
        sk, _ = scheme.keygen(polys=polys)
        f, g = polys[0], polys[1]
        h = gm.div_zq(g, f)
        hn = ref.ntt(h)
        assert all(hn[z] == 0 for z in Z)
        pk = gm.pack_512(hn)
        for rep in range(2):
            message = random.randrange(ref.FELT_PRIME)
            salt = bytes(random.randrange(256) for _ in range(40))
            point, _ = ref.hash_to_point(message, salt)
            *_, B0_fft, T_fft = sk
            while True:
                s = scheme.__sample_preimage__(B0_fft, T_fft, point)
                if sum(c * c for c in s[0]) + sum(c * c for c in s[1]) <= ref.SIG_BOUND:
                    break
            s1 = [c % Q for c in s[1]]
            hint = gm.mul_zq(s1, h)
            sig = gm.pack_512(s1) + [int.from_bytes(salt[:20], "little"),
                                     int.from_bytes(salt[20:], "little")] + gm.pack_512(hint)
            v = ref.verify(message, pk, sig)
            assert v.valid, (name, v)
            vectors.append({"message": message, "public_key": pk, "signature": sig, "valid": True,
                            "kind": f"zero-key {name}", "stream": (v.blocks, v.norm)})
            print(name, rep, "corr^2", dn, "blocks", v.blocks, "norm", v.norm,
                  "zero felts", [i for i, x in enumerate(pk) if x < 1 << 128], flush=True)
    ge.write_cairo("zk", vectors)


if __name__ == "__main__":
    main()
