"""Independent exact replay of the 6.3(2) rational certificate.

The eta enclosure is recomputed by forward differences rather than the
published checker's nested binomial sum. No floating-point decisions occur.
"""
import hashlib
import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parent
source = ROOT / 'provenance/beukers_cone_h4_certificate.json'
c = json.loads(source.read_text())
V = [[F(x) for x in row] for row in c['basis_Q']]

def convolution(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out

factor = [F(0)]*8 + [F((-1)**i * comb(4, i)) for i in range(5)]
P = [convolution(v, factor) for v in V]
assert len(V) == 4 and all(len(v) == 16 for v in V)
assert all(V[i][12+j] == (i == j) for i in range(4) for j in range(4))
assert all(len(p) == 28 for p in P)

def constraint(p, m, nu):
    return sum(x*(F(factorial(nu), (r+m+1)**(nu+1)) -
                  F(factorial(5-nu), (r+m+1)**(6-nu))) for r, x in enumerate(p))

assert all(constraint(p, m, nu) == 0 for p in P for m in range(4) for nu in range(3))
t = F(c['t'])
p = [y-t*x for x,y in zip(P[0], P[1])]
q = [y-t*x for x,y in zip(V[0], V[1])]
assert p != [F(0)]*len(p)
assert p + [F(0)] == [F(x) for x in c['P_coefficients']]
H = {s: [sum(F(1,j**s) for j in range(1,r+1)) for r in range(28)] for s in (6,7)}
A = sum(x*x for x in p)
B = -sum(x*x*H[7][r] for r,x in enumerate(p))
# Count unordered off-diagonal pairs exactly once, then double them.
B += 2*sum(p[r]*p[s]*(H[6][r]-H[6][s])/F(6*(r-s))
           for r in range(28) for s in range(r))
assert A > 0 and A == F(c['slope']) and B == F(c['constant'])

# Euler transform through finite differences, independent of stored sums.
differences = [F(1, (j+1)**7) for j in range(240)]
eta = F(0)
for k in range(240):
    eta += differences[0]/2**(k+1)
    differences = [x-y for x,y in zip(differences, differences[1:])]
lo = F(64,63)*eta
hi = lo+F(64,63*2**240)
assert lo == F(c['zeta_lower']) and hi == F(c['zeta_upper'])
lower, upper = A*lo+B, A*hi+B
assert -F(12115,10**52) < lower <= upper < -F(12114,10**52)

norms = [sum(abs(x) for x in v) for v in V]
assert all(n > 0 for n in norms)
normalized_V = [[x/n for x in v] for v,n in zip(V,norms)]
assert all(sum(abs(x) for x in v) == 1 for v in normalized_V)
negative_coordinates = [-t*norms[0], norms[1], F(0), F(0)]
assert all(sum(negative_coordinates[i]*normalized_V[i][j] for i in range(4)) == q[j]
           for j in range(16))

receipt = {
    'scope': 'EXACT_RATIONAL_REPLAY_AND_MATHEMATICAL_ANALYTIC_ENCLOSURE;NOT_LEAN_KERNEL',
    'source_commit': '86ca99a23d65cde4880a9005a49076c43e7bc968',
    'certificate_git_blob': '855f5f517fccafc45ff689cb872580b881ae0447',
    'published_checker_git_blob': '84f1fac82da4147824098add6b84ccef410c8d0d',
    'certificate_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'independent_checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'h': 4, 'K': 28, 'm0': 8, 'four_independent_basis_polynomials': True,
    'basis_degree_bound': 27, 'exact_basis_constraints_verified': 48,
    'normalized_coefficient_l1_norm': '1',
    'negative_direction_in_normalized_basis_verified': True,
    'eta_enclosure_terms': 240,
    'zeta_interval_width': str(hi-lo),
    'quadratic_strict_lower_bound': str(-F(12115,10**52)),
    'quadratic_strict_upper_bound': str(-F(12114,10**52)),
    'result': 'PASS'
}
(ROOT / 'independent_review_receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
