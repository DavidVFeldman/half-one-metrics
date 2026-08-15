import numpy as np, sys
from lp import build
from scipy.optimize import linprog

def classify(x, tol=1e-6):
    v = x
    if np.all((np.abs(v) < tol) | (np.abs(v-1) < tol)): return "partition"
    if np.all((np.abs(v-0.5) < tol) | (np.abs(v-1) < tol)): return "half-one"
    if np.all((np.abs(v) < tol)|(np.abs(v-0.5) < tol)|(np.abs(v-1) < tol)): return "den2-mixed"
    return "other"

trials = int(sys.argv[1]); ns=[int(v) for v in sys.argv[2].split(",")]
rng = np.random.default_rng(7)
print(f"{'n':>3} {'partition':>9} {'half-one':>9} {'den2mix':>8} {'other':>7}")
for n in ns:
    E,m,A = build(n); b=np.zeros(A.shape[0])
    c_ = {"partition":0,"half-one":0,"den2-mixed":0,"other":0}
    for _ in range(trials):
        r = linprog(-rng.normal(size=m), A_ub=A, b_ub=b, bounds=[(0,1)]*m, method="highs")
        c_[classify(r.x)] += 1
    print(f"{n:>3} {c_['partition']/trials:>9.3f} {c_['half-one']/trials:>9.3f} {c_['den2-mixed']/trials:>8.3f} {c_['other']/trials:>7.3f}")
    sys.stdout.flush()
