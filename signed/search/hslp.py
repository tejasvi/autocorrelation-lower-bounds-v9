# Direct highspy solves for the generator LPs (same LPs as scipy.optimize.linprog(method='highs') with A_ub x <= b_ub):
# presolve off, no scipy wrapper overhead, optional warm start from the previous basis of the same shape.
import numpy as np, highspy
_INF = highspy.kHighsInf
_BASIS = {}
def solve_ub(c, A, b, lo, hi, key=None):
    """min c.x s.t. A x <= b, lo <= x <= hi (None -> infinite). Returns (status_ok, x, fun)."""
    A = np.asarray(A, float); nr, nc = A.shape
    h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("presolve", "off")
    lp = highspy.HighsLp(); lp.num_col_ = nc; lp.num_row_ = nr
    lp.col_cost_ = np.asarray(c, float)
    lp.col_lower_ = np.array([-_INF if v is None else v for v in lo], float)
    lp.col_upper_ = np.array([_INF if v is None else v for v in hi], float)
    lp.row_lower_ = np.full(nr, -_INF); lp.row_upper_ = np.asarray(b, float)
    nzr, nzc = np.nonzero(A.T)            # column-major order of nonzeros
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.concatenate([[0], np.cumsum(np.bincount(nzr, minlength=nc))]).astype(np.int32)
    lp.a_matrix_.index_ = nzc.astype(np.int32); lp.a_matrix_.value_ = A.T[nzr, nzc]
    h.passModel(lp)
    if key is not None and key in _BASIS and _BASIS[key][0] == (nr, nc):
        h.setBasis(_BASIS[key][1])
    h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal: return False, None, None
    if key is not None: _BASIS[key] = ((nr, nc), h.getBasis())
    x = np.array(h.getSolution().col_value)
    return True, x, float(np.dot(lp.col_cost_, x))
