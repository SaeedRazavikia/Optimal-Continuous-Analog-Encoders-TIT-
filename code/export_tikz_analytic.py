"""Export scalar coefficients and certificate summaries for native TeX figures.

The TeX files draw analytic parametric curves.  No raster/PDF figures and no
sampled encoder paths are produced here.  Optimization and experiments are
not rerun: the exponential panel reads the existing rational certificate.
Run from any directory with the Python standard library only.
"""
from fractions import Fraction
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures" / "data"


def quadratic(M):
    t = M / 2
    b = 2 / (1 + 2 * t / (math.sqrt(t * t + 2) + t))
    return math.sqrt(b * (2 - b)), b, -1.0


def quartic(M):
    lo, hi = 0.0, 1 / 3
    for _ in range(100):
        rho = (lo + hi) / 2
        if 8 * rho**2 * (1 + rho) * (1 + 3 * rho) < M**2 * (1 - 3 * rho):
            lo = rho
        else:
            hi = rho
    rho = (lo + hi) / 2
    d = 1 + 2 * rho + 9 * rho**2
    a = math.sqrt(8 * rho / d)
    b = 2 / ((1 + rho) * math.sqrt(d))
    c = -(1 + 2 * rho + 3 * rho**2) / ((1 + rho) * math.sqrt(d))
    return rho, a, b, c


def write_table(path, header, rows):
    text = " ".join(header) + "\n"
    text += "".join(" ".join(format(v, ".17g") for v in row) + "\n" for row in rows)
    path.write_text(text)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rho, aq, bq, cq = quartic(4)
    cases = [(2, 2, 0, *quadratic(2)), (4, 4, rho, aq, bq, cq),
             (2, 1, 0, *quadratic(1))]
    write_table(OUT / "optimal_coefficients.dat", ["p", "M", "rho", "rootrho", "a", "b", "c", "score"],
                [(p, M, r, math.sqrt(r), a, b, c, 1 / (M*M/(a*a) + 1/(b*b)))
                 for p, M, r, a, b, c in cases])

    cert = json.loads((ROOT / "results" / "certified_synthesis.json").read_text())
    pw = cert["primal_witness"]
    scale = Fraction(pw["verification"]["scale"])
    H = [[float(Fraction(v) * scale) for v in row] for row in pw["H"]]
    # G = L^T L, with L upper triangular.  c solves L^T c = ell.
    l11 = math.sqrt(H[1][1])
    l12 = H[1][2] / l11
    l22 = math.sqrt(H[2][2] - l12*l12)
    c1 = H[0][1] / l11
    c2 = (H[0][2] - l12*c1) / l22
    write_table(OUT / "certified_coefficients.dat", ["c1", "c2", "l11", "l12", "l22"],
                [(c1, c2, l11, l12, l22)])
    upper = Fraction(cert["certified_bounds"]["upper"])
    rows = []
    for row in cert["convergence_table"]:
        lower = Fraction(row["lower"])
        gap_pct = float(100 * (upper - lower) / upper)
        rows.append((row["grid_points"], gap_pct, float(lower), float(upper)))
    write_table(OUT / "certified_convergence.dat", ["n", "gap_pct", "lower", "upper"], rows)
    print("Exported three small data tables for native analytic/certificate figures.")


if __name__ == "__main__":
    main()
