#!/usr/bin/env python3
# ==========================================================================
# sage_subprocess_search.py
#
# Rigorous integer-point search using SageMath's integral_points().
# Each curve is computed in a *fresh subprocess* with a hard OS timeout
# (subprocess.run timeout), so SageMath C-extension code cannot block it.
#
# For each n in [N_LOW, N_HIGH] the script builds:
#
#   E_n : y^2 = x^3 + (36n+27)^2 * x^2
#                   + 243*(4n+3)^3 * x
#                   + (46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748)
#
# and asks SageMath for ALL integral points (rigorous, proof=False).
#
# Usage:
#   python3 sage_subprocess_search.py --n_low -200 --n_high 200
#   python3 sage_subprocess_search.py --n_low -1000 --n_high 1000 --timeout 180
#   python3 sage_subprocess_search.py --n_low -200 --n_high 200 --workers 4
#
# Options:
#   --n_low    INT   start of n range  (default -200)
#   --n_high   INT   end of n range    (default  200)
#   --timeout  INT   seconds per curve (default  120)
#   --workers  INT   parallel SageMath instances (default 4)
#                    More than 4 is rarely faster due to SageMath startup cost.
#   --out      PATH  output file       (default /tmp/sage_subprocess_<n>.txt)
# ==========================================================================

import subprocess
import sys
import os
import time
import argparse
import multiprocessing as mp

SAGE = "/usr/local/bin/sage"

KNOWN = {
    (-1,      18,          167),
    (-1,      18,         -167),
    (94,     -562,        17722),
    (94,     -562,       -17722),
    (-110,    646,         40812),
    (-110,    646,        -40812),
    (-64,     144840,      333523318),
    (-64,     144840,     -333523318),
    (147498, -449511,  2312387148693),
    (147498, -449511, -2312387148693),
}

# ---------------------------------------------------------------------------
# The SageMath one-liner for a single curve
# ---------------------------------------------------------------------------
SAGE_ONE_LINER = """
import sys
n = {n}
a2 = (36*n + 27)^2
a4 = 243*(4*n + 3)^3
a6 = 46656*n^4 + 139968*n^3 + 157464*n^2 + 78713*n + 14748
try:
    E = EllipticCurve([0, a2, 0, a4, a6])
    pts = E.integral_points(both_signs=True)
    for P in pts:
        print("PT", int(P[0]), int(P[1]))
    print("DONE", len(pts))
except Exception as e:
    print("ERROR", str(e))
"""

def a6_coeff(n):
    return 46656*n**4 + 139968*n**3 + 157464*n**2 + 78713*n + 14748

def run_one_curve(args):
    """Run SageMath integral_points for a single n value.  Returns a dict."""
    n, timeout = args
    code = SAGE_ONE_LINER.format(n=n)
    t0 = time.time()
    try:
        result = subprocess.run(
            [SAGE, "--nodotsage", "-c", code],
            capture_output=True, text=True,
            timeout=timeout
        )
        elapsed = time.time() - t0
        stdout = result.stdout.strip()
        lines = stdout.splitlines()
        pts = []
        status = "ok"
        for line in lines:
            parts = line.split()
            if parts and parts[0] == "PT" and len(parts) == 3:
                pts.append((n, int(parts[1]), int(parts[2])))
            elif parts and parts[0] == "DONE":
                pass
            elif parts and parts[0] == "ERROR":
                status = "error:" + " ".join(parts[1:])
        return {"n": n, "status": status, "pts": pts, "elapsed": elapsed}
    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        return {"n": n, "status": "timeout", "pts": [], "elapsed": elapsed}
    except Exception as e:
        elapsed = time.time() - t0
        return {"n": n, "status": f"error:{e}", "pts": [], "elapsed": elapsed}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n_low",   type=int, default=-200)
    parser.add_argument("--n_high",  type=int, default=200)
    parser.add_argument("--timeout", type=int, default=120,
                        help="seconds per curve (default 120)")
    parser.add_argument("--workers", type=int, default=4,
                        help="parallel SageMath instances (default 4)")
    parser.add_argument("--out",     type=str, default="",
                        help="output file path (default auto)")
    args = parser.parse_args()

    out_path = args.out or f"/tmp/sage_subprocess_{args.n_low}_{args.n_high}.txt"

    n_values = list(range(args.n_low, args.n_high + 1))
    total = len(n_values)

    print("=" * 70)
    print(f"  SageMath integral_points() via subprocess")
    print(f"  n in [{args.n_low}, {args.n_high}]  ({total} curves)")
    print(f"  Per-curve timeout: {args.timeout}s  |  Workers: {args.workers}")
    print(f"  Output: {out_path}")
    print("=" * 70)
    sys.stdout.flush()

    all_solutions = []
    timeout_count = 0
    error_count = 0
    t_total = time.time()

    with open(out_path, "w") as fout:
        def log(msg):
            print(msg)
            fout.write(msg + "\n")
            fout.flush()

        log(f"n in [{args.n_low}, {args.n_high}], per-curve timeout={args.timeout}s, workers={args.workers}")
        log("=" * 70)

        work = [(n, args.timeout) for n in n_values]

        with mp.Pool(processes=args.workers) as pool:
            for i, res in enumerate(pool.imap(run_one_curve, work, chunksize=1)):
                n = res["n"]
                elapsed = res["elapsed"]
                status = res["status"]
                pts = res["pts"]

                if status == "timeout":
                    timeout_count += 1
                    msg = f"  n={n:>8},  TIMEOUT (>{args.timeout}s)"
                    log(msg)
                elif status.startswith("error"):
                    error_count += 1
                    msg = f"  n={n:>8},  {status}"
                    log(msg)
                elif pts:
                    for (nv, xv, yv) in pts:
                        all_solutions.append((nv, xv, yv))
                        marker = "(known)" if (nv, xv, yv) in KNOWN or (nv, xv, -yv) in KNOWN else "*** NEW ***"
                        msg = f"  SOLUTION: n={nv:>8}, x={xv:>12}, y={yv:>22}  [t={elapsed:.1f}s] {marker}"
                        log(msg)
                else:
                    # No solutions, no error — print every 20 curves
                    if (i + 1) % 20 == 0:
                        done = i + 1
                        elapsed_total = time.time() - t_total
                        pct = 100 * done / total
                        eta = (elapsed_total / done) * (total - done) if done > 0 else 0
                        msg = (f"  Progress: {pct:5.1f}%  n={n:>8},  t_curve={elapsed:.1f}s,"
                               f"  elapsed={elapsed_total:.0f}s,  ETA={eta:.0f}s")
                        log(msg)

        # Final summary
        elapsed_total = time.time() - t_total
        log("")
        log("=" * 70)
        log(f"  Search complete in {elapsed_total:.1f}s")
        log(f"  Solutions found: {len(all_solutions)}")
        log(f"  Timed-out curves: {timeout_count}")
        log(f"  Errors: {error_count}")
        log("")
        log("  All solutions:")
        for sol in sorted(set(all_solutions)):
            nv, xv, yv = sol
            marker = "(known)" if (nv, xv, yv) in KNOWN or (nv, xv, -yv) in KNOWN else "*** NEW ***"
            log(f"    n={nv:>8}, x={xv:>12}, y={yv:>22}  {marker}")
        log("=" * 70)

if __name__ == "__main__":
    main()
