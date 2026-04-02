# ==========================================================================
# parallel_search.py
#
# Multiprocessing brute-force search for integer solutions (n, x, y) to:
#
#   y^2 = x^3 + (36n+27)^2 * x^2
#             + 243*(4n+3)^3 * x
#             + (46656n^4 + 139968n^3 + 157464n^2 + 78713n + 14748)
#
# Search parameters (edit below):
#   N_LOW, N_HIGH : range of n values
#   X_LOW, X_HIGH : range of x values tested for each n
#
# The x range should cover where solutions are likely to exist.
# From analysis of known solutions, all x-values for |n| <= 200 lie in
# [-562, 144840].  For safety we use a wider margin.
# For |n| in [201, 10000], solutions should have |x| <= ~1,500,000
# (heuristic based on u/n^2 ≈ 432 observation and spread in known solutions).
#
# Typical throughput: ~2M checks/second per core.
# With 8 cores and default parameters (2x10^4 n-values, 3x10^6 x-values):
#   total checks = 6 × 10^10  (~8 hours per core, ~1 hour with 8 cores)
#
# Usage:
#   python3 parallel_search.py              # uses all available cores
#   python3 parallel_search.py --workers 4  # use 4 cores
#   python3 parallel_search.py --n_low -500 --n_high 500  # custom n range
# ==========================================================================

import math
import time
import sys
import os
import multiprocessing as mp
import argparse

# ---------------------------------------------------------------------------
# Coefficient functions (pure Python, no dependencies)
# ---------------------------------------------------------------------------

def a6(n):
    return 46656*n**4 + 139968*n**3 + 157464*n**2 + 78713*n + 14748

# ---------------------------------------------------------------------------
# Known solutions for cross-checking
# ---------------------------------------------------------------------------
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
# Worker function: search one chunk of n values
# ---------------------------------------------------------------------------

def _worker_init():
    """Worker initializer: ignore SIGINT so the pool survives Ctrl-C in the
    parent shell.  The main process handles graceful shutdown."""
    import signal as _sig
    _sig.signal(_sig.SIGINT, _sig.SIG_IGN)


def search_chunk(args):
    n_start, n_end, x_low, x_high, worker_id = args
    results = []
    t_start = time.time()

    for n_val in range(n_start, n_end + 1):
        # Pre-compute coefficients for this n
        _a2 = (36*n_val + 27)**2
        _a4 = 243*(4*n_val + 3)**3
        _a6 = a6(n_val)

        for x_val in range(x_low, x_high + 1):
            r = x_val**3 + _a2*x_val**2 + _a4*x_val + _a6
            if r < 0:
                continue
            y_val = math.isqrt(r)
            if y_val * y_val == r:
                results.append((n_val, x_val, int(y_val)))
                if y_val > 0:
                    results.append((n_val, x_val, -int(y_val)))

    elapsed = time.time() - t_start
    return results, worker_id, n_start, n_end, elapsed


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    # Ignore SIGINT so this long-running background search survives accidental
    # Ctrl-C in a shell sharing this terminal session.  SIGTERM is intentional
    # (e.g., `kill PID`) and should still terminate the process normally.
    import signal
    signal.signal(signal.SIGINT, signal.SIG_IGN)

    parser = argparse.ArgumentParser(description="Parallel brute-force integer point search")
    parser.add_argument("--n_low",   type=int, default=-10000, help="Lower bound for n (default: -10000)")
    parser.add_argument("--n_high",  type=int, default=10000,  help="Upper bound for n (default: 10000)")
    parser.add_argument("--x_low",   type=int, default=-1500000, help="Lower bound for x (default: -1500000)")
    parser.add_argument("--x_high",  type=int, default=1500000,  help="Upper bound for x (default: 1500000)")
    parser.add_argument("--workers", type=int, default=None,   help="Number of parallel workers (default: cpu_count)")
    parser.add_argument("--chunk",   type=int, default=None,   help="n-values per worker chunk (default: auto)")
    args = parser.parse_args()

    N_LOW  = args.n_low
    N_HIGH = args.n_high
    X_LOW  = args.x_low
    X_HIGH = args.x_high
    num_workers = args.workers or os.cpu_count() or 4
    n_total = N_HIGH - N_LOW + 1
    chunk_size = args.chunk or max(1, math.ceil(n_total / (num_workers * 4)))

    print("=" * 72)
    print("  Parallel brute-force integer-point search")
    print(f"  n in [{N_LOW}, {N_HIGH}]  ({n_total} values)")
    print(f"  x in [{X_LOW}, {X_HIGH}]  ({X_HIGH - X_LOW + 1} values per n)")
    total_checks = n_total * (X_HIGH - X_LOW + 1)
    print(f"  Total checks: {total_checks:.3e}")
    print(f"  Workers: {num_workers},  chunk size: {chunk_size} n-values per chunk")
    print("=" * 72)
    print()

    # Verify known solutions
    print("--- Verifying known solutions ---")
    for (nv, xv, yv) in sorted(KNOWN, key=lambda t: t[2] > 0, reverse=True):
        if yv < 0:
            continue
        a2v = (36*nv + 27)**2
        a4v = 243*(4*nv + 3)**3
        a6v = a6(nv)
        r = xv**3 + a2v*xv**2 + a4v*xv + a6v
        ok = (r == yv**2)
        print(f"  n={nv:>8}, x={xv:>10}, y={yv:>22}:  {'OK' if ok else 'WRONG!'}")
    print()

    # Split n range into chunks
    chunks = []
    n = N_LOW
    wid = 0
    while n <= N_HIGH:
        n_end = min(n + chunk_size - 1, N_HIGH)
        chunks.append((n, n_end, X_LOW, X_HIGH, wid))
        n = n_end + 1
        wid += 1
    print(f"  Total chunks: {len(chunks)}\n")

    # Run in parallel
    all_solutions = []
    t_global_start = time.time()
    chunks_done = 0

    with mp.Pool(processes=num_workers, initializer=_worker_init) as pool:
        for results, worker_id, n_s, n_e, elapsed in pool.imap_unordered(search_chunk, chunks):
            chunks_done += 1
            for sol in results:
                if sol not in all_solutions:
                    all_solutions.append(sol)
                    marker = "(known)" if sol in KNOWN or (sol[0], sol[1], -sol[2]) in KNOWN else "*** NEW ***"
                    print(f"  SOLUTION: n={sol[0]:>8}, x={sol[1]:>12}, y={sol[2]:>22}  {marker}", flush=True)

            elapsed_total = time.time() - t_global_start
            pct = 100.0 * chunks_done / len(chunks)
            eta = (elapsed_total / max(chunks_done, 1)) * (len(chunks) - chunks_done)
            if chunks_done % max(1, len(chunks)//20) == 0 or chunks_done == len(chunks):
                print(f"  Progress: {pct:5.1f}%  chunks={chunks_done}/{len(chunks)}"
                      f"  elapsed={elapsed_total:.0f}s  ETA={eta:.0f}s", flush=True)

    t_total = time.time() - t_global_start
    all_solutions = sorted(set(all_solutions))

    print()
    print("=" * 72)
    print(f"  Search complete in {t_total:.1f}s")
    print(f"  Solutions found: {len(all_solutions)}")
    print()
    print("  All solutions:")
    for sol in all_solutions:
        marker = "(known)" if sol in KNOWN or (sol[0], sol[1], -sol[2]) in KNOWN else "*** NEW ***"
        print(f"    n={sol[0]:>8}, x={sol[1]:>12}, y={sol[2]:>22}  {marker}")
    print("=" * 72)


if __name__ == "__main__":
    main()
