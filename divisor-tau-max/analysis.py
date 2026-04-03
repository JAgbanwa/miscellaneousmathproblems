"""
Divisor-function maximum problem
=================================
Question: Is there some n > 24 such that
    max_{m < n} (m + τ(m)) ≤ n + 2,
where τ(m) counts the number of positive divisors of m?

This script:
  1. Computes τ(m) for all m ≤ N via a linear sieve.
  2. Computes the running maximum M(n) = max_{m < n}(m + τ(m)).
  3. Identifies ALL n ≤ N satisfying the condition M(n) ≤ n + 2.
  4. Tracks record-setters (m such that m + τ(m) > k + τ(k) for all k < m).
  5. Produces a table of close misses (M(n) − n − 2 small and positive) for n > 24.
"""

import sys

# ── Parameters ────────────────────────────────────────────────────────────────
N = 10_000_000          # search bound
CLOSE_MISS_THRESHOLD = 4  # print rows where M(n) - (n+2) ≤ this for n > 24

# ── Step 1: sieve for τ ───────────────────────────────────────────────────────
print(f"Computing τ(m) for m = 1 … {N:,}  (additive sieve) …")
tau = [0] * (N + 1)
for d in range(1, N + 1):
    for m in range(d, N + 1, d):
        tau[m] += 1
print("  done.\n")

# ── Step 2: running maximum and condition check ───────────────────────────────
running_max = 0          # M(n) = max_{m < n}(m + τ(m))
good_n      = []         # all n with M(n) ≤ n + 2
record_m    = []         # record-setters: (m, τ(m), m+τ(m))
prev_record = 0

print("n values satisfying M(n) ≤ n+2:")
for n in range(1, N + 1):
    # Update running maximum: incorporate m = n-1
    if n >= 2:
        val = (n - 1) + tau[n - 1]
        if val > running_max:
            running_max = val
            record_m.append((n - 1, tau[n - 1], val))

    if running_max <= n + 2:
        good_n.append(n)
        suffix = "" if n <= 24 else "  ← n > 24 !"
        print(f"  n = {n:>5}:  M(n) = {running_max:>6},  n+2 = {n+2:>6}{suffix}")

print()
print(f"Complete list: {good_n}\n")
print(f"Largest n with M(n) ≤ n+2:  {max(good_n) if good_n else 'none'}")
print(f"Any n > 24 found: {any(x > 24 for x in good_n)}\n")

# ── Step 3: close misses for n > 24 ──────────────────────────────────────────
print(f"Close misses for n > 24  (M(n) − (n+2) ≤ {CLOSE_MISS_THRESHOLD}):")
print(f"{'n':>10}  {'M(n)':>10}  {'n+2':>8}  {'gap':>6}  record set by m")
running_max = 0
last_record_m = 0
for n in range(1, N + 1):
    if n >= 2:
        val = (n - 1) + tau[n - 1]
        if val > running_max:
            running_max = val
            last_record_m = n - 1
    if n > 24:
        gap = running_max - (n + 2)
        if 0 < gap <= CLOSE_MISS_THRESHOLD:
            print(f"{n:>10}  {running_max:>10}  {n+2:>8}  {gap:>6}  "
                  f"m={last_record_m}, τ={tau[last_record_m]}, "
                  f"m+τ={last_record_m+tau[last_record_m]}")

print()

# ── Step 4: minimum gap ───────────────────────────────────────────────────────
running_max = 0
min_gap, min_gap_n = float('inf'), -1
for n in range(1, N + 1):
    if n >= 2:
        val = (n - 1) + tau[n - 1]
        if val > running_max:
            running_max = val
    if n > 24:
        gap = running_max - (n + 2)
        if gap < min_gap:
            min_gap, min_gap_n = gap, n

print(f"Minimum of M(n)−(n+2) for n > 24 in [25, {N:,}]:  "
      f"{min_gap}  (first achieved at n = {min_gap_n})")
print()

# ── Step 5: record-setter sequence ───────────────────────────────────────────
print("Record-setter sequence for m > 20 (m such that m+τ(m) exceeds all previous):")
print(f"{'m':>10}  {'τ(m)':>6}  {'m+τ(m)':>10}")
for (m, t, v) in record_m:
    if m > 20:
        print(f"{m:>10}  {t:>6}  {v:>10}")
    if m > 200:
        print("  … (truncated at m=200)")
        break
