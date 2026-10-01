# Erdős Problem 190 in Lean 4

A self-contained Lean 4 / Mathlib proof of the answer to
[Erdős Problem 190](https://www.erdosproblems.com/190): $H(k)^{1/k}/k \to \infty$, where $H(k)$
is the least $N$ such that every finite colouring of $\{1, \dots, N\}$ has a monochromatic or
rainbow $k$-term arithmetic progression.

## Results

- `Erdos190.canonicalAP_lower_bound` (unconditional): for every $C$ and all large $k$, every $N$
  with the canonical property satisfies $N > (Ck)^k$.
- `Erdos190.erdos_190`: $H(k)^{1/k}/k \to \infty$, assuming that $H(k)$ exists for every $k$
  (Erdős–Graham, via Szemerédi's theorem, which is not in Mathlib).

## Method

A colouring with $k - 1$ colours has no rainbow $k$-AP, so it is enough to bound the van der
Waerden number $W(k-1, k)$ from below. The proof combines a union bound with a
Blankenship–Cummings–Taranchuk type product step over a Bertrand prime, giving
$W(k-1, k) \ge (k/8)^{(9/8 - o(1))k}$.

## Build

```bash
lake exe cache get
lake build
lake env lean Check.lean   # prints the axioms used
```

Lean `v4.33.1`, Mathlib `v4.33.1`. The CI workflow builds the project and fails if `sorryAx`
appears among the axioms.
