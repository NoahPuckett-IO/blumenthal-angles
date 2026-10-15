# JSP-000404: Blumenthal's problem (Erdős #504) in Lean 4

A Lean 4 / Mathlib project to formalize the complete determination of α_N for every N, which is the open Lean slot [JSP-000404](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000404).

**Problem.** α_N is the supremum of α ∈ [0, π] such that every set of N points in the plane contains three distinct points x, y, z with ∠xyz ≥ α. The task is to determine α_N.

**Claimed answer (Sendov 1995).** For N ≥ 5 and 2^{n-1} < N ≤ 2^n:
- α_N = π(1 − 2/(2n−1)) when N ≤ 2^{n−1} + 2^{n−3};
- α_N = π(1 − 1/n) otherwise.

The small cases are α_3 = π/3 and α_4 = π/2. Note that erdosproblems.com/504 has a typo: it prints 1/(2n−1).

## Status of the slot (audited 2026-10-14)
- **No valid Lean formalization exists.**
  - The only open on-topic PR, #2804, defines α as the formula itself, so it proves a tautology.
  - Earlier PRs (#42, #100, #300, #647) were partial and closed.
- **The mathematical gap is real.** See [`docs/MATH-CHECK.md`](docs/MATH-CHECK.md).
  - Sendov 1995, Lemma 4.1 is correct for s ≤ 3 centres. Its s = 4 claims are false (explicit 4-point sets with weight 10 > 9 and 20 > 18). Its induction step is missing in both the English paper and the Russian exposition (FPM 1995, Lemma 4.12).
  - The lemma is *equivalent* to the general lower bound: an inequality (W) about arbitrary finite point sets. So the missing step is the whole non-dyadic lower bound.
  - Extensive numerics (n ≤ 5, up to 10 centres) never exceed Sendov's bound, so the classification is very likely true but unproved.
  - The audit of existing submissions is in [`docs/AUDIT-JSP-000404.md`](docs/AUDIT-JSP-000404.md).

## Progress

| Step | Status |
|---|---|
| 1. Check Sendov's proof | **Done.** The gap is real: Lemma 4.1 is equivalent to the whole general lower bound. Numerics never beat Sendov's bound. See [`docs/MATH-CHECK.md`](docs/MATH-CHECK.md). |
| 2. Lean definitions and target statement | **Done.** Honest `alpha N`, the full statement `SendovAnswer`, and its reduction to `CapacityBound`. |
| 3. Upper bounds (constructions for all N) | Open: Erdős–Szekeres clustered sets plus Sendov's three-centre construction. |
| 4. Dyadic lower bounds | Open: the Erdős–Szekeres / Szekeres direction-colouring argument. |
| 5. General lower bound (inequality (W)) | **Open mathematics.** No proof exists in the literature. |
| 6. Assemble and submit to the Justin Sun Prize | Pending steps 3–5. |

## Lean status

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`. Build:

```bash
lake exe cache get
```
```bash
lake build
```
```bash
lake env lean Audit.lean
```

| File | Contents |
|---|---|
| `Blumenthal/Defs.lean` | `Plane`, `AnglesLE`, `alpha N`, which is the literal supremum from erdosproblems.com/504. Interface lemmas: `le_alpha` (lower bounds), `alpha_le` and `alpha_le_of_approx` (upper bounds from configurations), `alpha_mono`, `exists_max_angle`. |
| `Blumenthal/Statement.lean` | `SendovAnswer`, the full target with the corrected constant, *stated, not assumed*. Its halves `SendovLower` and `SendovUpper`. `capacity u` and `CapacityBound`: a set with all angles ≤ (1 − 2/u)π has ≤ `capacity u` points. |
| `Blumenthal/Reduction.lean` | `capacityBound_iff_sendovLower` and `sendovAnswer_iff_capacityBound_and_upper`. The open lower-bound half is exactly `CapacityBound`. |
| `Audit.lean` | `#print axioms` for the main results. All use only `propext`, `Classical.choice`, `Quot.sound`. |

There is no `sorry` and no custom axiom. What remains:
- `SendovUpper` (step 3);
- `CapacityBound`. Its even-integer cases are step 4; its general case is the open mathematics described in `docs/MATH-CHECK.md`.

## Sources
- B. Sendov, *Minimax of the angles in a plane configuration of points*, Acta Math. Hungar. 69 (1995) 27–46. Open copy: https://real-j.mtak.hu/7467/1/ActaMathHung_69.pdf. Russian exposition: Fundam. Prikl. Mat. 1 (1995), no. 2, 491–516 (mathnet.ru fpm81; PostScript on EMIS at `journals/FPM/ps/95/952/95210.zip`).
- P. Erdős and G. Szekeres, *On some extremum problems in elementary geometry* (1960/61): https://www.renyi.hu/~p_erdos/1960-09.pdf
- G. Szekeres, *On an extremum problem in the plane*, Amer. J. Math. 63 (1941), https://doi.org/10.2307/2371290
- https://www.erdosproblems.com/504
