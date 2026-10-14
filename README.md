# JSP-000404: Blumenthal's problem (Erdős #504) in Lean 4

**Goal:** a complete, original Lean 4 / Mathlib formalization that determines α_N for every N. This would win the Lean slot for [JSP-000404](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000404).

**Problem.** α_N is the supremum of α ∈ [0, π] such that every set of N points in the plane contains three distinct points x, y, z with ∠xyz ≥ α. The task is to determine α_N.

**Claimed answer (Sendov 1995).** For N ≥ 5 and 2^{n-1} < N ≤ 2^n:
- α_N = π(1 − 2/(2n−1)) when N ≤ 2^{n−1} + 2^{n−3};
- α_N = π(1 − 1/n) otherwise.

The small cases are α_3 = π/3 and α_4 = π/2. Note that erdosproblems.com/504 has a typo: it prints 1/(2n−1).

## Status of the slot (audited 2026-10-14)
- **No valid Lean formalization exists.**
  - The only open on-topic PR, #2804, defines α as the formula itself, so it proves a tautology.
  - Earlier PRs (#42, #100, #300, #647) were partial and closed.
- **The mathematical risk** is Sendov 1995, Lemma 4.1 (the general lower bound). Its case s ≥ 4 and the induction step are *asserted without proof*, and PR #300 claims some weight profiles exceed the asserted bound. If the gap is real, someone has to supply a new rigorous proof before any formalization can be complete. See `AUDIT.md`.

## Plan
1. **Math check (first).**
   - Reconstruct Sendov's generalized-configuration argument.
   - Test PR #300's claimed counterexample weight profiles.
   - Decide whether the lower bound is true as stated and find a rigorous proof. Brute-force checks help here: exact values are known for N ≤ 16 (SAT certificate in #647).
2. **Lean definitions and statement.** Define `alpha N` as the honest supremum over `Finset (EuclideanSpace ℝ (Fin 2))` using `EuclideanGeometry.angle`, and state the full theorem.
3. **Upper bounds (constructions) for all N.** These are the Erdős–Szekeres clustered configurations plus Sendov's three-centre construction.
4. **Dyadic lower bounds.** These follow from the Erdős–Szekeres / Szekeres direction-colouring argument.
5. **General lower bound.** This is the hard part and depends on step 1.
6. Assemble, build cleanly, check axioms, then submit a PR to TheJustinSunPrize/awards.

## Sources
- B. Sendov, *Minimax of the angles in a plane configuration of points*, Acta Math. Hungar. 69 (1995) 27–46. Open copy: https://real-j.mtak.hu/7467/1/ActaMathHung_69.pdf. Russian version: mathnet.ru (fpm81).
- P. Erdős and G. Szekeres, *On some extremum problems in elementary geometry* (1960/61): https://www.renyi.hu/~p_erdos/1960-09.pdf
- G. Szekeres, *On an extremum problem in the plane*, Amer. J. Math. 63 (1941), https://doi.org/10.2307/2371290
- https://www.erdosproblems.com/504
