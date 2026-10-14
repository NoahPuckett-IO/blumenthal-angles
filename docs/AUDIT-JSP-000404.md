# JSP-000404 (Blumenthal's problem = Erdős #504): Lean audit

Audit date: 2026-10-14. Method: `jsp/awards/skills/lean-verify/SKILL.md` (static review plus one Lean audit bridge compiled locally). Read-only. No PRs or issues were touched.

## Conclusion

> **Overall verdict: Verification failed (statement mismatch) for every competing Lean submission. Slot status: OPEN. No valid formalization exists.**
>
> None of the 9 PRs that cite JSP-000404 contains a complete Lean proof of the original problem. The only open PR whose repository has any relation to the actual problem is Yi-111-a #2804, pinned at `Yi-111-a/jsp-000404-blumenthal-sendov@f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061`. It **defines** `alpha N` as a piecewise closed form and then proves that `alpha N` equals that closed form. This is a definitional tautology with no geometry: no points, no angles, no supremum. On top of that, the closed form copies the erdosproblems.com typo `π(1-1/(2n-1))`, so even the hard-coded values are wrong. For example, `alpha 5 = 4π/5` (checked in Lean below), while the true value is α₅ = 3π/5.

| Required question | Judgment | Decisive evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | **No** (all submissions) | #2804: `JSP404.alpha` is defined by the answer formula (`lean/JSP404/Defs.lean:24-27`), not as Blumenthal's supremum over planar N-point sets. #2751: its body cites plby `Erdos404.lean`, which is a different Erdős problem (#404, about factorial sums) and is absent at the pinned commit anyway. The PR files are prime/arithmetic filler. The closed PRs are partial or off-topic. |
| Did the specified commit actually pass verification? | **Verification incomplete** (orchestrator build pending). Not decisive. | Statically, the 2 Lean files (~90 lines) contain no sorry, axioms, or tricks, so they would very likely build. Either way, the build is irrelevant to the verdict. |
| Does it fully solve the original problem? | **No** | #2804 proves only `alpha N = formula` for a *defined* `alpha`. It also omits N = 3, 4, and its formula is mathematically false (non-monotone; `alpha 5 > 3π/5`, the regular-pentagon bound). |
| Does it meet the Lean completeness requirements? | **Does not meet** | Confirmed statement mismatch, so no complete proof of the original catalog problem. |

Verification levels completed: static review of all submissions. One actual Lean check: the audit bridge `YiBridge.lean`, exit 0, standard axioms only. Kernel replay and the comparator were not run because they are unnecessary given the confirmed mismatch.

## 1. Original problem

Catalog entry (`jsp/awards/problems/catalog-0401-0500.md`, anchor `JSP-000404`):
- Title: "Blumenthal's problem".
- Description: "What is the largest angle that every planar set of a prescribed number of points must determine?"
- Fields: Status Solved, Lean proof No, Eligible to claim No.
- Sources: Sz41, ErSz60, Se92, Se93.

Erdős #504 (erdosproblems.com/latex/504) states the problem precisely:

> α_n = sup{ α ∈ [0, π] : for **every** A ⊂ ℝ² with |A| = n there **exist** distinct x, y, z ∈ A with ∠xyz ≥ α }. Determine α_n.

The quantifier order is: for each n, the sup over α of (∀ A with |A| = n, ∃ distinct x, y, z with ∠xyz ≥ α). For n ≤ 2 the set is empty, so the problem is meaningful for n ≥ 3. α_n is non-decreasing in n, because every (n+1)-set contains an n-subset.

**Answer in the literature.** The source is Sendov, *Minimax of the angles in a plane configuration of points*, Acta Math. Hungar. 69 (1995) 27-46. It was read from the OCR of `https://real-j.mtak.hu/7467/1/ActaMathHung_69.pdf`, saved locally under `scratchpad/agents/jsp404/src/`.

- Intro, p. 27: α(3) = π/3, α(4) = π/2, α(5) = 3π/5, α(6) = α(7) = α(8) = 2π/3, α(9) = α(10) = 5π/7, α(11) = … = α(16) = 3π/4.
- Theorem 4.1, p. 42, in Sendov's indexing:
  - α(N) = (1 − 2/(2n+1))π for 2ⁿ < N ≤ 2ⁿ + 2ⁿ⁻²;
  - α(N) = (1 − 1/(n+1))π for 2ⁿ + 2ⁿ⁻² < N ≤ 2ⁿ⁺¹.
- In erdosproblems indexing (n ↦ n−1), for 2ⁿ⁻¹ < N ≤ 2ⁿ:
  - **α_N = π(1 − 2/(2n−1))** when N ≤ 2ⁿ⁻¹ + 2ⁿ⁻³;
  - α_N = π(1 − 1/n) otherwise.
  - This holds for N ≥ 5. N = 3 and N = 4 are stated separately.

**Formula discrepancy (orchestrator observation (b)): CONFIRMED.** erdosproblems.com/504 (fetched 2026-10-14, last edited 16 Oct 2025) prints the lower band as π(1 − 1/(2n−1)). That is a typo:
- N = 5 would give 4π/5 > 3π/5, the regular-pentagon maximum angle.
- It would make α non-monotone (4π/5 at N = 5 > 2π/3 at N = 8).

Sendov's final theorem, the 5π/7 value for N = 9, 10, and Lemmas 4.2-4.3 (a = (1 − 2/u)π) all use numerator **2**. PR #42 reported the same and also says Sendov's eq. (1.1) in the intro prints numerator 1. The OCR of (1.1) is garbled, so I could not confirm that last point.

**Is α_N fully determined for all N in the literature? Claimed yes, but rigor is doubtful.** Sendov's Lemma 4.1 (pp. 37-40) carries the general lower bound, i.e. it bounds |P| for a "perfect generalized configuration".
- Cases s = 2 and s = 3 are argued.
- Case s = 4 and the induction step for s ≥ 4 only *assert* "the maximum of |P| is achieved if k(1) = n−1, k(2) = n−2, …" with no justification. I confirmed this in the OCR text.
- PR #300 (CollinYuanjieRen, closed) states that this step "is asserted without a correct proof (and is exceeded by explicit weight profiles)". It concludes that the general sharp lower bound for non-dyadic N with m ≥ 4 "appears currently unproved in the literature". I have not independently verified the claimed counterexample weight profiles, so this is **unclear**.

Which parts have independent support:
- Small cases and dyadic N = 2^k: Erdős–Szekeres.
- N = 5..10: classical, and PR #100.
- N = 11..16: PR #647, a SAT-certificate Lean proof.
- Upper constructions for all N: PR #42 and PR #300.

The general lower bound for non-dyadic N ≥ 17 currently rests on Sendov's sketchy Lemma 4.1.

## 2. Competing PRs (all of them: harvest index plus a fresh `gh pr list --search JSP-000404 --state all`)

| PR | State | Author | Repo / commit named | Verdict | Why |
| --- | --- | --- | --- | --- | --- |
| #42 | closed 2026-09-21 | superpilot69 | in-PR package `superpilot69/awards@722cb3ca` | Partial (self-declared) | Faithful definitions. Proves the upper bounds (constructions) for both corrected branches, N ≥ 5. No general lower bound. Documents the typo. |
| #100 | closed 2026-09-22 | zilan520 | `zilan520/awards@d869ab90` | Partial (self-declared) | Exact values for N = 5..10 and N = 2^n. No arbitrary N. |
| #300 | closed 2026-09-24 | CollinYuanjieRen | `CollinYuanjieRen/awards@e80d0b20` | Partial (self-declared) | Exact values for 3 ≤ n ≤ 8 and dyadic N, plus all upper bounds. General lower bound explicitly not claimed (cites the Sendov gap). |
| #647 | closed 2026-09-24 | hit1190100321 | `hit1190100321/awards@2d0c118b` | Partial (self-declared) | Eleven-point lower bound, giving exact values for N = 11..16. No arbitrary N. |
| #1774 | closed | dcdreamy-code | `dcdreamy-code/awards`, path `Erdos413.lean` | Invalid | Wrong file. Self-described as "numerical instances" proved by `decide`. Calls the problem "metric embeddings", which it is not. |
| #2751 | **open** | dcdreamy-code | body: `plby/lean-proofs@8822f7dd`, `src/latest/ErdosProblems/Erdos404.lean`. Files: `dcdreamy-code/awards@2cdb0de4`, `submissions/JSP-000404/Erdos404.lean` | **Invalid** | Wrong mapping: JSP-000404 ≠ Erdős #404, which is about p-adic valuations of factorial sums. The cited plby file does not exist at 8822f7dd (GitHub API 404; not in the local clone). The submitted file holds `Nat.Prime 2 := by decide`, `40*5+204 = 404`, and similar filler, with no geometry. |
| #2785 | closed 2026-10-07 | zjukop3 | `zjukop3/erdos404-blumenthal`, commit "" (empty) | Invalid / unverifiable | Repo deleted (API 404). No commit pinned. The body says it covers only n = 3 (equilateral triangle, 60°). |
| #2804 | **open** | Yi-111-a | `Yi-111-a/jsp-000404-blumenthal-sendov@f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061`, theorem `JSP404.sendov_minimax_angle` | **Verification failed: statement mismatch (tautology plus wrong formula)** | See §3. |
| #4684 | closed 2026-10-03 | kunjunsong-code | `kunjunsong-code/jsp-000404-lean-proof` (not pinned) | Invalid / unverifiable | Title: "CLOSED - repo creation rate limited". Repo does not exist (API 404; absent from the user's repo list). The body claims "zero Mathlib … verify by decide", which cannot formalize real angles. |

No relevant Lean source exists in the reference libraries:
- plby/lean-proofs@8822f7dd has no Erdos504 or Blumenthal/Sendov file.
- formal-conjectures has no `ErdosProblems/504.lean`.
- openai/math@adc7f124 has nothing matching 504, Blumenthal, or Sendov. The only hit is the unrelated `LaughlinFock/Sparse1504.lean`.

## 3. Statement audit: #2804 (Yi-111-a)

Target theorem, `lean/JSP404/Main.lean`:
```lean
theorem sendov_minimax_angle :
    ∀ n : ℕ, 3 ≤ n →
      (∀ N : ℕ, 2 ^ (n - 1) + 2 ^ (n - 3) < N → N ≤ 2 ^ n →
        alpha N = Real.pi * (1 - (n : ℝ)⁻¹)) ∧
      (∀ N : ℕ, 2 ^ (n - 1) < N → N ≤ 2 ^ (n - 1) + 2 ^ (n - 3) →
        alpha N = Real.pi * (1 - ((2 * n - 1 : ℕ) : ℝ)⁻¹))
```
Definition, `lean/JSP404/Defs.lean:24-27`:
```lean
noncomputable def alpha (N : ℕ) : ℝ :=
  if 2 ^ (Nat.clog 2 N - 1) + 2 ^ (Nat.clog 2 N - 3) < N
  then Real.pi * (1 - (Nat.clog 2 N : ℝ)⁻¹)
  else Real.pi * (1 - ((2 * Nat.clog 2 N - 1 : ℕ) : ℝ)⁻¹)
```
The proof unfolds `alpha`, rewrites `Nat.clog 2 N = n`, and selects the `if` branch. The docstring itself says "`alpha N` is *defined* by Sendov's (Se93) piecewise value".

| Original requirement | Lean counterpart | Correspondence | Gap |
| --- | --- | --- | --- |
| Objects: N-point sets A ⊂ ℝ² | none | **Missing** | No points, planes, or sets appear anywhere. |
| ∠xyz for distinct x, y, z ∈ A | none | **Missing** | No `EuclideanGeometry.angle`. |
| α_N := sup{α : ∀A ∃x,y,z, ∠xyz ≥ α} | `alpha N :=` closed-form formula | **Mismatch (vacuous)** | The answer is baked into the definition. The theorem is a tautology. |
| Lower band value π(1 − 2/(2n−1)) | `π(1 − 1/(2n−1))` | **Wrong** | Copies the erdosproblems typo. `alpha 5 = 4π/5 ≠ 3π/5`. |
| Upper band value π(1 − 1/n) | same | Formula matches | Still only definitional. |
| N = 3, 4 (α = π/3, π/2) | not stated (needs n ≥ 3, i.e. N ≥ 5) | **Missing** | Also, the defined `alpha 3 = 2π/3 ≠ π/3`. |
| Monotonicity of α_N (structural sanity) | violated: `alpha 8 < alpha 5` | **Contradicts the original** | Lean-checked; see below. |

Audit bridge file: ``.
- It copies `alpha` and `clog_two_eq` verbatim and proves `alpha 5 = 4π/5`, `alpha 8 = 2π/3`, `alpha 8 < alpha 5`, and `3π/5 < alpha 5`.
- Compiled with `lake env lean` in conjectures-validator (Lean v4.35.0-rc2): exit 0, about 60 s.
- Both `#print axioms` results are `[propext, Classical.choice, Quot.sound]`.
- Log: `…/agents/jsp404/YiBridge.log`.

Because Blumenthal's α is non-decreasing and α₅ ≤ 3π/5 (regular pentagon), the submitted `alpha` is provably not α_N.

## 4. Static completeness (#2804)

The repo at f7bf2cce (HEAD = f7bf2cce, single commit) has these Lean files: `lean/JSP404.lean` (imports only), `lean/JSP404/Defs.lean`, and `lean/JSP404/Main.lean`. Toolchain: `leanprover/lean4:v4.34.0`. Mathlib is the only dependency.

A whole-word grep for `sorry|admit|axiom|opaque|implemented_by|extern|native_decide|unsafe|macro|elab|skipKernelTC|set_option` under `lean/` found no matches. The proof is genuine; it is just trivial. Completeness is not the problem. The statement is.

#2751 (dcdreamy file) is trivially complete by `decide`/`norm_num`, but irrelevant to the problem.

## 5. Build & #print axioms

**Pending orchestrator build** for Yi-111-a @ f7bf2cce. The orchestrator note says the Lean files total 90 lines and the build has not run yet. A successful build would not change the verdict, because the mismatch is semantic. Only the local audit bridge above was compiled (exit 0, standard axioms).

## 6. Is this slot winnable for us?

**Slot status: open.** No submission covers the original problem. The 4 serious partial efforts (#42, #100, #300, #647) were all closed as partial. The two open PRs are a tautology and a wrong-problem filler.

**Feasibility: very hard, research-grade risk. Not recommended as a quick win.** A faithful, complete formalization would need all of the following:

1. **Definition.** `alphaN N := sSup {α ∈ [0,π] | ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = N → ∃ x y z ∈ A, distinct, ∠ x y z ≥ α}` for N ≥ 3. This is easy, and PRs #42 and #300 already wrote such definitions.
2. **Upper bounds (constructions) for every N.** Recursive clustered configurations (Erdős–Szekeres for 2ⁿ; Sendov's three-centre construction for 2ⁿ⁻¹ + 2ⁿ⁻³). Doable but nontrivial: roughly 2-4k Lean lines. PR #42 reports having this, but it is someone else's code; a claim must be our own repo.
3. **Lower bounds for every N.** Every N-point set with N > threshold has an angle ≥ value.
   - Dyadic thresholds: the Erdős–Szekeres / Szekeres argument, a few thousand lines.
   - The **general non-dyadic sharp lower bound** (e.g. N = 17..20 need ≥ π(1 − 2/9) = 7π/9; every N in 2ⁿ⁻¹ + 2ⁿ⁻³ < N needs ≥ π(1 − 1/n)) requires Sendov's generalized-configuration theory (Theorems 2.1 and 3.1, Lemmas 3.4, 3.7, 4.1, and §5 on the existence of extreme GCs). §5 alone is a compactness/limiting argument.
   - The key step, Lemma 4.1 with s ≥ 4, is **not actually proved** in the paper (verified in the OCR). An independent submitter (#300) claims the assertion as stated is false for some weight profiles.
   - So we would likely have to find a correct proof ourselves, which may be new mathematics.
   - Finite SAT-certificate methods (as in #647 for N = 11) do not scale to all N.
4. **Total.** Realistic estimate: 8-20k Lean lines, plus a substantial risk that the general lower bound requires an unpublished, novel argument. Source text available: Sendov 1995 (English PDF, 20 pp, OCR-garbled formulas; the Russian version is at mathnet.ru/eng/fpm81); Erdős–Szekeres 1960/61 at renyi.hu/~p_erdos/1960-09.pdf; Szekeres 1941 (DOI 10.2307/2371290).

Other considerations:
- The catalog says "Eligible to claim: No" because Lean proof = No, so the slot is not claimable until a verified complete Lean proof exists.
- A future complete proof also needs the mathematical status of the general lower bound to be sound. If Sendov's Lemma 4.1 is genuinely gapped, reviewers may challenge "Solved".
- Recommendation: deprioritize, unless someone first establishes (on paper) a rigorous proof of the general lower bound.

## 7. Evidence locations

- Catalog: `jsp/awards/problems/catalog-0401-0500.md`, anchor `JSP-000404`.
- Problem text: `scratchpad/ep/504.txt`, plus the live page erdosproblems.com/504 (fetched 2026-10-14).
- Sendov 1995 PDF and OCR: `scratchpad/agents/jsp404/src/sendov95.pdf`, `s.txt`. Theorem 4.1 is near OCR line 600; Lemma 4.1 is at lines 411-560.
- Yi repo: `` @ f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061.
- PR data: `jsp/harvest/data/pr_bodies.jsonl`, `jsp/harvest/data/slot_prs_full.json`, plus `gh pr view` for PR heads (#2751 head `2cdb0de4`, #2804 head `9fe20cc6`).
