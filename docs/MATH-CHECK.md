# Math check: Sendov's Lemma 4.1 (plan step 1)

Date: 2026-10-14. Scope: the general lower bound in Sendov's classification of Blumenthal's α_N.
Sources read in full:
- B. Sendov, *Minimax of the angles in a plane configuration of points*, Acta Math. Hungar. 69 (1995) 27–46. This is the English paper; Lemma 4.1 is on pp. 37–40.
- B. Sendov, *Обязательные конфигурации точек на плоскости*, Fundam. Prikl. Mat. 1 (1995), no. 2, 491–516. This is the Russian exposition; the same lemma is Lemma 4.12 on pp. 510–512. The source used was EMIS, `journals/FPM/ps/95/952/95210.zip`.
- P. Erdős, G. Szekeres, *On some extremum problems in elementary geometry* (1960/61), §§3–4.

All scripts referred to below are in [`research/numerics/`](../research/numerics/).

## Summary

1. **The gap is real, and it is the whole general case.** Sendov proves Lemma 4.1 for s = 2 and s = 3 (both arguments are correct). For s = 4 he only *asserts* where the maximum is attained. For s ≥ 5 he writes "let the lemma be proved for s − 1", gives no inductive step, and again asserts the extremal profile. The Russian exposition (Lemma 4.12) has the identical text, so neither version contains a fuller proof.
2. **Lemma 4.1 is equivalent to the general lower bound.** §3 restates the lemma as an inequality (W) about *arbitrary* finite point sets Q, with s = |Q|. The lower bound follows from (W) at once. Conversely, Sendov's own constructions show that the lower bound implies (W). So "the induction on s" is the entire general lower bound, not a technical step. Sendov's s ≤ 3 cases cover only sets with at most 3 points.
3. **Sendov's stated s = 4 maxima are false.** Explicit 4-point configurations beat them (§4.3):
   - weight 10 > 9 for n = 3, u = 15/2, which reproduces PR #300's "t = 15/4" remark;
   - weight 20 > 18 for n = 4, u = 9.99.
   Neither example exceeds the lemma's final bound 2^n + 2^(n−2). The *proof* of Lemma 4.1 is wrong; its *statement* has survived every test.
4. **No counterexample to the statement exists in the searched range.** Annealing over n = 2…5, u just below 2n+1 and 2n+2, and s = 3…10 always peaks *exactly* at Sendov's bound and never above it (§5). There are many equality configurations with s up to 9.
5. **Two natural proof routes cannot work as uniform arguments** (§6.3), shown by explicit, exactly checked examples:
   - induction by deleting one point;
   - Erdős–Szekeres "Kraft" counting over arc colourings.

   Any proof must use global structure or the counterexample hypothesis itself.
6. **How much geometry is needed** (§6.4–6.5):
   - (W) still holds numerically for abstract direction matrices in which every triple is a consistent triangle.
   - The first band holds even when only per-point angle bounds are imposed.
   - The first band reduces to a single-split statement (the "Cover Lemma") that held in every test, with a wide margin.

**Verdict.** Sendov's classification is very probably true. Its general lower bound (non-dyadic N ≥ 17) is unproved in the literature. A complete formalization of JSP-000404 needs a new proof of inequality (W). §6 collects partial results and structure that a proof could start from.

## 1. Notation

Fix u > 0. Put λ = 2π/u and α = (1 − 2/u)π = π − λ. Let n = ⌊u/2⌋ ≥ 2 and

    B(u) = 2^n             if 2n ≤ u < 2n+1,
    B(u) = 2^n + 2^(n−2)   if 2n+1 ≤ u < 2n+2.

For a finite Q ⊂ ℝ² and q ∈ Q, let D(q) ⊂ ℝP¹ = ℝ/πℤ be the set of directions of the lines qr, r ∈ Q∖{q}. These |Q|−1 directions cut the circle ℝP¹ (length π) into gaps θ_1, …, θ_{|Q|−1}, with Σθ_j = π. Define

    κ_u(q) = Σ_j max(0, ⌊θ_j/λ⌋ − 1),        F_u(Q) = Σ_{q∈Q} 2^{κ_u(q)}.

Equivalently, κ_u(q) is the largest size of a set S ⊂ ℝP¹ that is λ-separated and at distance ≥ λ from D(q). In Sendov's notation, φ_{i,j} = θ_j/π and κ_u = k'(i) of Lemma 3.7, i.e. ([uφ/2] − 1)_+ summed.

Sendov's Theorem 4.1, lower-bound half, in this notation:

> **(L)** If every angle of a finite set P ⊂ ℝ² is at most (1 − 2/u)π, then |P| ≤ B(u).

To see that this is the lower-bound half: if N > 2^n and some N-point set P has max angle A(P) < (1 − 2/(2n+1))π, put u = 2π/(π − A(P)) < 2n+1. Then (L) and the monotonicity of B give N ≤ B(u) ≤ 2^n, a contradiction. The second band is handled the same way.

## 2. Sendov's reduction: what is sound

Checked line by line:
- Theorem 2.1 / Lemma 2.3 (GC angles approximate real angles).
- Lemma 3.1 (Erdős–Szekeres even-partition bound).
- Lemma 3.3 (λ-sectors give an even partition).
- Lemmas 3.4–3.8 and Theorem 3.1.

These are all correct. The one subtlety is that Lemma 3.7's floor makes "≤ α" (not "< α") work: a gap of exactly 2λ admits one internal line at distance exactly λ from both ends. Their joint content is:

- **Upper count (Lemmas 3.3, 3.7).** In a GC V with top-level centres Q and GA(V) ≤ α, the cluster at q has at most 2^{κ_u(q)} points. So |P| ≤ F_u(Q).
- **Realisation (Lemmas 3.6, 3.8).** If Q has all angles ≤ α, then putting at each q a perfect cluster with κ_u(q) internal lines gives a GC with exactly F_u(Q) points and GA ≤ α. By Theorem 2.1, real configurations then have F_u(Q) points and all angles ≤ α + ε.

The existence of extreme GCs (§5 of the paper) is **not** needed for the lower bound.

## 3. The inequality behind Lemma 4.1

> **(W)** Let u ≥ 4. Let Q ⊂ ℝ² be finite with |Q| ≥ 2, and let every angle ∠xyz (x, y, z ∈ Q distinct) be ≤ (1 − 2/u)π. Then F_u(Q) ≤ B(u).

**Proposition 1.** (W) ⟹ (L). *Proof.* Apply (W) to Q = P and use |P| ≤ Σ_q 2^{κ_u(q)}. ∎

**Proposition 2.** (L) for all u ⟹ (W). *Proof.* Suppose F_u(Q) > B(u). The realisation in §2 gives, for every ε > 0, real configurations with F_u(Q) ≥ B(u) + 1 points and all angles ≤ (1 − 2/u)π + ε. B(u) is constant on [2n, 2n+1) and on [2n+1, 2n+2), so choosing u' slightly above u with B(u') = B(u) contradicts (L) at u'. ∎

**Lemma 4.1 is exactly (W) for |Q| = s.** By Lemma 3.4, a perfect GC with s top-level centres has |P| = Σ 2^{k(i)}. By Lemma 3.7, k(i) ≤ κ_u(o_i). So Lemma 4.1 for s centres is (W) for the s-point set of centres. Conversely, the realisation turns any s-point Q into such a GC.

So (L) ⟺ (W) ⟺ "Lemma 4.1 for every s". Sendov's induction parameter s is the number of points of an arbitrary configuration, which is why the missing step cannot be a small patch.

## 4. Sendov's proof of Lemma 4.1, case by case

Write t = u/2 = n + δ, with 0 ≤ δ < 1.

### 4.1 s = 2: correct

Both points have a single gap π. So κ = ⌊t⌋ − 1 = n − 1 and F = 2^n.

### 4.2 s = 3: correct (small misprint)

Let the triangle have angles πa_1, πa_2, πa_3. At vertex i the gaps are πa_i and π(1 − a_i).
- **κ(i) ≤ n − 1 always.** κ(i) = n − 1 iff ta_i < 2 and t(1 − a_i) ≥ n, i.e. a_i ≤ δ/t. Otherwise κ(i) ≤ n − 2.
- **The max-angle condition** is a_3 ≤ 1 − 1/t, i.e. a_1 + a_2 ≥ 1/t, and similarly for the other pairs.
- **Two vertices of weight 2^{n−1}** therefore force 2δ/t ≥ 1/t, i.e. δ ≥ 1/2. Hence F ≤ 2^{n−1} + 2·2^{n−2} = 2^n when δ < 1/2.
- **When δ ≥ 1/2 and κ(1) = κ(2) = n−1:** the third vertex has t(a_1 + a_2) ∈ [1, 2δ] ⊂ [1, 2), so it contributes only through t(1 − a_1 − a_2) ≤ t − 1. That gives κ(3) ≤ n − 2 and F ≤ 2^n + 2^{n−2}.
- **All three cannot be small,** since 3δ/t < 1.

This matches the paper. The paper's sentence "from (4.13) it follows that φ_{1,1} = 1/(2n+1)" should read "<".

### 4.3 s = 4: the asserted maxima are false

Sendov's claims for s = 4:
- **c.1** (δ < 1/2): the maximum of |P| is attained at k = (n−1, n−2, n−3, n−3).
- **c.2** (δ ≥ 1/2): the maximum is attained at k = (n−1, n−2, n−2, n−3), giving |P| = 2^n + 2^{n−3}.

No argument is given for either. Case c.2 is false. Two verified counterexamples:

| n | u | Q | κ_u | F_u(Q) | Sendov's s = 4 claim |
|---|---|---|---|---|---|
| 3 | 15/2 | (−1,0), (1,0), (0, 1/2), (0, 51/100) | (2,2,0,0) | **10** | 9 |
| 4 | 9.99 | [`sendov_s4_cfg_u10.txt`](../research/numerics/sendov_s4_cfg_u10.txt) | (1,3,1,3) | **20** | 18 |

Each example takes Sendov's 3-centre extremal triangle and splits the apex centre into two nearby points. The first row is checked in 50-digit arithmetic by [`sendov_s4_counterexample.py`](../research/numerics/sendov_s4_counterexample.py): max angle 0.7048π ≤ 0.7333π, and every gap/λ is at least 0.0095 from an integer. The second row is checked by `verify_weight.py`. Both reach 2^n + 2^{n−2}, the lemma's final bound, which they do not exceed.

PR #300's remark "t = 15/4 gives weight 10 > 9" is this same phenomenon. Splitting the apex further shows that the asserted extremal profiles for s ≥ 5 (case s.2) are also not the maximisers.

### 4.4 s ≥ 5: no argument

"Let the lemma be proved for s − 1, then for s we have two cases …" Only the claimed extremal profiles follow, with no use of the hypothesis for s − 1. Nothing here can be repaired locally. By §3, this step *is* the general lower bound.

## 5. Numerical evidence for (W)

[`weight_search.c`](../research/numerics/weight_search.c) runs simulated annealing over s-point configurations. It maximises F_u, with the max-angle condition imposed as a penalty, using 12 restarts × 3·10⁵ steps per cell. u is set to 10⁻⁷ below 2n+1 and below 2n+2. Raw output: [`weight_search_grid.txt`](../research/numerics/weight_search_grid.txt).

| n | u ↑ 2n+1: bound 2^n | best F for s = 3…10 | u ↑ 2n+2: bound 2^n+2^{n−2} | best F for s = 3…10 |
|---|---|---|---|---|
| 2 | 4 | 4, 4, — for s ≥ 5 | 5 | 5, 5, 5, — for s ≥ 6 |
| 3 | 8 | 8 for s = 3…8; — for s ≥ 9 | 10 | 10 for s = 3…8; 9 at s = 9; — at s = 10 |
| 4 | 16 | 16 for s = 3…8; 14 at s = 9; — at s = 10 | 20 | 20 for s = 3…9; 18 at s = 10 |
| 5 | 32 | 32 for s = 3…9; 22 at s = 10 | 40 | 40 for s = 3…9; 36 at s = 10 |

- "—" means the search found no s-point set with the required max angle. For s > B(u) that is exactly what (L) predicts; for n = 2 it matches α_5 = 3π/5 and α_6 = 2π/3.
- Values below the bound at large s are search limits, not structure.
- The bound is reached by many different weight profiles, e.g. (2,2,2,2,2,3,2,2,2) for n = 5, s = 9. The few equality configurations we inspected are all coarsenings of Sendov's 2- or 3-centre configuration: some centres are split into nearby points whose weights add up to the original.
- No run ever exceeded the bound.

## 6. Material for a proof attempt

### 6.1 Proven structural facts

All for Q as in (W).

- **(a) Every point has a gap ≥ λ, and κ_u(q) ≤ n − m(q).** Here m(q) is the number of gaps of D(q) of length ≥ λ.
  - Why a gap ≥ λ exists: let V(q) ⊂ S¹ be the unit vectors from q to the other points. A vector of V(q) and a vector of −V(q) are always ≥ λ apart. Going round S¹, the labels V / −V therefore change across free arcs of length ≥ λ, and these arcs project to gaps of D(q) of length ≥ λ.
  - The bound: κ = Σ_{θ_j ≥ λ}(⌊θ_j/λ⌋ − 1) ≤ ⌊π/λ⌋ − m = n − m.
- **(b) Hull vertices vs interior points.** Call a gap a *sign-change gap* if the labels V / −V differ on its two sides.
  - A hull vertex has exactly one sign-change gap, since V(q) lies in an open half-plane.
  - An interior point has at least three, because the label sequence is antisymmetric and so a half-turn has an odd number of changes.
  - Every sign-change gap is ≥ λ, so interior points have m(q) ≥ 3 and κ ≤ n − 3.
  - A hull vertex may still have m(q) ≥ 2. For example, the apex of the 3-centre configuration has gaps λ and π − λ.
- **(c) Few hull vertices.** Each exterior angle is ≥ λ, so the number of hull vertices is ≤ ⌊u⌋. In particular it is ≤ 2n when u < 2n+1.
- **(d) Weight n − 1 forces a narrow view.** κ(q) = n − 1 iff q sees all of Q∖{q} inside a cone whose line-directions span an arc of length ≤ π − nλ (< λ/2 when u < 2n+1).
- **(e) Individual cover bound.** Let c*(q) be the least number of half-open λ-arcs covering D(q). Then c*(q) + κ(q) ≤ n. *Proof:* cover each maximal run between gaps ≥ λ, of span ℓ_i, by ⌊ℓ_i/λ⌋ + 1 arcs, and sum the floors.
- **(f) A merge criterion.** Suppose ∠yxt ≥ λ for every t ∈ Q∖{x, y}, i.e. both gaps of D(x) next to the line xy are ≥ λ. Then deleting y raises κ(x) by at least 1. If moreover κ(y) ≤ κ(x), then F(Q) ≤ F(Q∖{y}).
- **(g) Kraft connection.** Erdős–Szekeres Lemma 4 says Σ_p 2^{ν(p)} ≤ 2^n for an even partition of K_N into n parts, where ν(p) counts the parts in which p is isolated. (W) has exactly this shape.
  - Colour each pair by the λ-arc containing its direction. Each colour class is bipartite, with a canonical left/right side.
  - Kraft for Q itself reads Σ_q 2^{−d(q)} ≤ 1 for every partition of ℝP¹ into half-open arcs of width ≤ λ, where d(q) is the number of arcs meeting D(q).
  - Applying Kraft to the realised GC of §2 gives nothing more, because the factor 2^{κ(q)} cancels.

### 6.2 Base cases

Proven:
- (W) holds for |Q| ≤ 3 (§4).
- (W) holds when u = 2n is an even integer, i.e. λ = π/n, by the plain Erdős–Szekeres covering argument.
  - n arcs of width λ tile ℝP¹.
  - Each internal direction of a realised cluster lies in its own arc, and that arc misses D(q). So ν(q) ≥ κ(q).
  - Kraft then gives F ≤ 2^n.

### 6.3 Routes that cannot work uniformly

Each example below satisfies (W), so none is a counterexample. Each shows that a particular induction or certificate cannot be applied to *every* configuration. A proof along these lines must therefore use the assumption F(Q) > B(u) itself.

- **Delete-one-point induction.** One would delete y when Δ(y) = Σ_{r≠y}(2^{κ_{Q∖y}(r)} − 2^{κ_Q(r)}) ≥ 2^{κ(y)}. There are configurations where every y fails ("irreducible").
  - Example: [`irreducible_cfg_u8_s6.txt`](../research/numerics/irreducible_cfg_u8_s6.txt), u = 8 − 10⁻⁷, κ = (1,0,0,1,0,0), F = 8. Checked by `deletion_check.py`.
  - A minimal counterexample to (W) would have to be irreducible, so this route needs a separate bound for irreducible sets.
- **Kraft certificates from arc colourings.** To get F ≤ 2^n one would like a partition of ℝP¹ into n+1 half-open arcs of width ≤ λ with Σ_q 2^{ν(q)} ≥ 2F(Q), where ν(q) is the number of arcs missing D(q). Exhaustive enumeration over colourings ([`kraft_exact.py`](../research/numerics/kraft_exact.py)) shows that none exists for:
  - [`kraft_cfg_u7_s6.txt`](../research/numerics/kraft_cfg_u7_s6.txt): u = 6.9999, F = 6, best Σ2^ν = 10 < 12;
  - [`kraft_cfg_u9_s7.txt`](../research/numerics/kraft_cfg_u9_s7.txt): u = 8.9999, F = 8, best 15 < 16.

  These sets are far below the bound, so the method could still work by contradiction for sets with F > B(u). But it cannot be a per-configuration certificate.
- **Kraft in the second band.** Take a colouring with n+1 arcs and call q *bad* if D(q) meets n+1−κ(q) arcs.
  - Kraft gives F_good + F_bad/2 ≤ 2^n.
  - Such a colouring therefore certifies F ≤ 2^n + 2^{n−2} only if F_bad ≤ 2^{n−1}.
  - The 3-centre extremal configuration meets this with equality, so there is no slack.
- **Sendov's own route** (order κ(1) ≥ … ≥ κ(s), guess the extremal profile) is refuted by §4.3.

### 6.4 How much geometry does a proof need?

(W) mentions only the line directions at each point. So it can be posed for abstract *direction matrices*: assign to each ordered pair a vector direction v(p,q) ∈ S¹ with v(q,p) = v(p,q) + π, and require every angle at every point to be ≤ (1 − 2/u)π. Two relaxations of planar point sets were tested with [`direction_models.c`](../research/numerics/direction_models.c):

| model | first band (u < 2n+1) | second band (2n+1 ≤ u < 2n+2) |
|---|---|---|
| **pseudo-configurations**: every triple is a consistent triangle, i.e. its three angles sum to π | bound holds (n = 3…5, s ≤ 8) | bound holds (n = 3…5, s ≤ 8) |
| **local model**: per-point angle bound only | bound holds (n = 2…5, s ≤ 8) | **fails**: F = 12 > 10 at n = 3, s = 5 ([`local_model_cex_u8_s5.json`](../research/numerics/local_model_cex_u8_s5.json), checked by `verify_direction_matrix.py`) |

Consequences for a proof:
- **Second band.** It must use triangle angle sums, as Sendov's s = 3 argument does. It apparently need not use full planar realisability.
- **First band** (α_N for 2^n < N ≤ 2^n + 2^{n−2}). It looks purely combinatorial: per-point angle bounds plus the Erdős–Szekeres colouring.
- **n = 2 in the local model.** Every point has one sign change, so it is "hull-like". The normal arcs N_p = {x : ⟨x, v⟩ ≤ 0 for all v ∈ V(p)} are interior-disjoint, since v(p,q) = −v(q,p). Each has length ≥ λ, and 2π < 5λ (resp. 6λ) gives at most 4 (resp. 5) points.

### 6.5 A reduction of the first band: the Cover Lemma

For θ ∈ S¹, let C(θ) be the set of points with no vector in [θ, θ+λ). Then:
- C(θ) ∪ C(θ+π) = P;
- every pair inside one cell has its line outside [θ, θ+λ) mod π.

> **Cover Lemma (conjecture, u < 2n+1).** There is a θ such that the lines inside C(θ) and the lines inside C(θ+π) can each be covered by n − 1 half-open λ-arcs.

By the Erdős–Szekeres bound each cell then has ≤ 2^{n−1} points, so |P| ≤ 2^n: the first band of (L) follows. In words: one global λ-colour, followed by n − 1 colours chosen *separately in each half*, always suffices. A single global colouring does not (§6.3).

A cell needs n arcs exactly when it contains a "spanning chain". That is n pairwise λ-separated lines filling the complementary arc of length (n−1)λ + w, with slack only w < λ/2.

Evidence ([`cover_lemma.py`](../research/numerics/cover_lemma.py)):
- **Local model:** no failure in about 400 configurations, n = 2…5. These were GC-expanded, up to 24 points.
- **Real point sets:** no failure on realisations of the extremal configurations for n = 3, 4.
- **Size of the bad set.** The set of θ whose cell C(θ) needs n arcs never exceeded 32% of the circle. Below 50% already guarantees a good θ: if B is the bad set, then B and B − π cannot cover the circle.
- **Typical structure.** Bad θ form windows of length ≤ w, one for each spanning chain whose gap contains [θ, θ+λ).

**A proven sufficient condition.** Suppose some arc J ⊂ ℝP¹ of length < λ − w meets the line set D(p) of every point p. Then the Cover Lemma holds. Proof:
- Take I ⊇ J of length λ. Every point has a vector in I⁺ or I⁻, so every point lies in exactly one cell.
- Let p, q be in the same cell, with vectors x_p, x_q lying over J. The angle bound at q excludes v(p,q) from (x_q − λ, x_q + λ). The angle bound at p excludes v(p,q) from the antipodal arc around x_p.
- Hence the line pq avoids (x_p − λ, x_p + λ) ∩ (x_q − λ, x_q + λ), which contains an open arc of length 2λ − |J| > λ + w.
- So each cell's lines lie in a closed arc of length < π − λ − w = (n−1)λ, which n − 1 half-open λ-arcs cover.

The extremal two-cluster configurations satisfy this condition, with J the connecting direction. General configurations need not.

A proof of the Cover Lemma, for example a bound |bad set| < π, would settle the first band for every n.

### 6.6 Directions that look viable

- **Minimal counterexample plus rigidity.** Normalise the diameter of a counterexample Q with minimal s. Consider the closed set of configurations whose κ-profile dominates that of Q.
  - Suppose two points can be pushed together inside this set. All the GC conditions are closed, so the limit is a valid GC with s − 1 top-level centres and at least F(Q) points. Lemma 3.8 then contradicts minimality. Otherwise Q is rigid, i.e. many angles equal α and many gaps are exact multiples of λ. That rigidity could then be analysed.
- **Adaptive Erdős–Szekeres splitting.** Split by one λ-arc chosen from the configuration, which turns the circle problem into two arc problems. Then show the two halves cannot both be large. The pigeonhole alignment in Erdős–Szekeres Theorem 2 is the precedent.
- **Computer-assisted proofs for fixed n.** A minimal counterexample has s ≤ B(u) + 1. For n = 3 this recovers α_9…α_16, which are known (Sendov [8]; SAT in PR #647). n = 4 (α_17…α_32) would be new, but this does not give all N.

## 7. Consequences for this repository's plan

- **Step 5 (general lower bound) is blocked on new mathematics.** Formalizing Sendov's argument is impossible as it stands. The intermediate claims a formalization would need are false (§4.3) and the induction step is absent.
- **Steps 2–4 are unaffected and can proceed:**
  - definitions and statement;
  - upper bounds for all N (Sendov's constructions);
  - dyadic lower bounds (Erdős–Szekeres).
- **The reduction (W) ⟹ (L) is cheap to formalize** (Proposition 1). A future proof of (W) would plug in without the generalized-configuration machinery. Only the motivation (Proposition 2) uses it.
- **A useful honest milestone:** prove (W) in Lean for |Q| ≤ 3. Also state (W) as the single open hypothesis behind the full theorem, and prove `(W) → SendovAnswer`. Then the full result depends on exactly one clearly stated lemma.

## 8. Reproducing

```
cd research/numerics
cc -O2 -o weight_search weight_search.c -lm
./weight_search 7.9999999 4 300000 12 11          # u s iters restarts seed
python3 -m pip install mpmath numpy scipy
python3 sendov_s4_counterexample.py              # §4.3, n = 3
python3 verify_weight.py 9.99 sendov_s4_cfg_u10.txt
python3 deletion_check.py 7.9999999 irreducible_cfg_u8_s6.txt
python3 kraft_exact.py 6.9999 kraft_cfg_u7_s6.txt
```
