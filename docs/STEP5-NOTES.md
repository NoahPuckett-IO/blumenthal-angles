# Step 5 notes: attacking the general lower bound

Status: **open in general.** The one-dimensional statement (R) of Attempt 3 is now **proved for n ≤ 3**
(by hand) and **for n = 4** (computer-assisted, one exact computation checked by two solvers); see
Attempt 4. With Attempt 3's reduction this settles the first band for N ≤ 20. (R) for n ≥ 5, and the
second band, remain open. These notes record what has been tried, so nobody repeats it.
Attempt 5: for even n the top class c = n − 1 is proved near λ = π/n, and on the whole band it is reduced to a one-window lemma (U) that is checked numerically but not proved.

Notation follows `MATH-CHECK.md`. All angles are ≤ π − λ, with λ = 2π/u. The first band is
2π/(2n+1) < λ ≤ π/n, where the target is |P| ≤ 2^n. Partition ℝP¹ into n arcs of width λ and one
short arc S of width w = π − nλ < λ/2.

## Attempt 1: Kraft averaged over rotations (fails per point)

Erdős–Szekeres Lemma 4 gives Σ_p 2^{ν_θ(p)} ≤ 2^{n+1} for any rotation θ of the n+1 arcs. Here
ν_θ(p) is the number of arcs that miss D(p). If E_θ[2^{ν_θ(p)}] ≥ 2 for every p, averaging over
θ would give |P| ≤ 2^n.

Using 2^ν ≥ 1 + ν, it would be enough to show E_θ[ν_θ(p)] ≥ 1. For a point with gaps g_j:

    E_θ[ν_θ(p)] = Σ_j [ n·(g_j − λ)_+ + (g_j − w)_+ ] / π.

This is large for points that see the rest of the set in a narrow cone. It is far below 1 for a
hull vertex whose view cone is as wide as allowed (π − λ): there is then a single gap ≈ λ, and
E ≈ (λ − w)/π. So a per-point averaging argument cannot work. Any proof has to transfer mass
from narrow-cone points to wide-cone points. This is consistent with §6.3 of `MATH-CHECK.md`:
certificates computed one configuration at a time do not exist.

## Attempt 2: merging the short arc into a neighbour (open)

Merge S with its neighbour A₁ into one class of width λ + w, which leaves n classes. The
Erdős–Szekeres code then fails to be injective only on pairs p, q joined by a "bent" chain
r → p → q in the merged class: the directions of rp and pq lie in S and in the far part of A₁,
more than λ apart. A proof along these lines needs a bound on such bent chains. The extremal
three-centre configurations contain them, so the bound would have to be sharp. Not resolved.

## Attempt 3: a one-dimensional relaxation of the first band (new; open)

### The reduction (proved on paper)

For p ∈ P let W(p) = V(p) ∪ −V(p) ⊂ S¹. Let σ_p : S¹ → {±1} be its *Voronoi sign function*:
σ_p(x) = +1 if the point of W(p) nearest to x lies in V(p), and −1 if it lies in −V(p). Then:

1. σ_p is odd: σ_p(x + π) = −σ_p(x).
2. **Every run of σ_p has length ≥ λ.** σ_p changes sign only at midpoints of sign-change gaps,
   which are ≥ λ (§6.1(a) of `MATH-CHECK.md`). A run from one such midpoint to the next therefore
   contains ≥ λ/2 on each side.
3. **For p ≠ q, σ_p = +1 and σ_q = −1 on the open arc (x − λ/2, x + λ/2), where x = v(p,q).** This holds
   because x ∈ V(p), −x ∈ V(q), and the nearest point of opposite label is ≥ λ away in both sets.

So the first band of (L) follows from a statement that involves no geometry at all, not even the
triangle condition:

> **(R)** Let (2n+1)λ > 2π. Let 𝒮 be a family of odd functions S¹ → {±1}, each with all runs of
> length ≥ λ, such that any two of them take opposite values on some open arc of length λ. Then
> |𝒮| ≤ 2^n.

(R) is equivalent to the same statement for families of finite sets V ⊂ S¹ that contain no two
vectors at angle > π − λ and satisfy V_p ∩ −V_q ≠ ∅ for p ≠ q. Each run condition forces at most n
sign changes per half-turn.

### Evidence that (R) is true

[`relaxation.py`](../research/numerics/relaxation.py) discretizes ℝP¹ into m cells and sets λ = Lπ/m.
It then computes the exact largest family:

| n | first-band discretizations (m, L) | largest family |
|---|---|---|
| 2 | (7,3), (9,4), (11,5) | 4 |
| 3 | (10,3), (13,4), (16,5), (17,5), (19,6) | 8 |
| 4 | (13,3), (17,4), (21,5) | 16 |
| 5 | (16,3), (21,4), (26,5) | 32 |

A grid (m, L) rules out counterexamples only for λ ≥ Lπ/m, so these checks leave a strip next to the
band edge unchecked. See Attempt 4.0, and Attempt 4.3 for the single grid that closes it.

**n = 5 (exact).** [`relaxation_cpsat.py`](../research/numerics/relaxation_cpsat.py) solves the same
maximum-family problem with OR-tools CP-SAT (16 workers): one AtMostOne per clique of a greedy
edge-clique cover of the incompatibility graph, maximise Σx_f, CP-SAT's own symmetry detection. It
returns OPTIMAL (objective = bound) at (16,3), (21,4), (26,5), so the largest family is exactly 2⁵ = 32:

| (m, L) | L/m | functions | largest family | wall time |
|---|---|---|---|---|
| (16,3) | 0.1875 | 448 | 32 | 134 s |
| (21,4) | 0.1905 | 854 | 32 | 192 s |
| (26,5) | 0.1923 | 1456 | 32 | 658 s |
| (27,5) | 0.1852 | 1854 | ≥ 32; upper bound 35 after 1.8 h (run then stopped), not closed | — |
| (11,2), band edge | 0.1818 | 198 | **41 > 40 = 2⁵ + 2³** | 0.2 s |

(Desktop, 16 threads, Python 3.13, ortools 9.15. Cross-checks: the same script reproduces 8 at
(10,3) and 16 at (13,3), (17,4). The independent SAT script
[`relaxation_sat.py`](../research/numerics/relaxation_sat.py) — CaDiCaL, clause per incompatible
pair, totalizer over a partition into incompatible classes, one case per symmetry orbit — reproduces
n ≤ 4 and finds 32 at (16,3), and proves 9 of its 10 orbit cases UNSAT at K = 33 there; its remaining
(unrestricted) case did not finish in ~30 min, so the n = 5 verdict rests on CP-SAT.)

Structure of the optimal families. Counting sign changes per half-turn, the optimal families found are
n = 3: 6×1, 2×3; n = 4: 8×1, 8×3; n = 5: 10×1, 20×3, 2×5. These are exactly the counts for the
Erdős–Szekeres product family {±1}ⁿ (a word ε has as many changes as the cyclic word (ε, −ε) has
alternations per half-turn: for n = 5, j and 5−j ones give 2·C(5,j) words). So at n = 5 the maximum
is attained by (a realisation of) the λ = π/n family, consistent with item 4 below: nothing beyond
inflatable families appears at the optimum.

At the band edge λ = 2π/(2n+1):
- (7,2) gives 10 = 2³ + 2, which is the second-band value.
- (9,2) gives **21 > 20 = 2⁴ + 2²**. So (R) fails in the second band, as the local model of
  `MATH-CHECK.md` §6.4 already showed. The second band needs triangle geometry; the first band
  apparently does not.

### Why the standard tools cannot prove (R)

1. **No LP or SDP bound works near the lower edge of the band.**
   - Every Erdős–Szekeres-style counting argument picks a random test set in which no two members
     can be separated, and gives each function survival probability ≥ 2^{−n}. That is a fractional
     colouring of the compatibility graph.
   - The Lovász theta function ϑ is the SDP analogue: the bound from orthogonal representations.
   - Since |𝒮| is an integer, either bound would suffice if it were below 2^n + 1. It is not:

     | (m, L) | L/m | χ_f | ϑ | ω |
     |---|---|---|---|---|
     | (9,4), n = 2 | 0.444 | 4.5 | 4.36 | 4 |
     | (10,3), n = 3 | 0.300 | **9.52** | **9.07** | 8 |
     | (13,4), n = 3 | 0.308 | **9.10** | 8.69 | 8 |
     | (16,5), n = 3 | 0.313 | 8.86 | 8.48 | 8 |

   - The bounds fall as λ grows towards π/n. Near λ = 2π/(2n+1) they exceed 2^n + 1. They cannot drop
     below it there: these bounds vary continuously with λ, and at the edge the true value is already
     2^n + 2^{n−2}.
   - The discrete families embed in the continuous problem, so this holds there too. It explains why
     Attempt 1 and the certificates in `MATH-CHECK.md` §6.3 failed.
   - **A proof must use the strict inequality λ > 2π/(2n+1) in an integral way and depend on the
     family itself.** This is how n = 2 works: arcs of length λ are packed on a circle,
     N ≤ ⌊2π/λ⌋ = 4.
2. **Fixed evaluation points do not suffice, even when chosen for the family.** This 8-member family
   at (10,3) cannot be separated by any 3 point evaluations:

   `0000001111 1111111111 1000011100 1000000000 0011110001 0001111111 1111000000 1111111000`

   It needs 4. An adaptive decision tree of depth 3 does exist for it. A 14-member family at (13,3)
   needs 5 evaluation points (`relaxation.py family`).
3. **Cutting ℝP¹ at one point fails.** Already for four half-plane functions at n = 2, every cut point
   lies inside the only long disagreement arc of some pair.
4. **Inflation fails, but only rarely.** Fix the cyclic order of all sign changes. The constraints
   (runs ≥ λ, one chosen disagreement run ≥ λ per pair) are then difference constraints. The family
   is realisable exactly for λ ≤ min 2πw/k over closed walks in the constraint graph, where k counts
   λ-constraints and w is the winding number.
   - If every walk has k ≤ 2nw, the family can be re-embedded at λ = π/n, and Erdős–Szekeres gives
     ≤ 2^n.
   - A first-band family has k < (2n+1)w on every walk. So the only obstructions are walks winding
     **w ≥ 2** times with 2nw < k < (2n+1)w.
   - In random maximal families these do occur, rarely: about 3 in 500 for n = 3, 4. Examples: the
     family in item 2, and

     `1110000111 0011110001 0111111111 0000000111 1111111100 0000111111 1111100000 1100000000`

   So a proof by inflation must handle multiply-winding walks.

5. **Induction by deleting a λ-window fails.**
   - Deleting a window of length λ from ℝP¹ (and its antipode from S¹) maps the first band for n onto
     the first band for n − 1. So it would be enough to split 𝒮 into two parts that each stay valid
     after deleting some window, possibly a different window for each part.
   - This *split lemma* fails for many families, including maximum ones. Random maximal 8-member
     families (n = 3) cannot be split this way in 13 of 69 cases at (10,3), and 13 of 34 at (13,4)
     (`relaxation.py split`).
   - The reason: deleting a window shortens the run that contains it. In particular, a function with
     n sign changes cannot survive any deletion.
   - This is the 1-D shadow of the Cover Lemma difficulty. Any recursion must transform the
     functions, not merely restrict them.

What still looks viable:
- **Adaptive decision trees.** Every family tested has an adaptive evaluation tree of depth n.
- **The winding analysis of item 4.** One would show that a family with 2^n + 1 members forces a
  closed walk with k ≥ (2n+1)·(winding around S¹). The extremal configurations at the band edge
  have exactly such a walk: 2n+1 tight constraints going once around S¹.

For each fixed n there are only finitely many combinatorial types: 2^n + 1 functions, at most n sign
changes each. So (R) for fixed n is a finite (very large) computation. This does not give all n.
Attempt 4.3 makes this precise: one grid decides it.

## Attempt 4: change-count classes and a finite-grid reduction (2026-10-20)

**Results.**
- (R) holds for **n ≤ 3** for every λ in the band (§4.2, by hand).
- (R) holds for **n = 4** for every λ ∈ (2π/9, π/4] (§4.4). This is computer-assisted: one exact
  computation on the grid (22, 5), done by two independent solvers.
- So the first band of (L) holds for n ≤ 4, and α_N = 7π/9 for 17 ≤ N ≤ 20. The upper bound is
  `alpha_lower_band_le`. **Lean status (2026-10-20):** (R) for n ≤ 3 and the reduction of Attempt 3 are
  formalized (see §4.7); n = 4 (the (22, 5) computation and the grid reduction) is not.
- (R) for general n is **not proved**. n = 5 is reduced to a single finite computation (§4.6) that was
  not carried out.
- The three suggested routes each fail at a specific, numerically checked point (§4.5).

Scripts: [`percc.py`](../research/numerics/percc.py) (classes, grid reduction, exact checks) and
[`routes.py`](../research/numerics/routes.py) (the route tests).

### 4.0 What the earlier exact checks cover

A family found on the grid (m, L) lives at λ = Lπ/m. Valid families only shrink as λ grows, so a check
at (m, L) rules out counterexamples at λ ≥ Lπ/m. **It says nothing about families that exist only
closer to the band edge.**
- The Attempt 3 tables therefore cover λ ≥ 5π/17 for n = 3 (band edge 2π/7), λ ≥ 3π/13 for n = 4
  (edge 2π/9), and λ ≥ 3π/16 for n = 5 (edge 2π/11).
- The strip next to the band edge, where the LP bounds fail and the band-edge counterexamples live, was
  unchecked. §4.3 shows which single grid closes it for a given family size.

### 4.1 Classes by number of sign changes

Write c(f) for the number of sign changes of f per half-turn. c(f) is odd, because f(x + π) = −f(x).
Also c(f) ≤ n, because cλ ≤ π < (n + ½)λ. Let 𝒮_c = {f ∈ 𝒮 : c(f) = c}. Each 𝒮_c is itself a
compatible family, and |𝒮| = Σ_c |𝒮_c|.

> **(R_c), conjecture.** If (2n+1)λ > 2π, then |𝒮_c| ≤ 2·C(n, c) for every odd c ≤ n.

Since Σ_{c odd} 2C(n, c) = 2^n, (R_c) for all c implies (R). The bound is sharp for every c at once:
the Erdős–Szekeres family has exactly 2C(n, c) words with c changes. (R_c) would also explain why
every optimal family in Attempt 3 has exactly this profile: a family of size 2^n has to fill every
class to its cap.

Exact largest family per class (`percc.py table`, `percc.py max`):

| n | grids (m, L) | c = 1 | c = 3 | c = 5 | cap 2C(n,c) |
|---|---|---|---|---|---|
| 2 | (7,3), (9,4), (11,5) | 4 | | | 4 |
| 3 | (10,3), (13,4), (16,5), (19,6) | 6 | 2 | | 6, 2 |
| 4 | (13,3), (17,4), (21,5), **(22,5)** | 8 | 8 | | 8, 8 |
| 5 | (16,3), (21,4) | 10 | 20 | 2 | 10, 20, 2 |
| 6 | (19,3) | 12 | ≥ 40 (bound 46 after 2000 s, not closed) | 12 | 12, 40, 12 |
| 3, band edge | (7,2) | 7 | 3 | | total 10 = overall maximum |
| 4, band edge | (9,2) | 9 | 12 | | total 21 = overall maximum |

At the band edge the class maxima still add up to the overall maximum.

(R_c) is not an LP statement either. The fractional chromatic number of the compatibility graph of one
class is below cap + 1 for c = 1 (it equals 2π/λ) and for n = 3. But for n = 4, c = 3 it is 10.40 at
(13,3) and 9.71 at (17,4), both above 9. So the classes need integral arguments too. §4.2 gives them
for c = 1 and c = n; §4.4 uses a computation for c = 3, n = 4.

### 4.2 Two classes by hand; (R) for n ≤ 3

**Lemma 0 (witness arcs).** If f and g are compatible, some open arc of length λ contains no sign change
of f or g, and f = −g on it.

*Proof.* Let B be an open arc of length λ with fg = −1 on B. Changes of f are ≥ λ apart, so f changes
at most once in B, and likewise g. Since fg is constant on B, f changes at a point of B exactly when g
does. If neither changes in B, take B. Otherwise both change at some y ∈ B. The runs of f and g ending at
y have length ≥ λ, so neither changes in (y − λ, y), and fg = −1 just left of y. Take (y − λ, y). ∎

**Theorem A (c = 1).** |𝒮_1| ≤ ⌊2π/λ⌋ = 2n.

*Proof.* A function with one change per half-turn is +1 exactly on a half-open half-circle
[u_f, u_f + π). For two such functions, fg = −1 on two antipodal arcs whose length is the circular
distance between u_f and u_g on S¹, and fg = +1 elsewhere. So f and g are compatible iff u_f and u_g are
≥ λ apart. A circle of length 2π < (2n+1)λ holds at most 2n such points. ∎

**Theorem B (c = n, n odd).** |𝒮_n| ≤ 2.

*Proof.* Work on T = ℝ/πℤ and write π = nλ + ε. The band condition is exactly ε < λ/2. A member of
𝒮_n has n changes in T, and consecutive changes are between λ and λ + ε apart.

*Slots.* Suppose f, g, h ∈ 𝒮_n are pairwise compatible. By Lemma 0 there is an arc A = (a, a + λ) on
which f and g do not change and f = −g.
- List the changes of f after a as y_1 < … < y_n ≤ a + π. Then a + kλ ≤ y_k ≤ a + π − (n−k)λ = a + kλ + ε.
- So each slot Σ_k = [a + kλ, a + kλ + ε], k = 1, …, n, contains exactly one change of f, and the same
  holds for g.
- Between the slots lie the gaps G_k = (a + kλ + ε, a + (k+1)λ) for 1 ≤ k ≤ n − 1, of length λ − ε.
  Add G_0 = (a + ε, a + λ − ε) ⊂ A, which is nonempty because 2ε < λ.
- f and g change once in each slot and nowhere else, and f = −g on A. Hence f = −g on every G_k.

*Where h agrees with g.* By Lemma 0 there is an arc A′ of length λ on which f and h do not change and
h = −f. A′ lies in one run of f.
- If that run is (y_k, y_{k+1}), the left end of A′ lies in [y_k, y_{k+1} − λ] ⊂ Σ_k, so A′ ⊃ G_k.
- If it is the run containing A, the left end lies in [a − ε, a + ε], so A′ ⊃ G_0.

So h = −f = g on some G_k, and h has no change there. In the same way h = −g on some G_j, again with no
change of h. Hence j ≠ k.

*Counting.* G_k and G_j cut T into two closed arcs R_1 and R_2, and every change of h lies in
R_1 ∪ R_2. Say R_1 contains s of the slots and R_2 the other n − s, with 1 ≤ s ≤ n − 1.
- Each R_i consists of its slots, the gaps between them, and at most an extra ε where it borders G_0 or
  A. So |R_1| ≤ (s − 1)λ + 2ε and |R_2| ≤ (n − s − 1)λ + 2ε.
- Since 2ε < λ, R_1 contains at most s points that are pairwise ≥ λ apart, and R_2 at most n − s.
- hg is +1 on G_k and −1 on G_j, so it changes sign an odd number of times in R_1. It changes sign
  exactly where one of h, g changes, and g changes s times in R_1. So h changes s + 1 times mod 2 in
  R_1, hence at most s − 1 times. Likewise h changes at most n − s − 1 times in R_2.
- Altogether h changes at most n − 2 times, but h has n changes. Contradiction. ∎

At the band edge (2ε = λ) the capacity step fails, and indeed three such functions exist there: grid
(7, 2), n = 3.

**Corollary.** (R) holds for n = 1, 2, 3 at every λ in the band.
- For n ≤ 2 only c = 1 occurs, so Theorem A applies.
- For n = 3, |𝒮| = |𝒮_1| + |𝒮_3| ≤ 6 + 2.

This covers the whole band, including the strip of §4.0.

### 4.3 The finite-grid reduction

**Lemma (grid reduction).** Let 𝒮 be as in (R) for some λ with (2n+1)λ > 2π, and let J = Σ_f c(f). Put

    P_J = max { k/w : k, w positive integers, k ≤ J, 2k < (2n+1)w }.

Then for all positive integers m, L with m/L ≥ P_J there is a family of the same size at (m, L), in the
discrete model of `relaxation.py`, and each member keeps its number of changes.

*Proof.* Measure lengths in units of λ, so T has length P_0 = π/λ < n + ½.
1. *Type.* Take one vertex for each (member, change) and list the J vertices in cyclic order around T,
   breaking ties arbitrarily. For each pair f ≠ g with g ≠ −f, fix a run of fg on which fg = −1, of length
   ≥ 1. One exists by compatibility, and its ends are vertices of f or g.
2. *Constraints.* The variables are x_1 ≤ … ≤ x_J ≤ x_1 + P, lifted positions on a circle of length P.
   - (i) Order: x_{i+1} − x_i ≥ 0 and x_1 + P − x_J ≥ 0.
   - (ii) Coincidence: x_i = x_j whenever vertices i and j coincide in 𝒮.
   - (iii) Runs: x_j − x_i ≥ 1 for consecutive changes i → j of one member. Add P when the arc passes
     the cut between vertex J and vertex 1.
   - (iv) Witness runs: the same inequality for each fixed run of step 1.

   The positions of 𝒮 satisfy all of these with P = P_0.
3. *Any solution is a family.* (i)–(ii) keep the cyclic order and all coincidences, so no change of f or
   g enters a fixed run, and coincident changes of f and g inside it stay coincident. Each fixed run is
   therefore still a run of fg with fg = −1, of length ≥ 1 by (iv), and every run of a member stays ≥ 1
   by (iii). A pair with g = −f keeps all its changes coincident by (ii), so it stays a pair g = −f.
4. *Which P work.* Every constraint reads x_j − x_i ≥ α − βP with α, β ∈ {0, 1}. Such a system is
   feasible iff every directed cycle of the constraint graph has Σα ≤ P·Σβ.
   - A cycle with Σα ≥ 1 has Σβ ≥ 1. The edges with β = 0 are of three kinds: order edges, which go
     forward; coincidence edges, which join coincident vertices; and run edges that do not pass the
     cut. A run edge has length ≥ 1 in 𝒮, so it goes strictly forward to a later non-coincident
     vertex. So a cycle using only β = 0 edges can never return after an α = 1 edge.
   - Simple cycles suffice, and a simple cycle has Σα ≤ J.
   - So the feasible P form a ray [P*, ∞), where P* = 0 or P* = k/w with 1 ≤ k ≤ J. P_0 is feasible and
     P_0 < n + ½, so P* ≤ P_J ≤ m/L.
5. *Integrality.* Take P = m/L and multiply by L. The right-hand sides become the integers Lα − mβ. A
   feasible system of difference constraints with integer bounds has an integer solution
   (shortest-path potentials). These are change positions on m cells with every run and every fixed run
   ≥ L cells, i.e. a discrete family at (m, L). ∎

*Numerical check of the lemma* (`routes.py pstar`, `routes.py realise`).
- The seven non-inflatable 3-change families of §4.5(a) have P* = 13/3 and J ∈ {21, 24}. Each one
  realises with integer positions, as a valid compatible family with the same change counts, on
  (22, 5) and on (13, 3), whose ratios are ≥ 13/3. None realises on (17, 4), whose ratio is
  4.25 < 13/3.
- The family of Attempt 3, item 2 (P* = 10/3) realises on (17, 5) and (10, 3) but not on (13, 4).
- Six random maximal families at (31, 7) have P* = 4 and all realise on (22, 5).

The converse is immediate: a discrete family at (m, L) with m/L < n + ½ is a family at λ = Lπ/m in the
band. Hence:

**Corollary 1 (each n is one computation).**
- (R_c) for n is equivalent to: no compatible set of 2C(n,c) + 1 strings with c changes exists on the
  single grid (m, L) = P_J (in lowest terms), with J = c·(2C(n,c) + 1).
- (R) for n is equivalent to: no compatible set of 2^n + 1 strings, with any numbers of changes, exists
  on the grid P_J with J = n(2^n + 1). This J bounds the changes of any 2^n + 1 members.

`percc.py grid n c` prints the grid:

| class | members to exclude | J | deciding grid | functions there |
|---|---|---|---|---|
| any n, c = 1 | 2n + 1 | 2n + 1 | (n, 1), i.e. λ = π/n | 2n (Theorem A) |
| n odd, c = n | 3 | 3n | (n, 1) | 2 (Theorem B) |
| n = 4, c = 3 | 9 | 27 | **(22, 5)** | 528 |
| n = 5, c = 3 | 21 | 63 | (60, 11) | 16240 |
| n = 4, all classes | 17 | ≤ 51 | (49, 11) | about 5100 |

**Corollary 2 (small families inflate).** If J ≤ 3n then P_J = n. So any family with at most 3n
changes in total is realisable at λ = π/n.
- This reproves Theorems A and B.
  - At λ = π/n, compatible one-change functions have jumps ≥ π/n apart on S¹, so there are at most 2n.
  - At λ = π/n, every run of an n-change function equals π/n, so compatibility forces g = −f, and there
    are at most 2.
- It also sharpens item 4 of Attempt 3. In the T picture, an obstruction to inflation needs a cycle with
  k ≥ 3n + 1 λ-constraints winding w ≥ 3 times.
- Every non-inflatable family whose P* I computed has P* = (3n+1)/3 exactly (`routes.py pstar`).
  These are the two families of Attempt 3, items 2 and 4 (10/3, n = 3), and the seven 3-change
  families of §4.5(a) (13/3, n = 4).

### 4.4 n = 4 (computer-assisted)

**Theorem C.** (R) holds for n = 4 at every λ ∈ (2π/9, π/4].

*Proof.* Only c = 1 and c = 3 occur. Theorem A gives |𝒮_1| ≤ 8. If |𝒮_3| ≥ 9, take nine members of
𝒮_3: then J = 27 and P_27 = 22/5. By the grid reduction there would be nine pairwise compatible
3-change strings at (22, 5). There are not:
- `percc.py max 22 5 3`: CP-SAT returns OPTIMAL, largest = 8, out of 528 functions (82 s).
- `percc.py sat 22 5 3 9`: CaDiCaL reports UNSAT in all 8 symmetry-orbit cases (202 s).
  - The symmetry breaking forces the least member of one orbit into the family and excludes every
    earlier orbit. This is valid because shifts and reflections preserve the problem.
  - `sat 22 5 3 8` finds a family of 8.
- The same verdicts came out of a separate first run: CP-SAT with clique-cover constraints and
  `relaxation_sat.functions`, and SAT with a third, independently written generator. All three
  generators give 528 functions.

So |𝒮_3| ≤ 8 and |𝒮| ≤ 16. ∎

The reduction step itself was checked numerically; see the end of the proof in §4.3. The 8-member
family found at (22, 5) also passes `relaxation.py family` (it is valid and compatible).

*What Theorem C gives.*
- With Attempt 3's reduction: a set with all angles ≤ (1 − 2/u)π, 8 ≤ u < 9, has ≤ 16 points.
- With `sendovUpper`: α_N = 7π/9 for N = 17, 18, 19, 20.
- Together with n ≤ 3 this is the whole first band up to N = 20.
- Sendov's paper claims these values, but its argument has the gap described in `MATH-CHECK.md`.
- In Lean this would need (R) for n = 4, i.e. a certified form of the (22, 5) computation, for example
  an LRAT proof checked in Lean, plus Attempt 3's reduction. Neither is done.

### 4.5 The suggested routes: where each one breaks

**(a) Inflation and multiply-winding walks.**
- The goal: show that 2^n + 1 members force a walk with k ≥ (2n+1)·winding.
- Restricting to one class does not remove the obstruction. 7 of 300 random maximal 3-change families
  at (13, 3), n = 4, are not inflatable to π/4, and all have P* = 13/3 (`routes.py inflate`).
- The whole-family rate there is 16/300. In 6 of those 16 the 3-change part alone is already
  non-inflatable.
- The two mixed examples of Attempt 3 do split into inflatable classes.
- So a proof along this route must deal with families that really carry 3n + 1 tight constraints
  winding 3 times around T, and I found no argument for that.
- What the route does give is Corollary 1: for each n only walks with k ≤ J matter.

**(b) Adaptive decision trees.** The natural induction fails as stated: fixing one value does not halve
the family.
- On every grid tested, the largest compatible family whose members all equal +1 on one fixed cell
  has 3·2^{n−2} members, not 2^{n−1} (`routes.py fixedsign`). That is 3 for n = 2 at (7,3), (9,4);
  6 for n = 3 at (10,3), (13,4), (16,5); and 12 for n = 4 at (13,3), (17,4).
- So a depth-n tree cannot come from an induction whose hypothesis is a size bound for families with
  prescribed values at the queried points.
- The query must depend on the whole family, and the hypothesis must carry more than a size bound.

Inside one class, *non-adaptive* evaluation worked in every test (`routes.py points`).
- n cells separate every random maximal c-change family at (10,3), (13,4) and (13,3).
- The exception: at (13,3), for one 7-member 3-change family, no separating choice of cells also keeps
  every word at exactly c changes, which is what an injection into the 2C(n,c) words with c changes
  would need.

**(c) Transforms from band n to band n − 1.** I tested the most flexible order-preserving transform:
collapse *any* L cells, not just a window, chosen separately for each of two parts, allowing runs to
vanish.
- Lemma (SD): every family is the union of two parts that each become valid at (m − L, L) after such a
  collapse. (SD) would imply (R) by induction on n.
- (SD) is false: 5 of 28 maximum (8-member) families at (10, 3) cannot be split this way
  (`routes.py split`).
- In the first of them the largest collapsible parts have 4 members each, but no two of them are
  complementary. The same holds on the doubled grid (20, 6).

### 4.6 What remains

- **n = 5.** By Theorems A and B, (R) for n = 5 follows from (R_c) for c = 3. By Corollary 1 that is
  equivalent to one statement: no 21 pairwise compatible 3-change strings exist at (60, 11).
  - That grid has 16240 such functions. A sample says about 75% of pairs are compatible, so a direct
    encoding has about 3·10⁷ incompatible pairs.
  - The direct CP-SAT/SAT set-up used here does not scale that far: the whole n = 5 family at (27, 5),
    1854 functions, did not close in 45 minutes.
  - It needs a symmetry-aware search, or a bound on critical cycles sharper than k ≤ J.
  - Evidence so far: the c = 3 class maximum is 20 at (16,3) and (21,4) (CP-SAT OPTIMAL, 118 s and
    81 s). Both ratios are below 60/11, so this is evidence, not proof.
- **A hand proof of (R_c) for 3 ≤ c ≤ n − 1.**
  - The slot argument of Theorem B uses that compatible n-change functions lock into the same slots.
  - For c = n − 1 the slots overlap. Two "species" appear: near-square waves of frequency n − 1, and
    n-waves with one missing change.
  - At the band edge (9, 2) the 12-member optimum is 3 of the first kind plus 9 of the second.
  - Just above the edge they must trade off down to 8. No argument found.
- **All n.** The grid of Corollary 1 grows like J ~ n·2^n. So the reduction settles each n in principle
  but is not a route to every n.

### 4.7 What is formalized in Lean

All without `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound` (`Audit.lean`).
- `StatementR n` (`Blumenthal/SignSeq.lean`): (R) for families of `f : ℝ → Bool` with `f (x + π) = ¬f x`,
  runs ≥ ℓ (no two switches inside an open window of length ℓ), pairwise opposite on an open arc of
  length ℓ.
- Sign sequences `SignSeq ℓ`: changes `y : ℤ → ℝ`, `y (k + c) = y k + π`, `c` odd, gaps ≥ ℓ.
  `exists_signSeq` (`SignBridge.lean`) shows every function in (R) is one, off its change points.
- Lemma 0 `exists_witness`, Theorem A `card_le_of_c_eq_one` (≤ 2n), Theorem B `card_le_two_of_c_eq`
  (≤ 2 for c = n, any odd n), and `statementR_of_le_three`.
- Attempt 3's reduction (`FirstBand.lean`), with σ_p(x) = label of the last point of W(p) at or before
  x + ℓ/2 instead of the Voronoi function (same three properties): `card_le_of_statementR`,
  `capacityBound_firstBand_of_statementR` (any n ≥ 2, assuming `StatementR n`).
- Consequences: `CapacityBound` on [2,3), [4,5), [6,7); `alpha_five` (3π/5), `alpha_nine`, `alpha_ten` (5π/7).
- Not formalized: n = 4 (Theorem C: the (22, 5) SAT certificate and the grid reduction of §4.3).
## Attempt 5: the top class for even n (c = n − 1) (2026-10-20)

**Results.**
- Three operations on a family keep compatibility (§5.1). With Theorem B, two of them give local integral
  bounds. The third gives a recursion n → n − 2.
- **Theorem D.** (R_{n−1}) holds for every even n when π/λ < n + 2/13 (§5.2, by hand). With Theorem C as
  the base, it holds for n ≥ 6 when π/λ < n + 4/21.
- **Theorem E.** On the whole band, (R_{n−1}) follows from one local statement (U): at most 2n − 2 members
  change inside any open arc of length λ (§5.3).
  - (U) is exact (CP-SAT OPTIMAL) on every grid tested.
  - It fails at the band edge, as it must.
  - **(U) is not proved.**
- **c = n − 2 (n odd):** the same reduction covers only π/λ < n + 1/(n−1). No proof (§5.5).

Notation: units λ = 1, T = ℝ/Pℤ, P = π/λ = n + ε, 0 ≤ ε < ½. Members have runs ≥ 1. M(n, c) is the largest
class-c family in band n. The scripts used here are not in the repository; they are kept with the session
notes.

### 5.1 Three compatibility-preserving operations

**Lemma D (delete a window of length 2).** Let W ⊂ T be an open arc of length 2. Let 𝒮_W be the members with
exactly two changes in W. Delete W and glue. Then each f ∈ 𝒮_W becomes a class-(c − 2) function with runs
≥ 1 on a circle of length P − 2 (band n − 2), and compatible members stay compatible. Hence
|𝒮_W| ≤ M(n − 2, c − 2).

*Proof.* Validity:
- Let p_0 < p_1 < p_2 < p_3 be consecutive changes of f, with p_1, p_2 ∈ W = (w, w + 2) and p_0 ≤ w,
  p_3 ≥ w + 2.
- Two changes are removed, so f has no change at the seam. The merged run has length p_3 − p_0 − 2 ≥ 1.
- The deleted set is P-periodic, so oddness is kept.

Compatibility. Take a witness A for f, g ∈ 𝒮_W (Lemma 0: open, length 1, f = −g, no change of f or g). If A
misses W + Pℤ it survives; for n ≥ 4 it meets at most one translate. Set:
- q_1 < q_2: the changes of g in W;
- u = max(p_1, q_1), v = min(p_2, q_2);
- σ: the value of fg just left of w. It is also the value just right of w + 2, since both f and g change
  twice in W;
- L, R: the last change of f or g before u, and the first after v. So L ≤ u − 1 and R ≥ v + 1.

The cases:
- *A ⊂ W.* The four points cut W into pieces.
  - The end pieces are shorter than 1, because p_2 − p_1 ≥ 1 and the span of the four points is < 2.
  - Apart from (u, v), the two remaining pieces have total length < 1.
  - So A ⊂ (u, v). There fg = σ, so σ = −1.
  - The glued arc (L, w) ∪ (w + 2, R) is opposite, change-free, and has length ≥ v − u ≥ 1.
- *A ∋ w.* Then σ = −1, and A ∩ W lies left of min(p_1, q_1). The arc A ∖ W, glued to (w + 2, R), has
  length ≥ min(p_2, q_2) − min(p_1, q_1) ≥ 1.
- *A ∋ w + 2.* Symmetric. ∎

**Lemma I (insert a unit window).** Fix x ∈ T. Insert a unit window at x, and give each member f the value
−f(x) on it. Each member with no change in (x − 1, x + 1) becomes class c + 2 in band n + 1, with runs ≥ 1:
the new runs are x − z_−, 1 and z_+ − x. Compatibility is kept:
- a witness not containing x survives;
- if x ∈ A, then fg(x) = −1 and the window itself is a witness.

So at most M(n + 1, c + 2) members have no change in (x − 1, x + 1). *For c = n − 1, n even, Theorem B
gives ≤ 2.*

**Lemma K (delete a unit window).** Let W = (w, w + 1). Take the members with exactly one change in W and no
other change in (w − 1, w + 2). Deleting W makes them class c in band n − 1, compatibly:
- if fg = −1 at the seam, the glued opposite arc has length ≥ 2;
- otherwise every witness avoids the collar.

So there are at most M(n − 1, c) of them. *For c = n − 1, Theorem B gives ≤ 2.*

Lemma D was checked on doubled grids, for every window, on 200 random maximal families at (13,3) and 100
at (31,7) (n = 4). It never failed.

### 5.2 Theorem D: the recursion near λ = π/n

f *survives* at x if (x − 1, x + 1) contains exactly two changes of f.
- f survives iff the run of f through x reaches within distance 1 of x on both sides.
- So the set where f does not survive, BC(f), has measure ≤ 2P − 2c. For c = n − 1 this is 2 + 2ε.
- Lemma D gives |𝒮| ≤ M(n − 2, n − 3) + #{non-survivors at x}, for every x.

*Proof of Theorem D.* Induct on even n; the base case n = 2 is Theorem A.
- If |𝒮| = 2n + 1 and every x had ≥ 5 non-survivors, then 5P ≤ Σ_f |BC(f)| ≤ (2n + 1)(2 + 2ε). That
  forces ε ≥ (n − 2)/(4n − 3).
- So for smaller ε, some x has ≥ 2n − 3 survivors. They contradict the induction hypothesis at the same ε.
- The thresholds (k − 2)/(4k − 3) increase with k, so the binding one is k = 4, giving 2/13. Starting from
  Theorem C, the binding one is k = 6, giving 4/21. ∎

**This averaging is exactly the LP bound.** Averaged over x, Lemma D gives |𝒮| ≤ 2(n − 2)P/(n − 2 − ε). That
equals the fractional chromatic number of the class:

| grid | 2(n−2)P/(n−2−ε) | χ_f |
|---|---|---|
| (13,3) | 10.400 | 10.400 |
| (17,4) | 9.714 | 9.714 |
| (22,5) | 11.000 | 11.000 |

Adding integral cuts to that LP (clique constraints, plus at every x: survivors ≤ 2(n − 2); members with no
change in (x − 1, x + 1) ≤ 2 (Lemma I); isolated changes ≤ 2 (Lemma K)) lowers it, but not below 9:
- (13,3): 9.58;
- (17,4): 9.15;
- (22,5): 9.94 (survivor cut only).

The LP optimum puts all its weight on functions with a gap ≥ 2λ (shapes (1,1,7/3) and (1,4/3,2) at (13,3)).

### 5.3 Theorem E: the whole band from one window

**Slot lemma.** Suppose the union Z of all change points has two cyclically consecutive points more than ε
apart. Then |𝒮_c| ≤ 2C(n, c), and |𝒮| ≤ 2^n.

*Proof.* Choose y so that [y − ε, y) contains no change. The half-open unit slots [y + k, y + k + 1),
k = 0, …, n − 1, then hold all changes, each at most one per member. A member's word is its set of
occupied slots together with its value just before y. If f, g have the same word, then:
- f = g at every slot boundary;
- f = g in the gap and in unoccupied slots;
- inside an occupied slot, fg = −1 only between the two changes, on an arc shorter than 1.

So f and g are incompatible. ∎

A 2^n + 1 family therefore has an ε-dense change set. This is consistent with the non-inflatable families
of §4.5, which use every cell of (13,3).

**(U), conjecture.** For every open arc U ⊂ T of length 1, at most 2n − 2 members of 𝒮_{n−1} change in U.

**Theorem E.** (U) implies (R_{n−1}) for every ε < ½.

*Proof.* Suppose |𝒮| = N = 2n + 1. For y ∈ T, let c(y) be the number of members with a change in
Λ = (y − ε, y).
- Since ∫c = N(n − 1)ε < (n − 1)P exactly when ε < ½, there is a positive-measure set of y with
  c(y) ≤ n − 2. Take such a y with no change at any of the points y + k.
- The open unit slots S_k = (y + k, y + k + 1), k = 0, …, n − 1, together with Λ, hold all changes, at
  most one per member each.
- So, with h_k the number of members having no change in S_k,

      Σ_k h_k = Σ_f (n − (n − 1 − [f changes in Λ])) = N + c(y) ≤ 3n − 1.

- Hence some h_k ≤ 2, and S_k has ≥ 2n − 1 changers, which contradicts (U). ∎

The same computation for any class c needs (U_c): at most 2C(n − 1, c − 1) changers per window. It gives
c(y) ≥ c for all y, which is a contradiction only for ε < n/(2C(n, c)). That is ½ for c = 1 and c = n − 1,
and 1/(n − 1) for c = n − 2.

**Evidence for (U).** CP-SAT, OPTIMAL in every case. The table gives the largest compatible family all of
whose members change inside one open window of length λ:

| grid | n | largest | 2n − 2 |
|---|---|---|---|
| (13,3) | 4 | 6 | 6 |
| (22,5) | 4 | 6 | 6 |
| (31,7) | 4 | 6 | 6 |
| (19,3) | 6 | 10 | 10 |
| (9,2), band edge | 4 | **8** | 6 |
| (13,2), band edge | 6 | **15** | 10 |

Further data:
- On random maximal families at (13,3), (22,5) and (31,7), every window misses at least two members of any
  8-member family.
- Some pair of adjacent windows has exactly two misses each.

### 5.4 Why (U) resists the same arguments

- **A one-sided version is false.** It is not true that at most n − 1 members change *upward* in U. For n = 4
  at P = 4.4 (grid (88, 20), U = cells 1–19), the 3-change functions with changes at
  {1,22,42}, {10,42,62}, {19,62,82}, {1,22,62}, {19,42,82} are valid and pairwise compatible, and all change
  upward in U (checked with `relaxation.compatible` and `runs_ok`). So (U) must use both directions
  together.
  - In the n = 4 model, an up-changer is a point (a, b) with b − a ∈ [1, 2 + ε].
  - Two up-changers are compatible iff their L∞ distance is ≥ 1.
  - Up to 5 such points fit; the up/down cross constraints must cut the total to 6.
- **Rotating slots around U breaks injectivity.** Fix S_0 = U and rotate n − 1 unit slots and an ε-gap
  around the rest of T. Then:
  - each point lies in the gap with probability ε/(n − 1 + ε);
  - the expected number of gap hits is < n − 2 exactly when ε < ½, which is what (U) would need;
  - the slot that wraps across U still holds at most one change per member.

  But two members with the same word can be compatible: one changes just before U and the other just after
  it, with an opposite arc of length ≥ 1 between f's two changes. Recording the side doubles the words.
  The non-wrapping placements form only n discrete gap positions, and averaging over n positions is too weak.
- **Recursing (U) on itself with Lemma D needs ≤ 2 non-survivors among the changers.** Averaging fails here
  too.

### 5.5 c = n − 2 (n odd)

- Lemma D gives M(n, n − 2) ≤ M(n − 2, n − 4) + #non-survivors, with cap difference 4n − 6.
- Uniform averaging fails already at ε = 0. Words with adjacent agreements have |BC| = 3, so the bound
  |BC| ≤ 4 + 2ε is lossy.
- Theorem E's reduction covers only ε < 1/(n − 1), conditional on (U_{n−2}): at most (n − 1)(n − 2)
  changers per window.
- Lemma I caps the members deep at a point by M(n + 1, n), the top class of the even band n + 1. For n = 5
  that is (R_5) at n = 6. Doubly deep points (two inserted windows) give ≤ 2 by Theorem B.
- No proof, and no new n = 5 computation.

### 5.6 Other routes, all negative (n = 4 unless noted)

- **Species split by a gap ≥ 2λ.** Species 2 alone is already non-LP (see §5.2). Species 1 alone reaches 4
  at (13,3) and 5 at (22,5).
- **Fixed sign at one cell.** The class maximum is 2n − 1, not n: 7 at (13,3), (17,4), (22,5); 11 at (19,3)
  for n = 6.
- **One up-change per member as a representative, pairwise ≥ λ apart on S¹.** Fails for 18 of 91
  8-member families at (13,3).
- **LP restricted to the neighbourhood of one or two members.** Up to 8.17 for one member and 7.17 for two
  at (13,3). Still fractional.
- **Critical cycles.** For non-inflatable 8-families at (13,3) the cycle is the rotation orbit
  0, 3, 6, …, 10 (k = 13, w = 3). At the edge, 9-families have 9 unit arcs in two turns. No rule found.
- **Band-edge class maxima.** 12 at (9,2), 19 at (13,2) (n = 6), 26 at (17,2) (n = 8), i.e. (7n − 4)/2.
- **n = 6.** (25,4): class maximum 12 = cap (OPTIMAL). (32,5): ≥ 12, bound 15 after 58 min, not closed.

### 5.7 Partial results on (U)

- **Theorem E needs no slots.** For each member, the y with no change of f in (y, y + 1) form a set of
  measure P − (n − 1) = 1 + ε. So the average number of members missing a unit window is N(1 + ε)/P. For
  N = 2n + 1 this is < 3 exactly when ε < ½, so some window has ≥ 2n − 1 changers.
- **(U) holds for short windows (proved).** At most 2n − 2 members change in any open arc of length
  ≤ 1 − ε. *Proof.*
  - Embed the arc in a unit window U, and cover the other changes of the changers by greedy half-open unit
    slots in T ∖ U. If at most n − 1 slots are needed, the slot argument of §5.3, with U as slot 0, injects
    the changers into (missing slot, sign): at most 2(n − 1) words.
  - Otherwise greedy finds n changes, consecutive ones ≥ 1 apart. Call the owners of the first and last
    f_1 and f_n. Their changes in U satisfy p_n − p_1 ≥ (n − 1) + 2 − P = 1 − ε.
  - So the U-changes are not inside an arc of length < 1 − ε. ∎
- **Why that is not enough.**
  - Fed into the averaging, the short version gives the cap 2n only for ε < 1/(2n + 3).
  - For a unit window, the obstruction is a chain of n + 2 changes, from p_1 to p_n + P, with every gap in
    [1, 1 + ε). It needs changers whose U-changes lie near both ends of U.
- **(U) is not LP either.** The fractional bound for the changers of one window is:
  - 7.50 at (13,3);
  - 7.09 at (17,4);
  - 7.85 at (22,5);

  all above 2n − 1 = 7.
- **Structure at (22,5).** Changers with an upward change in U number at most 5 = 2n − 3. With k up-changers
  the total is still at most 6, for every k = 1, …, 5 (CP-SAT OPTIMAL). So the two directions trade off one
  for one.
- **A block recursion.** Let (U_r) say: at most 2(n − r) members change in each of r consecutive unit
  windows. (U_{n−1}) holds trivially. All changes are then pinned, so members of the same sign are
  incompatible, giving ≤ 2.
  - Averaging the step (U_{r+1}) → (U_r) over windows in the complement of the block works for
    ε < (m − 4)/(2m − 2) with m = n − r, because each member loses at most 1 + ε at the block's ends.
  - It fails for m ≤ 4 at every ε, and for larger ε at every m. So small m and large ε need another
    argument.
- **The tight chain does not lower the count.** At (22,5) there are 5 possible chains (4 changes in
  T ∖ U, consecutive gaps ≥ λ). For each one, forcing every chain point to be a change of the family
  still allows 6 = 2n − 2 changers (CP-SAT OPTIMAL). Example: five down-changers {0,5,11}, {0,5,16},
  {3,15,20}, {4,10,15}, {4,9,21} and one up-changer {0,12,17}. So excluding chains is (U) itself.
  - Relative to the lattice of the chain (slots of length λ from the first U-change, leftover arc of
    length ε), the members with no change in the leftover inject as usual. The members with a change in
    the leftover miss two slots.
  - In the example these leftover members are exactly as many as the unused words, but no simple rule
    assigns them words: (largest or smallest missing slot) × (same or flipped direction). Each such rule
    fails on a third or more of the random maximal changer families at (22,5).
- **c = n − 2, n = 5: the tools give nothing new.**
  - The reduction above needs ε < ¼.
  - Lemma D needs a point with ≤ 14 non-survivors. Averaging gives about 16.8.
  - Lemma I gives only ≤ 12 deep members, via (R_5) at n = 6, where words have 2.
  - Already, the exact computations at (16,3), (21,4), (26,5) cover π/λ ≤ 16/3. So only the strip
    (16/3, 5.5) is open, and the grid (60,11) decides it.

### 5.8 Two further routes to (U), and where they stop

**(a) Induction on n, as a minimal-counterexample argument.** Take a window U with 2n − 1 changers, at
the least n for which (U) fails.
- Delete a 2-window W that avoids the U-changes. By Lemma D, the members with exactly two changes in W
  remain compatible changers of U in band n − 2. By minimality there are ≤ 2n − 6 of them.
- So every such W must have ≥ 5 changers without two changes in it. A contradiction needs one W with ≤ 4.
- Relative to a slot lattice with slot 0 ⊃ U-changes, the aligned windows S_k ∪ S_{k+1} lose at most 4
  of the members with no change in the leftover arc, by injectivity of the words.
- Each member with a change in the leftover arc misses two slots and spoils every aligned window that
  meets either one. For n = 4 one such member spoils both aligned windows.
- **This is where the route stops.** Excluding windows with ≥ 5 losses is the same window-finding
  problem as §5.2, now inside the changers.
- Numerically the needed window always exists: every random maximal changer family at (22,5) (300) and
  (31,7) (200) has a W with ≤ 4 losses, and the 6-member ones have exactly 4. But a 7-member family
  cannot be tested.
- Contracting a single slot instead (unit deletion, band n − 1) keeps only the members whose change in the
  slot is isolated (Lemma K). With Theorem B there are at most 2 of them, so the counterexample is never
  transported.

**(b) Antipodal labelling / Tucker–Ky Fan.**
- Label x ∈ S¹ by the members that are + on a unit arc at x. Compatibility says every pair is separated by
  some antipodal pair of labels.
- Every integral bound found so far (Erdős–Szekeres at λ = π/n, the slot lemma, Theorem B, Lemma U′)
  injects the family into words through *one* cell structure. A parity or degree argument would naturally
  produce such a structure.
- **This is where the route stops:** no such structure exists in general. The non-inflatable 8-families
  at (13,3) (§4.5) have a change at all 13 boundaries. Four half-open slots of length λ cover at most 12
  of them.
- So a Tucker-type proof would have to give an injection into 2^n (or 2C(n,c)) words not induced by any
  single cell structure. None was found.

### 5.9 Further angles (n = 4 unless noted)

**Capture covering: new, integral, unproved.** Call a sequence of the window operations D, K, I of §5.1 a
*capture* if it ends in the top class of an odd band. The members it keeps are pairwise compatible there,
so by Theorem B (Theorem A in band 1) it keeps at most 2 of them.
- **Every member is capturable.**
  - A member with a run ≥ 2 is captured by I at a deep point.
  - Any other member is captured by D^j I. Deleting j windows merges 2j + 1 consecutive runs into a run of
    length 1 + (2j + 1)(slack)/(n − 1). That reaches 2 within the available j.
- **Conjecture (C).** Every compatible family of class n − 1 is covered by n captures. (C) implies |𝒮| ≤ 2n
  with no averaging.
- **Evidence** (`capture.py`, depth ≤ 2, i.e. D, K, I, DK, DI, KD, ID at every position of the doubled grid):
  - all 130 functions at (13,3) and all 528 at (22,5) are capturable;
  - every random maximal family of size 7 or 8 (100 at each grid) is covered by exactly 4 = n captures.
  - The non-inflatable 8-family of §4.5 is covered by one DI and three DK. So the maximum families split into
    n captured pairs.
- **Where it stops.** Induction through D lifts a cover of the survivors at x (n − 2 captures) and needs the
  non-survivors at x covered by 2 captures, i.e. ≤ 4 of them. That is again the window step of §5.2.

**Dead angles.**
- **Polynomial method / Haemers rank over F₂** (`haemers.py`, CaDiCaL):
  - Class 1 at (9,4) needs rank 5 > 4 = α.
  - Even Theorem B's class at (10,3) needs rank > 2.
  - So low-rank fitting matrices cannot see these packing bounds.
- **LP plus every capture and deletion cut up to depth 2** (468 cuts at (13,3)): still 9.5789, the same as
  with depth-1 cuts (D, I, K). These local integral lemmas are exhausted.
- **Shifting / compression.** Type-preserving compression stops at P*, and P* = 13/3 > 4 for maximum
  families. Compressing to one cell structure is impossible when every cell is used (§5.8).
- **Stability / extension.** For F of size 2n + 1 and any g ∈ F, the points where F ∖ g has exactly 4
  non-survivors lie inside BC(g) automatically. The only quantitative version reproduces Theorem D's
  threshold.
- **Zones of U for (U).** Split U into end zones of length ε and a middle. Lemma U′ gives
  |left| + |middle| ≤ 2n − 2 and |middle| + |right| ≤ 2n − 2. A counterexample needs both end zones
  occupied, and nothing closes the gap.
- **Double counting (member, witness) with parity.** No parity identity was found. On T, fg has an even
  number of changes, but the number of long opposite runs has no fixed parity.

## What would settle the problem

Any one of the following:
- A proof of inequality (W) of `MATH-CHECK.md`, or of the Cover Lemma (§6.5) for the first band.
- For the first band only: a proof of (R) for n ≥ 5. (R) is now proved for n ≤ 4 (Attempt 4).
  - By item 1 of Attempt 3, any proof must be adaptive or otherwise integral.
  - Attempt 4.5 shows where decision trees, inflation and transforms break as posed.
  - The class conjecture (R_c) of Attempt 4.1 is a sharper target that splits (R) into pieces. Its
    cases c = 1 and c = n are proved.
  - The second band would still be open.
- A computer-assisted proof for fixed n combined with a structural reduction to bounded n.
  - For each fixed n the finite reduction now exists: one grid decides (R), Attempt 4.3.
  - No reduction to bounded n is known.
  - n = 5 needs the single computation of Attempt 4.6.

In Lean, only `CapacityBound` needs to be proved: `sendovAnswer_iff_capacityBound_and_upper`
together with `sendovUpper` gives `SendovAnswer` from it.
