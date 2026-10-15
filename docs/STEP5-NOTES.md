# Step 5 notes: attacking the general lower bound

Status: **open**. These notes record what has been tried, so nobody repeats it.

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

## What would settle the problem

Any one of the following:
- A proof of inequality (W) of `MATH-CHECK.md`, or of the Cover Lemma (§6.5) for the first band.
- For the first band only: a proof of (R) above. By item 1 of Attempt 3 it must be adaptive; an
  induction on n via decision trees, or an analysis of multiply-winding walks, are the natural
  routes. The second band would still be open.
- A computer-assisted proof for fixed n combined with a structural reduction to bounded n. No
  such reduction is known.

In Lean, only `CapacityBound` needs to be proved: `sendovAnswer_iff_capacityBound_and_upper`
together with `sendovUpper` gives `SendovAnswer` from it.
