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

## What would settle the problem

Any one of the following:
- A proof of inequality (W) of `MATH-CHECK.md`, or of the Cover Lemma (§6.5) for the first band.
- A computer-assisted proof for fixed n combined with a structural reduction to bounded n. No
  such reduction is known.

In Lean, only `CapacityBound` needs to be proved: `sendovAnswer_iff_capacityBound_and_upper`
together with `sendovUpper` gives `SendovAnswer` from it.
