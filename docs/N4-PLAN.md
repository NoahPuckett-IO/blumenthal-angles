# n = 4 in Lean: plan and status

Target: `StatementR 4`, hence `CapacityBound` on [8, 9) via `capacityBound_firstBand_of_statementR`,
hence α_N = 7π/9 for 17 ≤ N ≤ 20 (with `sendovUpper`). Mathematics: `docs/STEP5-NOTES.md` §4.3–4.4.

## Status

| Block | Content | Status |
|---|---|---|
| 1 | No 9 pairwise compatible 3-change strings on the (22, 5) grid | **Done**: `Grid.no_nine_compatible` (`Blumenthal/N4/GridMain.lean`). Axioms: propext, Classical.choice, Quot.sound. Full `lake build` verified on macOS. |
| 2 | Grid reduction: a continuous family realises on (22, 5) | **Done** (full macOS `lake build` passed): `Reduce1.lean` (complete constraint graph, cycle bound, potentials, transfer T1/T2), `Reduce2.lean` (windows, `exists_dstr`), `DiffCons.lean` (Lemma DC). |
| 3 | `card_le_sixteen`, `StatementR 4`, α values | **Done** (full macOS `lake build` passed): `N4.statementR_four`, `Blumenthal.alpha_seventeen_to_twenty` (`AlphaFour.lean`, needs the full Mathlib build). Audit: `Blumenthal/N4/Audit2.lean`. |

## Block 3 (assembly), for orientation

`SignSeq.card_le_sixteen`: for `F : ι → SignSeq ℓ`, `0 < ℓ`, `2π < 9ℓ`, pairwise `Compat`, `s.card ≤ 16`.
- `c ≤ 4` (`c_le`) and `c` odd, so `c ∈ {1, 3}`.
- `c = 1`: `card_le_of_c_eq_one` gives ≤ 8.
- `c = 3`: Block 2 + Block 1 give ≤ 8.
`statementR_four` then copies `statementR_of_le_three` (bridge `exists_signSeq`, `compat_of_rep`).

## Block 2: the reduction, formal route

As implemented: instead of order/run/witness edges, the complete graph on the 27 base points with
weight `5α − 22μ` for the best valid inequality `X w + μπ − X v ≥ αℓ` (α, μ ∈ {0,1}). This captures all
order and separation information at once; decoding only uses the transfer rules (T1) `p ≤ q ⇒ p' ≤ q'`
and (T2) `p + ℓ ≤ q ⇒ p' + 5 ≤ q'`.

Fix ℓ with 2π < 9ℓ and 9 members `F_1..F_9 : SignSeq ℓ`, all with `c = 3`, pairwise `Compat`.
Units: positions divided by ℓ, so a half-turn has length P₀ = π/ℓ < 9/2.

**Vertices.** The 27 change classes v = (i, k), i ∈ Fin 9, k ∈ Fin 3, with real position
x_v = y_i(k)/ℓ. A point of the cover is (v, m) at x_v + m P₀ (m ∈ ℤ); every change of every
member is such a point (`y_add_mul`).

**Edges** v → w with shift m ∈ ℕ and α ∈ {0, 1}, valid in the original:
x_w + m P₀ − x_v ≥ α.
1. Order edges: consecutive points in the sorted cyclic order of all 27 classes (α = 0), plus the
   reverse edge for coincident points (α = 0, keeps equalities).
2. Run edges: (i, k) → (i, k+1), α = 1 (`gap`); k = 2 → (i, 0) with m = 1 (`y_add_c`).
3. Witness edges: for each pair i ≠ j, `exists_witness` gives an arc of length ≥ ℓ free of changes
   of F_i, F_j with F_i ≠ F_j on it. Its two ends are consecutive merged changes p → q; edge
   p → q with α = 1.

**Cycle bound (the key arithmetic).** A closed walk of ≤ 28 edges with total shift w has
Σα ≤ P₀ w (sum of the original inequalities) and Σα ≤ 28. Since P₀ < 9/2: Σα = 0 when w = 0,
and 2 Σα < 9w otherwise. For integers k ≤ 28, w ≥ 1, 2k < 9w implies 5k ≤ 22w
(checked case by case for w ≤ 6; trivial for w ≥ 7). So every closed walk of ≤ 28 edges has
weight ≤ 0 for the integer weights 5α − 22m.

**Lemma DC (generic, Bellman–Ford potentials).** Finite vertex set V, integer edge weights c(v, w).
If every closed walk with at most |V| edges has total weight ≤ 0, then there is p : V → ℤ with
p(w) − p(v) ≥ c(v, w) on every edge. Proof: p(v) = maximum weight of a simple path ending at v.
Extending the best path to v by the edge v → w either gives a simple path to w, or w is already
on it; then the part from w to v plus the edge is a closed walk of ≤ |V| edges, weight ≤ 0, so
the prefix ending at w is at least as heavy.

**Decoding.** New integer positions p(v) on a half-turn of 22 cells.
- Order edges ⇒ weak cyclic order of all points preserved, coincidences preserved.
- Run edges ⇒ each member has 3 changes per half-turn with gaps ≥ 5 ⇒ a `Grid.DStr`
  (normalise residues mod 22 into a < b < c, record the sign on cell 0).
- Witness edges + order ⇒ for each pair, a window of ≥ 5 cells with no change of either member,
  on which the change counts (hence values) are the original ones, so they differ ⇒ `DCompat`.
- 9 pairwise compatible `DStr` contradict `Grid.no_nine_compatible`.

## Estimated size
- Lemma DC: ~300 lines (generic, reusable for n = 5).
- Encoding + cycle bound: ~500 lines.
- Decoding to `DStr` / `DCompat`: ~600 lines.
- Assembly: ~100 lines.
