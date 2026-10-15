# Numerics for the Lemma 4.1 math check

Supporting scripts for [`docs/MATH-CHECK.md`](../../docs/MATH-CHECK.md). Notation:
- λ = 2π/u;
- κ_u(q) = Σ_gaps max(0, ⌊θ/λ⌋ − 1) over the gaps between consecutive lines from q to the other points;
- F_u(Q) = Σ_q 2^{κ_u(q)}.

| File | What it does |
|---|---|
| `weight_search.c` | Simulated annealing that maximises F_u over s-point sets with max angle ≤ (1 − 2/u)π. `./weight_search u s iters restarts seed`; set `SHOW=1` to print the best configuration. |
| `weight_search_grid.txt` | Output of the grid n = 2…5, u = 2n+1−10⁻⁷ and 2n+2−10⁻⁷, s = 3…10 (12 restarts × 3·10⁵ steps). `bestF=0` means no feasible configuration was found. |
| `weights.py` | 50-digit helpers: max angle, gaps, κ_u, F_u. |
| `verify_weight.py` | Verifies a configuration file (`x y` per line). Reports the max angle, κ_u, F_u, and the distance of each gap/λ from an integer. |
| `sendov_s4_counterexample.py` | The explicit n = 3, u = 15/2 four-point set with F = 10, which beats Sendov's asserted s = 4 maximum of 9. |
| `sendov_s4_cfg_u10.txt` | n = 4 four-point set with F = 20 at u = 9.99, which beats Sendov's asserted 18. |
| `irreducible_search.c`, `deletion_check.py`, `irreducible_cfg_u8_s6.txt` | Search for, and exact check of, a configuration where deleting any single point lowers F (delete-one induction fails). |
| `kraft_partition_search.c` | Heuristic adversarial search for configurations with no arc-colouring Kraft certificate. |
| `direction_models.c` | Annealing over abstract direction matrices. Default: pseudo-configurations (triangle-consistent). `NOTRI=1`: local model with per-point angle bounds only. `SHOW=1` prints the best matrix. Usage as `weight_search`. |
| `verify_direction_matrix.py`, `local_model_cex_u8_s5.json` | Exact check of a direction matrix: antisymmetry, angle bound, triangle defect, κ, F. The JSON file is the local-model set with F = 12 > 10. |
| `cover_lemma.py` | Cover Lemma tests on GC-expanded local configurations and on realised real point sets. Reports the fraction of bad θ. |
| `kraft_exact.py`, `kraft_cfg_u7_s6.txt`, `kraft_cfg_u9_s7.txt` | Exhaustive enumeration over arc colourings (an LP per grouping) confirming that no certificate Σ 2^ν ≥ 2F exists for these sets. |

Build: `cc -O2 -o weight_search weight_search.c -lm`.

Python dependencies: `pip install mpmath numpy scipy`.
