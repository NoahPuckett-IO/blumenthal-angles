# research/n4: generating the n = 4 data and certificates

None of the generated Lean files has to be trusted: `Blumenthal/N4/GridFacts.lean` checks every
fact used about the data, and `CaseCert0.lean` / `CaseCerts.lean` are checked by the kernel against
`Blumenthal/N4/Cert.lean`, whose soundness is `CertSound.checkCert_sound`. The scripts only make the
files reproducible. Each step below reproduces the committed file byte for byte.

```bash
cd research/n4
python3 sym_search.py --export                      # -> GridData.lean (528 strings, orbits, reps)
python3 gen_data.py GridData.lean .                 # -> GridSym.lean, AdjTree.lean
python3 extract_rows.py AdjTree.lean > rows.txt     # adjacency rows for the certificate generator
python3 emit_cases.py rows.txt GridData.lean        # -> CaseCert0.lean, CaseCerts.lean
```

Copy the outputs to `Blumenthal/N4/`. Each step takes under a minute.

| Script | Role |
|---|---|
| `sym_search.py` | Enumerates the 528 three-change strings on the (22, 5) grid, their compatibility graph and its 12 rotation orbits (44 each); counts the symmetry-reduced search (21 693 nodes with a static order); `--export` writes `GridData.lean` (vertices ordered by degree). |
| `gen_data.py` | Rotation permutation and rotations-to-representative (`GridSym.lean`); adjacency rows as a balanced tree (`AdjTree.lean`). |
| `gencert.py` | Branch-and-bound with greedy colouring by degree inside the candidate set; emits colour-class certificates (5 340 nodes for orbit 0, ≤ 6 for the others). |
| `emit_cases.py` | Writes the 12 certificate theorems. |
| `extract_rows.py` | Reads the rows back out of `AdjTree.lean`. |
