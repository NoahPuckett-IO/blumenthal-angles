import Blumenthal.N4.GridData
import Blumenthal.N4.GridSym
import Blumenthal.N4.AdjTree

/-!
Computational definitions for the (22, 5) grid (core Lean only, so that the heavy kernel
checks in `GridFacts` and `CaseCerts` can be compiled without Mathlib).
-/

namespace Grid

def M44 : Nat := 2 ^ 44 - 1

/-- rotate a 44-bit mask by one cell: bit `i` of the result is bit `i - 1 (mod 44)` -/
def rot1 (x : Nat) : Nat := ((x <<< 1) &&& M44) ||| (x >>> 43)

def hasWindow (d : Nat) : Bool :=
  let d1 := rot1 d
  let d2 := rot1 d1
  let d3 := rot1 d2
  let d4 := rot1 d3
  (d &&& d1 &&& d2 &&& d3 &&& d4) != 0

/-- compatibility of two masks: they differ on 5 cyclically consecutive cells -/
def compat (x y : Nat) : Bool := hasWindow (x ^^^ y)

/-- the value on cell `i` from the parameters: flip at every change point in `(0, i]` -/
def valP (s : Bool) (a b c i : Nat) : Bool :=
  let n := ([a, b, c, a + 22, b + 22, c + 22].filter fun p => 0 < p && p ≤ i).length
  xor s (n % 2 == 1)

/-- the mask with bit `i` equal to `f i`, for `i < n` -/
def maskUpTo (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => maskUpTo f n ||| (if f n then 2 ^ n else 0)

def maskP (s : Bool) (a b c : Nat) : Nat := maskUpTo (valP s a b c) 44

/-- vertex `i` (position in `gridMasks`) lives at bit `bitOf i` -/
def bitOf (i : Nat) : Nat := 527 - i

/-- set bit `bitOf (j0 + k)` iff `f (L[k])` -/
def packL (f : Nat → Bool) : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, j => (if f x then 2 ^ bitOf j else 0) ||| packL f xs (j + 1)

def mI (i : Nat) : Nat := gridMasks.getD i 0
def orbI (i : Nat) : Nat := gridOrbit.getD i 0
def repI (o : Nat) : Nat := gridReps.getD o 0
def rotI (i : Nat) : Nat := gridRotIdx.getD i 0

def iterRot : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => iterRot n (rotI i)

/-- candidate set of orbit case `o`: neighbours of the representative with orbit `≥ o` -/
def caseP (o : Nat) : Nat :=
  adjTree.get (bitOf (repI o)) &&& packL (fun x => decide (o ≤ x)) gridOrbit 0

end Grid
