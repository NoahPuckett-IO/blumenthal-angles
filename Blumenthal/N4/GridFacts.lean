import Blumenthal.N4.GridDefs

/-!
Facts about the generated data, each checked by kernel evaluation (`decide +kernel`, no
`native_decide`). They are stated as Boolean checks; `GridMain` turns them into propositions.
-/

namespace Grid

def chkBasic : Bool :=
  gridMasks.length == 528 && gridOrbit.length == 528 && gridRotIdx.length == 528 &&
    gridToRep.length == 528 && gridReps.length == 12 &&
    gridMasks.all (· < 2 ^ 44) && gridOrbit.all (· < 12) && gridReps.all (· < 528) &&
    gridRotIdx.all (· < 528)

theorem chkBasic_eq : chkBasic = true := by decide +kernel

theorem masks_nodup : gridMasks.Nodup := by decide +kernel

/-- every parameter tuple of a valid string gives a mask in the list -/
def chkMem : Bool :=
  [true, false].all fun s => (List.range 22).all fun a => (List.range 22).all fun b =>
    (List.range 22).all fun c =>
      !(a + 5 ≤ b && b + 5 ≤ c && c + 5 ≤ a + 22) || gridMasks.contains (maskP s a b c)

theorem chkMem_eq : chkMem = true := by decide +kernel

/-- the adjacency rows are the compatibility rows, in chunks -/
def chkRows (lo n : Nat) : Bool :=
  (List.range' lo n).all fun i => adjTree.get (bitOf i) == packL (compat (mI i)) gridMasks 0

theorem chkRows0 : chkRows 0 66 = true := by decide +kernel
theorem chkRows1 : chkRows 66 66 = true := by decide +kernel
theorem chkRows2 : chkRows 132 66 = true := by decide +kernel
theorem chkRows3 : chkRows 198 66 = true := by decide +kernel
theorem chkRows4 : chkRows 264 66 = true := by decide +kernel
theorem chkRows5 : chkRows 330 66 = true := by decide +kernel
theorem chkRows6 : chkRows 396 66 = true := by decide +kernel
theorem chkRows7 : chkRows 462 66 = true := by decide +kernel

/-- rotation by one cell permutes the list and preserves orbit labels -/
def chkRot : Bool :=
  (List.range 528).all fun i => mI (rotI i) == rot1 (mI i) && orbI (rotI i) == orbI i

theorem chkRot_eq : chkRot = true := by decide +kernel

/-- `gridToRep[i]` rotations take vertex `i` to the representative of its orbit -/
def chkRep : Bool :=
  (List.range 528).all fun i => iterRot (gridToRep.getD i 0) i == repI (orbI i)

theorem chkRep_eq : chkRep = true := by decide +kernel

end Grid
