import Blumenthal

/-! Axiom audit: every result below should depend only on `propext`, `Classical.choice`,
`Quot.sound`. Run with `lake env lean Audit.lean`. -/

#print axioms Blumenthal.le_alpha
#print axioms Blumenthal.alpha_le
#print axioms Blumenthal.alpha_le_of_approx
#print axioms Blumenthal.alpha_mono
#print axioms Blumenthal.sendovAnswer_iff
#print axioms Blumenthal.capacityBound_iff_sendovLower
#print axioms Blumenthal.sendovAnswer_iff_capacityBound_and_upper
