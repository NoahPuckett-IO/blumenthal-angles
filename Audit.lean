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
#print axioms Blumenthal.card_le_two_pow_of_anglesLE
#print axioms Blumenthal.capacityBound_even
#print axioms Blumenthal.le_alpha_of_two_pow_lt
#print axioms Blumenthal.alpha_le_of_construction
#print axioms Blumenthal.alpha_two_pow_le
#print axioms Blumenthal.alpha_three_le
#print axioms Blumenthal.alpha_three
#print axioms Blumenthal.alpha_lower_band_le
#print axioms Blumenthal.sendovUpper
