import Garden.CnfRuns
import Garden.DirectRuns
/-! `lake env lean Axioms.lean` prints the axioms each main theorem depends on. reproduce.sh
requires every list to be within `propext`, `Classical.choice`, `Quot.sound` (a `sorry` would show
up as `sorryAx`, `native_decide` as `Lean.ofReduceBool`). -/
#print axioms CnfRuns.mod3_6_size_13
#print axioms CnfRuns.mod3_6_size_13_lists
#print axioms DirectRuns.mod3_6_size_13_direct
#print axioms Garden.LratDirect.check_sound
#print axioms Garden.LratDirect.scan_sound
#print axioms Garden.LratDirect.leaf_sound
#print axioms Mod3Tower.mod3_6_lower_sat
#print axioms Mod3Tower.mod3_2_6_lower_sat
#print axioms CnfSound.adm_sat
#print axioms Mod3Upper.mod3_1_upper
#print axioms Mod3Upper.mod3_2_upper
#print axioms CircuitDual.mod3_6_size_dual
#print axioms CnfRuns.cnf13_sat
