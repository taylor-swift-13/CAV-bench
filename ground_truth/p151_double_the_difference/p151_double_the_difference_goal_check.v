From SimpleC.EE.CAV.ground_truth_p151_double_the_difference Require Import p151_double_the_difference_goal p151_double_the_difference_proof_auto p151_double_the_difference_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p151_double_the_difference_proof_auto.
  Include p151_double_the_difference_proof_manual.
End VC_Correctness.
