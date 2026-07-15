From SimpleC.EE.CAV.ground_truth_p030_get_positive Require Import p030_get_positive_goal p030_get_positive_proof_auto p030_get_positive_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p030_get_positive_proof_auto.
  Include p030_get_positive_proof_manual.
End VC_Correctness.
