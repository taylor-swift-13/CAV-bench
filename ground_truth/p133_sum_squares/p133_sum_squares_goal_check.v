From SimpleC.EE.CAV.ground_truth_p133_sum_squares Require Import p133_sum_squares_goal p133_sum_squares_proof_auto p133_sum_squares_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p133_sum_squares_proof_auto.
  Include p133_sum_squares_proof_manual.
End VC_Correctness.
