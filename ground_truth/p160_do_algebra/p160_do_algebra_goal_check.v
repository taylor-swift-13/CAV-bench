From SimpleC.EE.CAV.ground_truth_p160_do_algebra Require Import p160_do_algebra_goal p160_do_algebra_proof_auto p160_do_algebra_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include string_strategy_proof.
  Include p160_do_algebra_proof_auto.
  Include p160_do_algebra_proof_manual.
End VC_Correctness.
