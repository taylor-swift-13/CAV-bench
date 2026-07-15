From SimpleC.EE.CAV.ground_truth_p035_max_element Require Import p035_max_element_goal p035_max_element_proof_auto p035_max_element_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p035_max_element_proof_auto.
  Include p035_max_element_proof_manual.
End VC_Correctness.
