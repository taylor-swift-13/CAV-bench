From SimpleC.EE.CAV.ground_truth_p111_histogram Require Import p111_histogram_goal p111_histogram_proof_auto p111_histogram_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include string_strategy_proof.
  Include p111_histogram_proof_auto.
  Include p111_histogram_proof_manual.
End VC_Correctness.
