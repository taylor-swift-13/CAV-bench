From SimpleC.EE.CAV.ground_truth_p057_monotonic Require Import p057_monotonic_goal p057_monotonic_proof_auto p057_monotonic_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p057_monotonic_proof_auto.
  Include p057_monotonic_proof_manual.
End VC_Correctness.
