From SimpleC.EE.CAV.ground_truth_p062_derivative Require Import p062_derivative_goal p062_derivative_proof_auto p062_derivative_proof_manual.

Module VC_Correctness : VC_Correct.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include p062_derivative_proof_auto.
  Include p062_derivative_proof_manual.
End VC_Correctness.
