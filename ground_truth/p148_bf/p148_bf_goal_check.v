From SimpleC.EE.CAV.ground_truth_p148_bf Require Import p148_bf_goal p148_bf_proof_auto p148_bf_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p148_bf_proof_auto.
  Include p148_bf_proof_manual.
End VC_Correctness.
