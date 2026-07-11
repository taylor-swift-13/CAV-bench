From SimpleC.EE.CAV.ground_truth_p113_odd_count Require Import p113_odd_count_goal p113_odd_count_proof_auto p113_odd_count_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p113_odd_count_proof_auto.
  Include p113_odd_count_proof_manual.
End VC_Correctness.
