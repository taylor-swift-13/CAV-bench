From SimpleC.EE.CAV.ground_truth_p149_sorted_list_sum Require Import p149_sorted_list_sum_goal p149_sorted_list_sum_proof_auto p149_sorted_list_sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p149_sorted_list_sum_proof_auto.
  Include p149_sorted_list_sum_proof_manual.
End VC_Correctness.
