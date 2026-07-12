From SimpleC.EE.CAV.ground_truth_p125_split_words Require Import p125_split_words_goal p125_split_words_proof_auto p125_split_words_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p125_split_words_proof_auto.
  Include p125_split_words_proof_manual.
End VC_Correctness.
