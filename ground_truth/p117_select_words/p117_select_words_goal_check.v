From SimpleC.EE.CAV.ground_truth_p117_select_words Require Import p117_select_words_goal p117_select_words_proof_auto p117_select_words_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p117_select_words_proof_auto.
  Include p117_select_words_proof_manual.
End VC_Correctness.
