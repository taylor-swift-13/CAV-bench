From SimpleC.EE.CAV.ground_truth_p101_words_string Require Import p101_words_string_goal p101_words_string_proof_auto p101_words_string_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p101_words_string_proof_auto.
  Include p101_words_string_proof_manual.
End VC_Correctness.
