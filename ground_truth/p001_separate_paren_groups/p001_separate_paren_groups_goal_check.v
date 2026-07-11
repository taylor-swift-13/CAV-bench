From SimpleC.EE.CAV.ground_truth_p001_separate_paren_groups Require Import p001_separate_paren_groups_goal p001_separate_paren_groups_proof_auto p001_separate_paren_groups_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p001_separate_paren_groups_proof_auto.
  Include p001_separate_paren_groups_proof_manual.
End VC_Correctness.
