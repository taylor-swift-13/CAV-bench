From SimpleC.EE.CAV.ground_truth_p162_string_to_md5 Require Import p162_string_to_md5_goal p162_string_to_md5_proof_auto p162_string_to_md5_proof_manual.

Module VC_Correctness : VC_Correct.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p162_string_to_md5_proof_auto.
  Include p162_string_to_md5_proof_manual.
End VC_Correctness.
