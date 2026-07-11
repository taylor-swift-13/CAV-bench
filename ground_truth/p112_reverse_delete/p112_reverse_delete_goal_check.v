From SimpleC.EE.CAV.ground_truth_p112_reverse_delete Require Import p112_reverse_delete_goal p112_reverse_delete_proof_auto p112_reverse_delete_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p112_reverse_delete_proof_auto.
  Include p112_reverse_delete_proof_manual.
End VC_Correctness.
