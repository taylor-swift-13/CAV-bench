From SimpleC.EE.CAV.ground_truth_p060_sum_to_n Require Import p060_sum_to_n_goal p060_sum_to_n_proof_auto p060_sum_to_n_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p060_sum_to_n_proof_auto.
  Include p060_sum_to_n_proof_manual.
End VC_Correctness.
