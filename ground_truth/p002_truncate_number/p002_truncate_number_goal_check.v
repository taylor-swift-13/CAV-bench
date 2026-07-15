From SimpleC.EE.CAV.ground_truth_p002_truncate_number Require Import p002_truncate_number_goal p002_truncate_number_proof_auto p002_truncate_number_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p002_truncate_number_proof_auto.
  Include p002_truncate_number_proof_manual.
End VC_Correctness.
