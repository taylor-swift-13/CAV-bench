From SimpleC.EE.CAV.ground_truth_p083_starts_one_ends Require Import p083_starts_one_ends_goal p083_starts_one_ends_proof_auto p083_starts_one_ends_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p083_starts_one_ends_proof_auto.
  Include p083_starts_one_ends_proof_manual.
End VC_Correctness.
