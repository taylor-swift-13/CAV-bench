From SimpleC.EE.CAV.ground_truth_p053_add Require Import p053_add_goal p053_add_proof_auto p053_add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p053_add_proof_auto.
  Include p053_add_proof_manual.
End VC_Correctness.
