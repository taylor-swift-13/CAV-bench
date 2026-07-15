From SimpleC.EE.CAV.ground_truth_p097_multiply Require Import p097_multiply_goal p097_multiply_proof_auto p097_multiply_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p097_multiply_proof_auto.
  Include p097_multiply_proof_manual.
End VC_Correctness.
