From SimpleC.EE.CAV.ground_truth_p024_largest_divisor Require Import p024_largest_divisor_goal p024_largest_divisor_proof_auto p024_largest_divisor_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p024_largest_divisor_proof_auto.
  Include p024_largest_divisor_proof_manual.
End VC_Correctness.
