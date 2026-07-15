From SimpleC.EE.CAV.ground_truth_p099_closest_integer Require Import p099_closest_integer_goal p099_closest_integer_proof_auto p099_closest_integer_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p099_closest_integer_proof_auto.
  Include p099_closest_integer_proof_manual.
End VC_Correctness.
