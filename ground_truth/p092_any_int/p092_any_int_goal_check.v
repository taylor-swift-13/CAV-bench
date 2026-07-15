From SimpleC.EE.CAV.ground_truth_p092_any_int Require Import p092_any_int_goal p092_any_int_proof_auto p092_any_int_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p092_any_int_proof_auto.
  Include p092_any_int_proof_manual.
End VC_Correctness.
