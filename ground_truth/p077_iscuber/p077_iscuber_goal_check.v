From SimpleC.EE.CAV.ground_truth_p077_iscuber Require Import p077_iscuber_goal p077_iscuber_proof_auto p077_iscuber_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p077_iscuber_proof_auto.
  Include p077_iscuber_proof_manual.
End VC_Correctness.
