From SimpleC.EE.CAV.ground_truth_p049_modp Require Import p049_modp_goal p049_modp_proof_auto p049_modp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p049_modp_proof_auto.
  Include p049_modp_proof_manual.
End VC_Correctness.
