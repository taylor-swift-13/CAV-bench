From SimpleC.EE.CAV.ground_truth_p153_Strongest_Extension Require Import p153_Strongest_Extension_goal p153_Strongest_Extension_proof_auto p153_Strongest_Extension_proof_manual.

Module VC_Correctness : VC_Correct.
  Include ptr_array2_strategy_proof.
  Include char_array_strategy_proof.
  Include string_strategy_proof.
  Include p153_Strongest_Extension_proof_auto.
  Include p153_Strongest_Extension_proof_manual.
End VC_Correctness.
