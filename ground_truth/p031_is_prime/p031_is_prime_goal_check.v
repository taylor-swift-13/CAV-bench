From SimpleC.EE.CAV.ground_truth_p031_is_prime Require Import p031_is_prime_goal p031_is_prime_proof_auto p031_is_prime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p031_is_prime_proof_auto.
  Include p031_is_prime_proof_manual.
End VC_Correctness.
