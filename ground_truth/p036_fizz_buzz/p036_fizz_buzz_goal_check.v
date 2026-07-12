From SimpleC.EE.CAV.ground_truth_p036_fizz_buzz Require Import p036_fizz_buzz_goal p036_fizz_buzz_proof_auto p036_fizz_buzz_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p036_fizz_buzz_proof_auto.
  Include p036_fizz_buzz_proof_manual.
End VC_Correctness.
