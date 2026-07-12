From SimpleC.EE.CAV.ground_truth_p039_prime_fib Require Import p039_prime_fib_goal p039_prime_fib_proof_auto p039_prime_fib_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p039_prime_fib_proof_auto.
  Include p039_prime_fib_proof_manual.
End VC_Correctness.
