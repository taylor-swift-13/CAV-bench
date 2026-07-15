From SimpleC.EE.CAV.ground_truth_p071_triangle_area Require Import p071_triangle_area_goal p071_triangle_area_proof_auto p071_triangle_area_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p071_triangle_area_proof_auto.
  Include p071_triangle_area_proof_manual.
End VC_Correctness.
