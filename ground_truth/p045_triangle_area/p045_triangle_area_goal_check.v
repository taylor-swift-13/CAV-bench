From SimpleC.EE.CAV.ground_truth_p045_triangle_area Require Import p045_triangle_area_goal p045_triangle_area_proof_auto p045_triangle_area_proof_manual.

Module VC_Correctness : VC_Correct.
  Include p045_triangle_area_proof_auto.
  Include p045_triangle_area_proof_manual.
End VC_Correctness.
