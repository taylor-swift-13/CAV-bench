(* def Strongest_Extension(class_name, extensions):
"""You will be given the name of a class (a string) and a list of extensions.
The extensions are to be used to load additional classes to the class. The
strength of the extension is as follows: Let CAP be the number of the uppercase
letters in the extension's name, and let SM be the number of lowercase letters
in the extension's name, the strength is given by the fraction CAP - SM.
You should find the strongest extension and return a string in this
format: ClassName.StrongestExtensionName.
If there are two or more extensions with the same strength, you should
choose the one that comes first in the list.
For example, if you are given "Slices" as the class and a list of the
extensions: ['SErviNGSliCes', 'Cheese', 'StuFfed'] then you should
return 'Slices.SErviNGSliCes' since 'SErviNGSliCes' is the strongest extension
(its strength is -1).

Definition problem_153_pre_z (class_l : list Z) (rows : list (list Z)) : Prop :=
  problem_153_pre (string_of_list_z_153 class_l) (rows_to_strings_z_153 rows).

Definition problem_153_spec_z
    (class_l : list Z) (rows : list (list Z)) (out_l : list Z) : Prop :=
  problem_153_spec
    (string_of_list_z_153 class_l)
    (rows_to_strings_z_153 rows)
    (string_of_list_z_153 out_l).

Definition is_upper_z_153 (c : Z) : bool :=
  Z.leb 65 c && Z.leb c 90.

Definition is_lower_z_153 (c : Z) : bool :=
  Z.leb 97 c && Z.leb c 122.

Definition char_strength_delta_153 (c : Z) : Z :=
  (if is_upper_z_153 c then 1 else 0) +
  (if is_lower_z_153 c then -1 else 0).

Fixpoint extension_strength_z (s : list Z) : Z :=
  match s with
  | [] => 0
  | c :: rest => char_strength_delta_153 c + extension_strength_z rest
  end.

Definition strength_scan_state_153 (s : list Z) (j strength : Z) : Prop :=
  0 <= j <= string_lib.string_length s /\
  strength = extension_strength_z (sublist 0 j s) /\
  - j <= strength <= j.

Definition best_prefix_state_153
    (rows : list (list Z)) (k best_idx max_strength : Z) : Prop :=
  0 < k <= Zlength rows /\
  0 <= best_idx < k /\
  max_strength =
    extension_strength_z (row_payload_z_153 (Znth best_idx rows nil)) /\
  (forall j,
     0 <= j < k ->
     extension_strength_z (row_payload_z_153 (Znth j rows nil)) <= max_strength) /\
  (forall j,
     0 <= j < k ->
     extension_strength_z (row_payload_z_153 (Znth j rows nil)) = max_strength ->
     best_idx <= j).

Definition output_payload_153 (class_l ext_l : list Z) : list Z :=
  class_l ++ [46] ++ ext_l.

Definition output_len_safe_153
    (class_l : list Z) (rows : list (list Z)) (n : Z) : Prop :=
  forall i,
    0 <= i < n ->
    string_lib.string_length class_l + row_len_z_153 (Znth i rows nil) + 2 < INT_MAX.

Definition rows_well_formed_153 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_153 row in
    row = string_lib.c_string payload /\
    string_lib.all_ascii payload /\
    string_lib.no_inner_nul payload /\
    string_lib.string_length payload <= 100 /\
    string_lib.string_length payload < INT_MAX.

Definition ascii_strength_delta_153 (c : ascii) : Z :=
  (if is_uppercase c then 1 else 0) +
  (if is_lowercase c then -1 else 0).
