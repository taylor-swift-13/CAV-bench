(* def get_max_triples(n):
You are given a positive integer n. You have to create an integer array a of length n.
For each i (1 ≤ i ≤ n), the value of a[i] = i * i - i + 1.
Return the number of triples (a[i], a[j], a[k]) of a where i < j < k,
and a[i] + a[j] + a[k] is a multiple of 3.

Definition triple_nat_147 := (nat * nat * nat)%type.

Fixpoint triples_k_list_aux_147 (n i j : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_k_list_aux_147 n i j fuel' in
      let k := j + 1 + Z.of_nat fuel' in
      if triple_good_bool_147 i j k
      then prev ++ (Z.to_nat i, Z.to_nat j, Z.to_nat k) :: nil
      else prev
  end.

Fixpoint triples_j_list_aux_147 (n i : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_j_list_aux_147 n i fuel' in
      let j := i + 1 + Z.of_nat fuel' in
      prev ++ triples_k_list_aux_147 n i j (Z.to_nat (n + 1 - (j + 1)))
  end.

Fixpoint triples_i_list_aux_147 (n : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_i_list_aux_147 n fuel' in
      let i := 1 + Z.of_nat fuel' in
      prev ++ triples_j_list_aux_147 n i (Z.to_nat (n + 1 - (i + 1)))
  end.

Definition triples_list_147 (n : Z) : list triple_nat_147 :=
  triples_i_list_aux_147 n (Z.to_nat n).
