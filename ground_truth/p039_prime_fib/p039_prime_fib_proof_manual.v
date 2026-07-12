Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import p039_prime_fib_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p039_prime_fib.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Import ListNotations.
Open Scope Z_scope.



Lemma pf_state_init : pf_state 0 2 3.
Proof.
  unfold pf_state.
  left.
  repeat split; lia.
Qed.

Lemma pf_state_sum_bound :
  forall count f1 f2,
    pf_state count f1 f2 ->
    0 <= f1 /\ 0 <= f2 /\ f1 + f2 <= 233.
Proof.
  intros count f1 f2 Hst.
  unfold pf_state in Hst.
  repeat (destruct Hst as [Hst | Hst]).
  all: destruct Hst as [? [? ?]]; subst; lia.
Qed.

Lemma pf_state_bounds :
  forall count f1 f2,
    pf_state count f1 f2 ->
    0 <= count /\ 2 <= f1 /\ f1 <= 89 /\ 3 <= f2 /\ f2 <= 144.
Proof.
  intros count f1 f2 Hst.
  unfold pf_state in Hst.
  repeat (destruct Hst as [Hst | Hst]).
  all: destruct Hst as [? [? ?]]; subst; lia.
Qed.

Lemma prime_candidate_mod_nonzero :
  forall f1 w,
    2 <= w ->
    w * w <= f1 ->
    (f1 = 2 \/ f1 = 3 \/ f1 = 5 \/ f1 = 13 \/ f1 = 89) ->
    Z.rem f1 w <> 0.
Proof.
  intros f1 w Hw Hsq Hprime.
  destruct Hprime as [-> | [-> | [-> | [-> | ->]]]].
  - lia.
  - lia.
  - assert (w = 2) by nia. subst w. simpl. discriminate.
  - assert (w = 2 \/ w = 3) by nia.
    destruct H as [-> | ->]; simpl; discriminate.
  - assert (w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9) by nia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      simpl; discriminate.
Qed.

Lemma pf_state_nonprime_step :
  forall count f1 f2,
    pf_state count f1 f2 ->
    f1 <> 2 ->
    f1 <> 3 ->
    f1 <> 5 ->
    f1 <> 13 ->
    f1 <> 89 ->
    pf_state count f2 (f1 + f2).
Proof.
  intros count f1 f2 Hst H2 H3 H5 H13 H89.
  unfold pf_state in *.
  destruct Hst as [[? [? ?]] | Hst].
  - subst. contradiction.
  - destruct Hst as [[? [? ?]] | Hst].
    + subst. contradiction.
    + destruct Hst as [[? [? ?]] | Hst].
      * subst. contradiction.
      * destruct Hst as [[? [? ?]] | Hst].
        -- subst. right. right. right. right. left. repeat split; lia.
        -- destruct Hst as [[? [? ?]] | Hst].
           ++ subst. contradiction.
           ++ destruct Hst as [[? [? ?]] | Hst].
              ** subst. right. right. right. right. right. right. left. repeat split; lia.
              ** destruct Hst as [[? [? ?]] | Hst].
                 --- subst. right. right. right. right. right. right. right. left. repeat split; lia.
                 --- destruct Hst as [[? [? ?]] | [? [? ?]]].
                     +++ subst. right. right. right. right. right. right. right. right. repeat split; lia.
                     +++ subst. contradiction.
Qed.

Lemma pf_state_prime_step :
  forall count f1 f2 n w,
    pf_state count f1 f2 ->
    2 <= w ->
    w * w > f1 ->
    (forall k : Z, 2 <= k /\ k < w -> Z.rem f1 k <> 0) ->
    count < n ->
    n <= 5 ->
    count + 1 <> n ->
    pf_state (count + 1) f2 (f1 + f2).
Proof.
  intros count f1 f2 n w Hst Hw Hexit Hnodiv Hcount Hn Hneq.
  unfold pf_state in Hst.
  destruct Hst as [[? [? ?]] | Hst].
  - subst. right. left. repeat split; lia.
  - destruct Hst as [[? [? ?]] | Hst].
    + subst. right. right. left. repeat split; lia.
    + destruct Hst as [[? [? ?]] | Hst].
      * subst. right. right. right. left. repeat split; lia.
      * destruct Hst as [[? [? ?]] | Hst].
        -- subst.
           assert (2 < w) by nia.
           assert (2 <= 2 /\ 2 < w) by nia.
           specialize (Hnodiv 2 H0).
           simpl in Hnodiv. contradiction.
        -- destruct Hst as [[? [? ?]] | Hst].
           ++ subst. right. right. right. right. right. left. repeat split; lia.
           ++ destruct Hst as [[? [? ?]] | Hst].
              ** subst.
                 assert (3 < w) by nia.
                 assert (2 <= 3 /\ 3 < w) by nia.
                 specialize (Hnodiv 3 H0).
                 simpl in Hnodiv. contradiction.
              ** destruct Hst as [[? [? ?]] | Hst].
                 --- subst.
                     assert (2 < w) by nia.
                     assert (2 <= 2 /\ 2 < w) by nia.
                     specialize (Hnodiv 2 H0).
                     simpl in Hnodiv. contradiction.
                 --- destruct Hst as [[? [? ?]] | [? [? ?]]].
                     +++ subst.
                         assert (5 < w) by nia.
                         assert (2 <= 5 /\ 5 < w) by nia.
                         specialize (Hnodiv 5 H0).
                         simpl in Hnodiv. contradiction.
                     +++ subst.
                         assert (n = 5) by lia.
                         subst n. contradiction.
Qed.

Lemma pf_state_prime_return :
  forall count f1 f2 n w,
    pf_state count f1 f2 ->
    2 <= w ->
    w * w > f1 ->
    (forall k : Z, 2 <= k /\ k < w -> Z.rem f1 k <> 0) ->
    count < n ->
    n <= 5 ->
    count + 1 = n ->
    prime_fib_spec n f1.
Proof.
  intros count f1 f2 n w Hst Hw Hexit Hnodiv Hcount Hn Heq.
  unfold pf_state in Hst.
  unfold prime_fib_spec.
  destruct Hst as [[? [? ?]] | Hst].
  - subst. left. repeat split; lia.
  - destruct Hst as [[? [? ?]] | Hst].
    + subst. right. left. repeat split; lia.
    + destruct Hst as [[? [? ?]] | Hst].
      * subst. right. right. left. repeat split; lia.
      * destruct Hst as [[? [? ?]] | Hst].
        -- subst.
           assert (2 < w) by nia.
           assert (2 <= 2 /\ 2 < w) by nia.
           specialize (Hnodiv 2 H0).
           simpl in Hnodiv. contradiction.
        -- destruct Hst as [[? [? ?]] | Hst].
           ++ subst. right. right. right. left. repeat split; lia.
           ++ destruct Hst as [[? [? ?]] | Hst].
              ** subst.
                 assert (3 < w) by nia.
                 assert (2 <= 3 /\ 3 < w) by nia.
                 specialize (Hnodiv 3 H0).
                 simpl in Hnodiv. contradiction.
              ** destruct Hst as [[? [? ?]] | Hst].
                 --- subst.
                     assert (2 < w) by nia.
                     assert (2 <= 2 /\ 2 < w) by nia.
                     specialize (Hnodiv 2 H0).
                     simpl in Hnodiv. contradiction.
                 --- destruct Hst as [[? [? ?]] | [? [? ?]]].
                     +++ subst.
                         assert (5 < w) by nia.
                         assert (2 <= 5 /\ 5 < w) by nia.
                         specialize (Hnodiv 5 H0).
                         simpl in Hnodiv. contradiction.
                     +++ subst. right. right. right. right. repeat split; lia.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Lemma proof_of_prime_fib_safety_wit_5 : prime_fib_safety_wit_5.
Proof.
  unfold prime_fib_safety_wit_5.
  left.
  intros.
  Intros.
  match goal with
  | H : pf_state _ _ _ |- _ =>
      pose proof (pf_state_sum_bound _ _ _ H)
  end.
  entailer!.
Qed.

Lemma proof_of_prime_fib_safety_wit_8 : prime_fib_safety_wit_8.
Proof.
  unfold prime_fib_safety_wit_8.
  left.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_prime_fib_entail_wit_1 : prime_fib_entail_wit_1.
Proof.
  unfold prime_fib_entail_wit_1.
  right.
  intros.
  Intros.
  entailer!.
  apply pf_state_init.
Qed.

Lemma proof_of_prime_fib_entail_wit_2 : prime_fib_entail_wit_2.
Proof.
  unfold prime_fib_entail_wit_2.
  right.
  intros.
  Intros.
  match goal with
  | H : pf_state _ _ _ |- _ =>
      pose proof (pf_state_bounds _ _ _ H)
  end.
  entailer!.
Qed.

Lemma proof_of_prime_fib_entail_wit_3 : prime_fib_entail_wit_3.
Proof.
  unfold prime_fib_entail_wit_3.
  right.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_1 : prime_fib_entail_wit_4_1.
Proof.
  unfold prime_fib_entail_wit_4_1.
  right.
  intros.
  Intros.
  entailer!.
  eapply (pf_state_prime_step count f1 f2 n_pre w); eauto.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_2 : prime_fib_entail_wit_4_2.
Proof.
  unfold prime_fib_entail_wit_4_2.
  right.
  intros.
  Intros.
  entailer!.
  match goal with
  | Hcond : ?i = 0 -> _, Hz : ?i = 0 |- _ =>
      pose proof (Hcond Hz) as Hneq;
      destruct Hneq as [[[[Hneq2 Hneq3] Hneq5] Hneq13] Hneq89]
  end.
  eapply (pf_state_nonprime_step count f1 f2); eauto.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_3 : prime_fib_entail_wit_4_3.
Proof.
  unfold prime_fib_entail_wit_4_3.
  right.
  intros.
  Intros.
  entailer!.
  assert (Hnotprime :
    ~ (f1 = 2 \/ f1 = 3 \/ f1 = 5 \/ f1 = 13 \/ f1 = 89)).
  { intro Hprime.
    pose proof (prime_candidate_mod_nonzero f1 w PreH6 PreH3 Hprime).
    contradiction. }
  eapply (pf_state_nonprime_step count f1 f2); eauto; tauto.
Qed.

Lemma proof_of_prime_fib_return_wit_1 : prime_fib_return_wit_1.
Proof.
  unfold prime_fib_return_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  match goal with
  | Hst : pf_state ?count ?f1 ?f2,
    Hall : (_ -> forall kk, _),
    Hnz : ?isprime <> 0,
    Hw : 2 <= ?w,
    Hexit : ?w * ?w > ?f1,
    Hcount : ?count < ?n,
    Hn : ?n <= 5,
    Heq : ?count + 1 = ?n |- _ =>
      eapply (pf_state_prime_return count f1 f2 n w); eauto;
      intros; apply (Hall Hnz); auto
  end.
Qed.
