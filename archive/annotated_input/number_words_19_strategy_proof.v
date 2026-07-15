Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE Require Import number_words_19_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.coins_19.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma number_words_19_strategy1_correctness : number_words_19_strategy1.
  pre_process_default.
Admitted.

Lemma number_words_19_strategy2_correctness : number_words_19_strategy2.
  pre_process_default.
Admitted.

Lemma number_words_19_strategy3_correctness : number_words_19_strategy3.
  pre_process_default.
Admitted.

Lemma number_words_19_strategy7_correctness : number_words_19_strategy7.
  pre_process_default.
Admitted.

Lemma number_words_19_strategy4_correctness : number_words_19_strategy4.
  pre_process_default.
Admitted.

Lemma number_words_19_strategy5_correctness : number_words_19_strategy5.
  pre_process_default.
Admitted.

Lemma number_words_19_strategy6_correctness : number_words_19_strategy6.
  pre_process_default.
Admitted.

Lemma number_words_19_strategy8_correctness : number_words_19_strategy8.
  pre_process_default.
Admitted.
