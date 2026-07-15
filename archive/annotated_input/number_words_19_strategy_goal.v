Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.coins_19.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition number_words_19_strategy1 :=
  forall (w8 : Z) (w6 : Z) (w4 : Z) (w2 : Z) (w0 : Z) (words : Z) (w1 : Z) (w3 : Z) (w5 : Z) (w7 : Z) (w9 : Z),
    TT &&
    emp **
    ((PtrArray.full words 10 (@cons Z w0 (@cons Z w1 (@cons Z w2 (@cons Z w3 (@cons Z w4 (@cons Z w5 (@cons Z w6 (@cons Z w7 (@cons Z w8 (@cons Z w9 (@nil Z))))))))))))) **
    ((CharArray.full w0 (Z.add ( number_word_len_z 0) 1) (@app Z ( number_word_z 0) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w1 (Z.add ( number_word_len_z 1) 1) (@app Z ( number_word_z 1) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w2 (Z.add ( number_word_len_z 2) 1) (@app Z ( number_word_z 2) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w3 (Z.add ( number_word_len_z 3) 1) (@app Z ( number_word_z 3) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w4 (Z.add ( number_word_len_z 4) 1) (@app Z ( number_word_z 4) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w5 (Z.add ( number_word_len_z 5) 1) (@app Z ( number_word_z 5) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w6 (Z.add ( number_word_len_z 6) 1) (@app Z ( number_word_z 6) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w7 (Z.add ( number_word_len_z 7) 1) (@app Z ( number_word_z 7) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w8 (Z.add ( number_word_len_z 8) 1) (@app Z ( number_word_z 8) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w9 (Z.add ( number_word_len_z 9) 1) (@app Z ( number_word_z 9) (@cons Z 0 (@nil Z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9))
    ).

Definition number_words_19_strategy2 :=
  forall (d : Z) (words : Z) (w1 : Z) (w3 : Z) (w5 : Z) (w7 : Z) (w9 : Z) (w8 : Z) (w6 : Z) (w4 : Z) (w2 : Z) (w0 : Z),
    TT &&
    (coq_prop (Z.le 0 d)) &&
    (coq_prop (Z.lt d 10)) &&
    emp **
    ((number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9))
    |--
    (
    TT &&
    emp **
    ((number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9))
    ) ** (
    ALL (v : Z),
      TT &&
      (coq_prop (v = (@Znth Z d (@cons Z w0 (@cons Z w1 (@cons Z w2 (@cons Z w3 (@cons Z w4 (@cons Z w5 (@cons Z w6 (@cons Z w7 (@cons Z w8 (@cons Z w9 (@nil Z))))))))))) 0))) &&
      emp -*
      TT &&
      emp **
      ((poly_store FET_ptr (Z.add words (Z.mul d (@sizeof_front_end_type FET_ptr))) v))
      ).

Definition number_words_19_strategy3 :=
  forall (word : Z) (d : Z) (w0 : Z) (w1 : Z) (w2 : Z) (w3 : Z) (w4 : Z) (w5 : Z) (w6 : Z) (w7 : Z) (w8 : Z) (w9 : Z) (words : Z),
    TT &&
    (coq_prop (Z.le 0 d)) &&
    (coq_prop (Z.lt d 10)) &&
    (coq_prop (word = (@Znth Z d (@cons Z w0 (@cons Z w1 (@cons Z w2 (@cons Z w3 (@cons Z w4 (@cons Z w5 (@cons Z w6 (@cons Z w7 (@cons Z w8 (@cons Z w9 (@nil Z))))))))))) 0))) &&
    emp **
    ((number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9))
    |--
    (
    TT &&
    emp **
    ((number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray.full word (Z.add ( number_word_len_z d) 1) (@app Z ( number_word_z d) (@cons Z 0 (@nil Z)))))
    ).

Definition number_words_19_strategy7 :=
  forall (words : Z) (w1 : Z) (w3 : Z) (w5 : Z) (w7 : Z) (w9 : Z) (w8 : Z) (w6 : Z) (w4 : Z) (w2 : Z) (w0 : Z),
    TT &&
    emp **
    ((number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((PtrArray.full words 10 (@cons Z w0 (@cons Z w1 (@cons Z w2 (@cons Z w3 (@cons Z w4 (@cons Z w5 (@cons Z w6 (@cons Z w7 (@cons Z w8 (@cons Z w9 (@nil Z))))))))))))) **
    ((CharArray.full w0 5 (@app Z ( number_word_z 0) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w1 4 (@app Z ( number_word_z 1) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w2 4 (@app Z ( number_word_z 2) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w3 6 (@app Z ( number_word_z 3) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w4 5 (@app Z ( number_word_z 4) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w5 5 (@app Z ( number_word_z 5) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w6 4 (@app Z ( number_word_z 6) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w7 6 (@app Z ( number_word_z 7) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w8 6 (@app Z ( number_word_z 8) (@cons Z 0 (@nil Z))))) **
    ((CharArray.full w9 5 (@app Z ( number_word_z 9) (@cons Z 0 (@nil Z)))))
    ).

Definition number_words_19_strategy4 :=
  forall (d : Z) (w0 : Z) (w2 : Z) (w4 : Z) (w6 : Z) (w8 : Z) (w9 : Z) (w7 : Z) (w5 : Z) (w3 : Z) (w1 : Z) (words : Z) (word : Z),
    TT &&
    (coq_prop (Z.le 0 d)) &&
    (coq_prop (Z.lt d 10)) &&
    emp **
    ((number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)) **
    ((CharArray.full word (Z.add ( number_word_len_z d) 1) (@app Z ( number_word_z d) (@cons Z 0 (@nil Z)))))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9))
    ).

Definition number_words_19_strategy5 :=
  forall (n1 : Z) (n2 : Z) (p : Z) (l1 : (@list Z)),
    TT &&
    (coq_prop (n1 = n2)) &&
    emp **
    ((CharArray.full p n1 l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Z)),
      TT &&
      (coq_prop (l1 = l2)) &&
      emp -*
      TT &&
      emp **
      ((CharArray.full p n2 l2))
      ).

Definition number_words_19_strategy6 :=
  forall (l1 : Z) (l2 : Z) (p : Z) (r : Z),
    TT &&
    (coq_prop (l1 = l2)) &&
    emp **
    ((CharArray.undef_seg p l1 r))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((CharArray.undef_seg p l2 r))
    ).

Definition number_words_19_strategy8 :=
  forall (p : Z) (x : Z),
    TT &&
    emp **
    ((CharArray.undef_seg p x x))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Module Type number_words_19_Strategy_Correct.

  Axiom number_words_19_strategy1_correctness : number_words_19_strategy1.
  Axiom number_words_19_strategy2_correctness : number_words_19_strategy2.
  Axiom number_words_19_strategy3_correctness : number_words_19_strategy3.
  Axiom number_words_19_strategy7_correctness : number_words_19_strategy7.
  Axiom number_words_19_strategy4_correctness : number_words_19_strategy4.
  Axiom number_words_19_strategy5_correctness : number_words_19_strategy5.
  Axiom number_words_19_strategy6_correctness : number_words_19_strategy6.
  Axiom number_words_19_strategy8_correctness : number_words_19_strategy8.

End number_words_19_Strategy_Correct.
