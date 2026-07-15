(*
  Definition-only MD5 specification for HumanEval problem 162.
  The digest function below follows RFC 1321: byte padding, 64 compression
  rounds per block, little-endian state serialization, and lowercase hex.
*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope N_scope.

Definition md5_mask32 : N := 0xffffffff.
Definition md5_u32 (x : N) : N := N.land x md5_mask32.
Definition md5_not32 (x : N) : N := N.lxor (md5_u32 x) md5_mask32.
Definition md5_add (x y : N) : N := md5_u32 (x + y).
Definition md5_add4 (a b c d : N) : N := md5_u32 (a + b + c + d).

Definition md5_rotl (x : N) (s : nat) : N :=
  let k := N.of_nat s in
  let r := N.of_nat (32 - s) in
  md5_u32 (N.lor (N.shiftl (md5_u32 x) k)
                 (N.shiftr (md5_u32 x) r)).

Local Close Scope N_scope.
Definition md5_shifts : list nat :=
  [7;12;17;22; 7;12;17;22; 7;12;17;22; 7;12;17;22;
   5;9;14;20; 5;9;14;20; 5;9;14;20; 5;9;14;20;
   4;11;16;23; 4;11;16;23; 4;11;16;23; 4;11;16;23;
   6;10;15;21; 6;10;15;21; 6;10;15;21; 6;10;15;21].
Local Open Scope N_scope.

Definition md5_constants : list N :=
  [0xd76aa478;0xe8c7b756;0x242070db;0xc1bdceee;
   0xf57c0faf;0x4787c62a;0xa8304613;0xfd469501;
   0x698098d8;0x8b44f7af;0xffff5bb1;0x895cd7be;
   0x6b901122;0xfd987193;0xa679438e;0x49b40821;
   0xf61e2562;0xc040b340;0x265e5a51;0xe9b6c7aa;
   0xd62f105d;0x02441453;0xd8a1e681;0xe7d3fbc8;
   0x21e1cde6;0xc33707d6;0xf4d50d87;0x455a14ed;
   0xa9e3e905;0xfcefa3f8;0x676f02d9;0x8d2a4c8a;
   0xfffa3942;0x8771f681;0x6d9d6122;0xfde5380c;
   0xa4beea44;0x4bdecfa9;0xf6bb4b60;0xbebfbc70;
   0x289b7ec6;0xeaa127fa;0xd4ef3085;0x04881d05;
   0xd9d4d039;0xe6db99e5;0x1fa27cf8;0xc4ac5665;
   0xf4292244;0x432aff97;0xab9423a7;0xfc93a039;
   0x655b59c3;0x8f0ccc92;0xffeff47d;0x85845dd1;
   0x6fa87e4f;0xfe2ce6e0;0xa3014314;0x4e0811a1;
   0xf7537e82;0xbd3af235;0x2ad7d2bb;0xeb86d391].

Definition md5_byte (bytes : list N) (i : nat) : N :=
  N.land (nth i bytes 0) 255.

Definition md5_word_le (bytes : list N) (i : nat) : N :=
  md5_u32
    (md5_byte bytes (4*i) +
     N.shiftl (md5_byte bytes (4*i+1)) 8 +
     N.shiftl (md5_byte bytes (4*i+2)) 16 +
     N.shiftl (md5_byte bytes (4*i+3)) 24).

Definition md5_words (block : list N) : list N :=
  map (md5_word_le block) (seq 0 16).

Record md5_state : Type := {
  md5_a : N;
  md5_b : N;
  md5_c : N;
  md5_d : N
}.

Definition md5_initial : md5_state :=
  {| md5_a := 0x67452301;
     md5_b := 0xefcdab89;
     md5_c := 0x98badcfe;
     md5_d := 0x10325476 |}.

Definition md5_fg (i : nat) (b c d : N) : N * nat :=
  if Nat.ltb i 16 then
    (md5_u32 (N.lor (N.land b c) (N.land (md5_not32 b) d)), i)
  else if Nat.ltb i 32 then
    (md5_u32 (N.lor (N.land d b) (N.land (md5_not32 d) c)),
     ((5*i+1) mod 16)%nat)
  else if Nat.ltb i 48 then
    (md5_u32 (N.lxor b (N.lxor c d)), ((3*i+5) mod 16)%nat)
  else
    (md5_u32 (N.lxor c (N.lor b (md5_not32 d))), ((7*i) mod 16)%nat).

Fixpoint md5_rounds
    (fuel i : nat) (a b c d : N) (words : list N)
    : md5_state :=
  match fuel with
  | O => {| md5_a := a; md5_b := b; md5_c := c; md5_d := d |}
  | S fuel' =>
      let '(f, g) := md5_fg i b c d in
      let mixed := md5_add4 a f (nth i md5_constants 0)
                                  (nth g words 0) in
      let next_b := md5_add b (md5_rotl mixed (nth i md5_shifts 0%nat)) in
      md5_rounds fuel' (S i) d next_b b c words
  end.

Definition md5_compress (st : md5_state) (block : list N) : md5_state :=
  let r := md5_rounds 64 0 (md5_a st) (md5_b st)
                              (md5_c st) (md5_d st) (md5_words block) in
  {| md5_a := md5_add (md5_a st) (md5_a r);
     md5_b := md5_add (md5_b st) (md5_b r);
     md5_c := md5_add (md5_c st) (md5_c r);
     md5_d := md5_add (md5_d st) (md5_d r) |}.

Fixpoint md5_process_blocks
    (fuel : nat) (bytes : list N) (st : md5_state) : md5_state :=
  match fuel with
  | O => st
  | S fuel' =>
      md5_process_blocks fuel' (skipn 64 bytes)
        (md5_compress st (firstn 64 bytes))
  end.

Definition md5_length_bytes (bit_length : N) : list N :=
  [N.land bit_length 255;
   N.land (N.shiftr bit_length 8) 255;
   N.land (N.shiftr bit_length 16) 255;
   N.land (N.shiftr bit_length 24) 255;
   N.land (N.shiftr bit_length 32) 255;
   N.land (N.shiftr bit_length 40) 255;
   N.land (N.shiftr bit_length 48) 255;
   N.land (N.shiftr bit_length 56) 255].

Definition md5_pad (bytes : list N) : list N :=
  let n := length bytes in
  let zero_count := ((56 + 64 - ((n + 1) mod 64)) mod 64)%nat in
  bytes ++ [128] ++ repeat 0 zero_count ++
  md5_length_bytes (N.of_nat n * 8).

Definition md5_word_bytes (w : N) : list N :=
  [N.land w 255;
   N.land (N.shiftr w 8) 255;
   N.land (N.shiftr w 16) 255;
   N.land (N.shiftr w 24) 255].

Definition md5_digest_bytes (bytes : list N) : list N :=
  let padded := md5_pad bytes in
  let st := md5_process_blocks ((length padded / 64)%nat) padded md5_initial in
  md5_word_bytes (md5_a st) ++ md5_word_bytes (md5_b st) ++
  md5_word_bytes (md5_c st) ++ md5_word_bytes (md5_d st).

Definition md5_hex_digit (n : N) : Z :=
  if N.ltb n 10 then Z.of_N (48 + n) else Z.of_N (87 + n).

Definition md5_byte_hex (b : N) : list Z :=
  [md5_hex_digit (N.shiftr b 4); md5_hex_digit (N.land b 15)].

Definition md5_digest_z (input : list Z) : list Z :=
  map Z.of_N
    (md5_digest_bytes (map (fun z => N.land (Z.to_N z) 255) input)).

Local Open Scope Z_scope.
Definition md5_hex_digit_z (n : Z) : Z :=
  if n <? 10 then 48 + n else 87 + n.

Definition md5_byte_hex_z (b : Z) : list Z :=
  [md5_hex_digit_z (b / 16); md5_hex_digit_z (b mod 16)].

Definition md5_hex_z (input : list Z) : list Z :=
  concat (map md5_byte_hex_z (md5_digest_z input)).

Definition md5_digest_ok_z (input : list Z) : Prop :=
  Zlength (md5_digest_z input) = 16 /\
  forall k, 0 <= k < 16 ->
    let b := Znth k (md5_digest_z input) 0 in
    ((((0 <= b < 256 /\ 0 <= b / 16) /\ b / 16 < 16) /\
       0 <= b mod 16) /\ b mod 16 < 16).

Definition md5_hex_prefix_z
    (digest : list Z) (i : Z) (output : list Z) : Prop :=
  output = concat (map md5_byte_hex_z (firstn (Z.to_nat i) digest)).

Definition problem_162_pre_z (input : list Z) : Prop :=
  Forall (fun z => (0 < z <= 255)%Z) input.

Definition problem_162_spec_z (input output : list Z) : Prop :=
  match input with
  | [] => output = [78; 111; 110; 101]%Z
  | _ :: _ => output = md5_hex_z input
  end.
