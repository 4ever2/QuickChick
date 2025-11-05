(* Splittable randomness implemenation from the OCaml stdlib
   The OCaml implementation uses 64 bit integers, here we use the 63-bit primitive integers
   the 64bit mixing function is still used, it is unclear if using it with 63-bit integers
   still gives the same independence and distribution properties but it seems good enough for
   our usecase.
*)

From Coq Require Import Uint63.
From Coq Require Import Program.
From Coq Require Import ZArith.

Open Scope uint63_scope.

Record state := {
  a : int;
  s : int;
  x0 : int;
  x1 : int;
}.

Definition M := 5851342789287276437.
Definition M0 := 6537550379118437091.

Definition rotl x k :=
  (x << k) lor (x >> (64 - k)).

Definition next st :=
  (* Combining operation *)
  let z := st.(s) + st.(x0) in
  (* Mixing function *)
  let z := (z lxor (z >> 32)) * M0 in
  let z := (z lxor (z >> 32)) * M0 in
  let z := (z lxor (z >> 32)) in
  (* LCG update *)
  let s' := st.(s) * M + st.(a) in
  (* XBG update *)
  let q0 := st.(x0) in
  let q1 := st.(x1) in
  let q1 := q1 lxor q0 in
  let q0 := rotl q0 24 in
  let q0 := q0 lxor q1 lxor (q1 << 16) in
  let q1 := rotl q1 37 in

  (* return result *)
  ({| a := st.(a); s := s'; x0 := q0; x1 := q1 |}, z).

Definition max_int31 := 1073741823.
Definition max_int32 := (1 << 31) - 1.

Definition bits st :=
  let (st, x) := next st in
  (st, x land max_int31).

Definition bits64 st :=
  next st.

Definition mk i1 i2 i3 i4 := {|
    a := (i1 lor 1);
    s := i2;
    x0 := (if i3 =? 0 then 1 else i3);
    x1 := (if i4 =? 0 then 2 else i4);
  |}.

Definition split st :=
  let (st, i1) := bits64 st in
  let (st, i2) := bits64 st in
  let (st, i3) := bits64 st in
  let (st, i4) := bits64 st in
  (st, mk i1 i2 i3 i4).

(* TOOD: init from single seed *)
Definition init s1 s2 s3 s4 := {|
    a := s1;
    s := s2;
    x0 := s3;
    x1 := s4;
  |}.

(* TODO: we hardcode a seed for now, ideally the seed should come from the plugin *)
Definition make_self_init : unit -> state :=
  fun _ => init
    6196874289567705097
    586573249833713189
    8591268803865043407
    6388613595849772044.

Definition g_bool st :=
  let (st, i) := next st in
  (st, (i land 1) =? 0).

From Coq Require Import Program.

#[bypass_check(guard)]
Program Fixpoint int_aux st n mask {measure (Z.to_nat (to_Z n))}  :=
  let (st, i) := next st in
  let r := i land mask in
  let v := r mod n in
  if mask - n +1 <? r -v
  then int_aux st n mask
  else (st, v).
Next Obligation. Admitted.

Definition g_int st bound :=
  (* We assume bound is valid since we cannot throw an exception *)
  int_aux st bound max_int31.

Definition g_full_int st bound :=
  int_aux st bound (if bound <=? max_int31 then max_int31
                    else if bound <=? max_int32 then max_int32
                    else max_int).


Section QC.
  Lemma state_inhabited : inhabited state.
  Proof.
    constructor.
    exact (LMXRandom.make_self_init tt).
  Qed.

  Definition randomNext (st: state) : Z * state :=
    let (st, i) := bits st in
    (to_Z i, st).

  Definition mkRandomSeed (i : Z) : state :=
    let i := of_Z i in
    init i i i i.

  Definition newRandomSeed : state :=
    make_self_init ().

  Definition randomSplit (st : state) : state * state :=
    split st.

  Definition randomRBool : bool * bool -> state -> bool * state :=
    (fun _ r => let (st, b) := g_bool r in (b, st)).

  Definition randomRNat : nat * nat -> state -> nat * state :=
    (fun '(x,y) r =>
    let (st, i) := g_full_int r (of_Z (Z.of_nat (y - x + 1))) in
    (x + (Z.to_nat (to_Z i)),st))%nat.

  Definition randomRInt : Z * Z -> state -> Z * state :=
    (fun '(x,y) r =>
    let (st, i) := g_int r (of_Z (y - x + 1)) in
    (x + (to_Z i), st))%Z.

  Definition randomRN : N * N -> state -> N * state :=
    (fun '(x,y) r =>
    let (st, i) := g_int r (of_Z (Z.of_N (y - x + 1))) in
    (x + (Z.to_N (to_Z i)), st))%N.
End QC.
