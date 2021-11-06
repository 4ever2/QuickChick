From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import Arith List String Lia.
From QuickChick Require Import QuickChick.
Import ListNotations.

(* Types *)

Inductive type : Type :=
| N : type
| Arrow : type -> type -> type.

Derive (Arbitrary, Show, EnumSized) for type.
Instance dec_type (t1 t2 : type) : Dec (t1 = t2).
Proof. dec_eq. Defined.

(* Terms *)

Definition var := nat.

Inductive term : Type :=
| Const : nat -> term
| Id : var -> term
| App : term -> term -> term
| Abs : term -> term.

(* Environments *)

Definition env := list type.

Inductive bind : env -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.

(* Generate variables of a specific type in an env. *)
Derive ArbitrarySizedSuchThat for (fun x => bind env x tau).
(* Get the type of a given variable in an env. *)
Derive EnumSizedSuchThat for (fun tau => bind env x tau).
(* Check whether a variable has a given type in an env. *)
Derive DecOpt for (bind env t tau).

(* Typing *)

Inductive typing (e : env) : term -> type -> Prop :=
| TId :
    forall x tau,
      bind e x tau ->
      typing e (Id x) tau
| TConst :
    forall n,
      typing e (Const n) N
| TAbs :
    forall t tau1 tau2,
      typing (tau1 :: e) t tau2 ->
      typing e (Abs t) (Arrow tau1 tau2)
| TApp :
    forall t1 t2 tau1 tau2,
      typing e t2 tau1 ->
      typing e t1 (Arrow tau1 tau2) ->
      typing e (App t1 t2) tau2.

(* Generate terms of a specific type in an env. *)
Derive ArbitrarySizedSuchThat for (fun t => typing env t tau).

Derive EnumSizedSuchThat for (fun tau => typing env t tau).



(* Check whether a variable has a given type in an env. *)
Derive DecOpt for (typing env t tau).



(* Legacy. Printing. *)
(*
Open Scope string.

Fixpoint show_type (tau : type) :=
  match tau with
    | N => "Nat"
    | Arrow tau1 tau2 =>
      "(" ++ show_type tau1 ++ " -> " ++ show_type tau2 ++ ")"
  end.

Instance showType : Show type := { show := show_type }.

Fixpoint show_term (t : term) :=
  match t with
    | Const n => show n
    | Id x => "Id" ++ show x
    | App t1 t2 => "(" ++ show_term t1 ++ " " ++ show_term t2 ++ ")"
    | Abs t => "λ.(" ++ show_term t ++ ")"
  end.

Close Scope string.

Instance showTerm : Show term := { show := show_term }.
*)
