(** 

This file contains temporary definitions that will eventually
get merged into the various files from the TLC library. 

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
Require Import LibTactics LibLogic LibList.
Require LibListZ.
Generalizable Variables A B.  



(*----------------------*)
(* Nat *)

Require Import LibNat LibInt.


Section NatSimpl.
Open Scope nat_scope.
Implicit Types n : nat.

Lemma nat_zero_plus : forall n,
  0 + n = n.
Proof using. intros. math. Qed.

Lemma nat_plus_zero : forall n,
  n + 0 = n.
Proof using. intros. math. Qed.

Lemma nat_plus_succ : forall n1 n2,
  n1 + S n2 = S (n1 + n2).
Proof using. intros. math. Qed.
  
Lemma nat_minus_zero : forall n,
  n - 0 = n.
Proof using. intros. math. Qed.

Lemma nat_succ_minus_succ : forall n1 n2,
  S n1 - S n2 = n1 - n2.
Proof using. intros. math. Qed.

Lemma nat_minus_same : forall n,
  n - n = 0.
Proof using. intros. math. Qed.

Lemma nat_plus_minus_same : forall n1 n2,
  n1 + n2 - n1 = n2.
Proof using. intros. math. Qed.

End NatSimpl.

Hint Rewrite nat_zero_plus nat_plus_zero nat_plus_succ
  nat_minus_zero nat_succ_minus_succ
  nat_minus_same nat_plus_minus_same : rew_nat.




(*----------------------*)
(* ListExec *)

Require Import LibLogic. (* needed? *)
Require Import LibReflect.

(* TODO: LibListExec : is_not_nil *)
Definition is_not_nil A (l:list A) : bool :=
  match l with
  | nil => false
  | _ => true
  end.
  
Lemma is_not_nil_eq : forall A (l:list A),
  is_not_nil l = isTrue (l <> nil).
Proof.
  intros. destruct l; simpl; rew_bool_eq; auto_false.
Qed.

Lemma List_length_eq : forall A (l:list A),
  List.length l = LibList.length l.
Proof using. intros. induction l; simpl; rew_list; auto. Qed.


Lemma List_app_eq : forall A (L1 L2:list A),
  List.app L1 L2 = LibList.app L1 L2.
Proof using.
  intros. induction L1; simpl; rew_list; congruence.
Qed.

Lemma List_rev_eq : forall A (L:list A),
  List.rev L = LibList.rev L.
Proof using.
  intros. induction L; simpl; rew_list. { auto. } 
  { rewrite List_app_eq. congruence. }
Qed.

Lemma List_map_eq : forall A B (f:A->B) (L:list A),
  List.map f L = LibList.map f L.
Proof using.
  intros. induction L; simpl; rew_listx; congruence.
Qed.

Lemma List_combine_eq : forall A B (L1:list A) (L2:list B),
  length L1 = length L2 ->
  List.combine L1 L2 = LibList.combine L1 L2.
Proof using.
  introv E. gen L2. induction L1 as [|x1 L1']; intros.
  { auto. }
  { destruct L2 as [|x2 L2']. { false. }
    rew_list in E. simpl. fequals~. }
Qed.

(*  todo: reformulate without arguments *)



(*----------------------*)
(* Hint for LibListZ *)

Hint Rewrite LibListZ.length_map LibListZ.index_map_eq : rew_arr.


(*----------------------*)
(* Tactics *)

(* todo: generalize [intro_subst] *)

Ltac isbust_core tt :=
  match goal with |- forall _, _ = _ -> _ =>
    let X := fresh "TEMP" in
    let HX := fresh "E" X in
    intros X HX; subst X
  end.

Tactic Notation "isubst" :=
  isbust_core tt.


