(** 

This file describes the syntax and semantics of a lambda calculus 
with mutable heap. The language includes recursive functions, and a 
couple of primitive functions. Records and arrays operations are 
encoded using pointer arithmetics, and using the [alloc] operation
which allocates at once a requested number of consecutive memory cells.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
Require Export LibCore.
Require Export Fmap TLCbuffer.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Source language syntax *)

(* ---------------------------------------------------------------------- *)
(** Representation of variables and locations *)

Definition var := nat.
Definition loc := nat.
Definition null : loc := 0%nat.
Definition field := nat.

Definition eq_var_dec := Nat.eq_dec.

Global Opaque field var loc.


(* ---------------------------------------------------------------------- *)
(** Syntax of the source language *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_alloc : prim
  | val_eq : prim
  | val_sub : prim
  | val_add : prim
  | val_ptr_add : prim.

Inductive val : Type := 
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> trm -> trm -> trm -> trm.

(** The type of values is inhabited *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.


(* ---------------------------------------------------------------------- *)
(** Coercions *)

Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Source language semantics *)

(* ---------------------------------------------------------------------- *)
(** Definition of capture-avoiding substitution *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let aux_no_capture x t := if eq_var_dec x y then t else aux t in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if eq_var_dec x y then trm_val w else t
  | trm_fun x t1 => trm_fun x (aux_no_capture x t1)
  | trm_fix f x t1 => trm_fix f x (if eq_var_dec f y then t1 else 
                                   aux_no_capture x t1)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (aux_no_capture x t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  end.


(* ---------------------------------------------------------------------- *)
(** Big-step evaluation *)

Section Red.

Definition state := fmap loc val.

Local Open Scope fmap_scope.

Implicit Types t : trm.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types i : field.
Implicit Types b : bool.
Implicit Types n : int.

Inductive red : state -> trm -> state -> val -> Prop :=
  | red_val : forall m v,
      red m v m v
  | red_fun : forall m x t1,
      red m (trm_fun x t1) m (val_fun x t1)
  | red_fix : forall m f x t1,
      red m (trm_fix f x t1) m (val_fix f x t1)
  | red_if : forall m1 m2 m3 b r t0 t1 t2,
      red m1 t0 m2 (val_bool b) ->
      red m2 (if b then t1 else t2) m3 r ->
      red m1 (trm_if t0 t1 t2) m3 r
  | red_seq : forall m1 m2 m3 t1 t2 r,
      red m1 t1 m2 val_unit ->
      red m2 t2 m3 r ->
      red m1 (trm_seq t1 t2) m3 r
  | red_let : forall m1 m2 m3 x t1 t2 v1 r,
      red m1 t1 m2 v1 ->
      red m2 (subst x v1 t2) m3 r ->
      red m1 (trm_let x t1 t2) m3 r
  | red_app_arg : forall m1 m2 m3 m4 t1 t2 v1 v2 r,
      (* TODO: add [not_is_val t1 \/ not_is_val t2] *)
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_app v1 v2) m4 r ->
      red m1 (trm_app t1 t2) m4 r
  | red_app_fun : forall m1 m2 v1 v2 x t r,
      v1 = val_fun x t ->
      red m1 (subst x v2 t) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_app_fix : forall m1 m2 v1 v2 f x t r,
      v1 = val_fix f x t ->
      red m1 (subst f v1 (subst x v2 t)) m2 r ->
      red m1 (trm_app v1 v2) m2 r
  | red_ref : forall ma mb v l,  
      mb = (fmap_single l v) ->
      l <> null ->
      \# ma mb ->
      red ma (val_ref v) (mb \+ ma) (val_loc l)
  | red_get : forall m l v,
      fmap_data m l = Some v ->
      red m (val_get (val_loc l)) m v
  | red_set : forall m m' l v,
      m' = fmap_update m l v ->
      red m (val_set (val_loc l) v) m' val_unit
  | red_alloc : forall k n ma mb l,
      mb = fmap_conseq l k val_unit ->
      n = nat_to_Z k ->
      l <> null ->
      \# ma mb ->
      red ma (val_alloc (val_int n)) (mb \+ ma) (val_loc l)
  | red_add : forall m n1 n2 n',
      n' = n1 + n2 ->
      red m (val_add (val_int n1) (val_int n2)) m (val_int n')
  | red_sub : forall m n1 n2 n',
      n' = n1 - n2 ->
      red m (val_sub (val_int n1) (val_int n2)) m (val_int n')
  | red_ptr_add : forall l' m l n,
      (l':nat) = (l:nat) + n :> int ->
      red m (val_ptr_add (val_loc l) (val_int n)) m (val_loc l')
  | red_eq : forall m v1 v2,
      red m (val_eq v1 v2) m (val_bool (isTrue (v1 = v2)))
  | red_while : forall m1 m2 t1 t2 r,
      red m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) m2 r ->
      red m1 (trm_while t1 t2) m2 r
  | red_for_arg : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
      (* TODO: add [not_is_val t1 \/ not_is_val t2] *)
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_for x v1 v2 t3) m4 r ->
      red m1 (trm_for x t1 t2 t3) m4 r
  | red_for : forall m1 m2 x n1 n2 t3 r,
      red m1 (
        If (n1 <= n2)   
          then (trm_seq (subst x n1 t3) (trm_for x (n1+1) n2 t3))
          else val_unit) m2 r ->
      red m1 (trm_for x n1 n2 t3) m2 r.

  (* Remark: alternative for red_for rules.
    | red_for : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
        red m1 (
          (trm_seq (trm_let x n1 t3) (trm_for x (n1+1) n2 t3))
          val_unit) m2 r ->
        red m1 (trm_for x n1 n2 t3) m2 r
  *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Derived rules *)

Lemma red_ptr_add_nat : forall m l (f : nat),
  red m (val_ptr_add (val_loc l) (val_int f)) m (val_loc (l+f)%nat).
Proof using. intros. applys* red_ptr_add. math. Qed.

Lemma red_if_bool : forall m1 m2 b r t1 t2,
  red m1 (if b then t1 else t2) m2 r ->
  red m1 (trm_if b t1 t2) m2 r.
Proof using. introv M1. applys* red_if. applys red_val. Qed.

Lemma red_for_le : forall m1 m2 m3 x n1 n2 t3 r,
  n1 <= n2 ->
  red m1 (subst x n1 t3) m2 val_unit ->
  red m2 (trm_for x (n1+1) n2 t3) m3 r ->
  red m1 (trm_for x n1 n2 t3) m3 r.
Proof using.
  introv N M1 M2. applys red_for. case_if.
  { applys red_seq. applys M1. applys M2. }
  { false; math. }
Qed.

Lemma red_for_gt : forall m x n1 n2 t3,
  n1 > n2 ->
  red m (trm_for x n1 n2 t3) m val_unit.
Proof using.
  introv N. applys red_for. case_if.
  { false; math. }
  { applys red_val. }
Qed.

End Red.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Notation for terms *)

(* ---------------------------------------------------------------------- *)
(** Notation for concrete programs *)

Notation "'()" := val_unit : trm_scope.

Notation "'If_' t0 'Then' t1 'Else' t2" :=
  (trm_if t0 t1 t2)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'If_' t0 'Then' t1 'End'" :=
  (trm_if t0 t1 val_unit)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'Let' x ':=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Let'  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Let' 'Rec' f x ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x t1) t2)
  (at level 69, f ident, x ident, right associativity,
  format "'[v' '[' 'Let'  'Rec'  f  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "t1 ;; t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity, only parsing,
   format "'[v' '[' t1 ']'  ;;  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Fix' f x ':=' t" :=
  (trm_fix f x t)
  (at level 69, f ident, x ident) : trm_scope.

Notation "'Fix' f x1 x2 ':=' t" :=
  (trm_fix f x1 (trm_fun x2 t))
  (at level 69, f ident, x1 ident, x2 ident) : trm_scope.

Notation "'Fix' f x1 x2 x3 ':=' t" :=
  (trm_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f ident, x1 ident, x2 ident, x3 ident) : trm_scope.

Notation "'ValFix' f x ':=' t" :=
  (val_fix f x t)
  (at level 69, f ident, x ident) : trm_scope.

Notation "'ValFix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f ident, x1 ident, x2 ident) : trm_scope.

Notation "'ValFix' f x1 x2 x3 ':=' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f ident, x1 ident, x2 ident, x3 ident) : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 ident) : trm_scope.

Notation "'Fun' x1 x2 ':=' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1 ident, x2 ident) : trm_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 ident, x2 ident, x3 ident) : trm_scope.

Notation "'ValFun' x1 ':=' t" :=
  (val_fun x1 t)
  (at level 69, x1 ident) : trm_scope.

Notation "'ValFun' x1 x2 ':=' t" :=
  (val_fun x1 (trm_fun x2 t))
  (at level 69, x1 ident, x2 ident) : trm_scope.

Notation "'ValFun' x1 x2 x3 ':=' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 ident, x2 ident, x3 ident) : trm_scope.

Notation "'LetFun' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 t1) t2)
  (at level 69, f ident, x1 ident) : trm_scope.

Notation "'LetFun' f x1 x2 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 (trm_fun x2 t1)) t2)
  (at level 69, f ident, x1 ident, x2 ident) : trm_scope.

Notation "'LetFun' f x1 x2 x3 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 (trm_fun x2 (trm_fun x3 t1))) t2)
  (at level 69, f ident, x1 ident, x2 ident, x3 ident) : trm_scope.

Notation "'LetFix' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 t1) t2)
  (at level 69, f ident, x1 ident) : trm_scope.

Notation "'LetFix' f x1 x2 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 t1)) t2)
  (at level 69, f ident, x1 ident, x2 ident) : trm_scope.

Notation "'LetFix' f x1 x2 x3 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 (trm_fun x3 t1))) t2)
  (at level 69, f ident, x1 ident, x2 ident, x3 ident) : trm_scope.

Notation "'While' t1 'Do' t2 'Done'" :=
  (trm_while t1 t2)
  (at level 69, t2 at level 68,
   format "'[v' 'While'  t1  'Do'  '/' '[' t2 ']' '/'  'Done' ']'")
   : trm_scope.

Notation "'For' x ':=' t1 'To' t2 'Do' t3 'Done'" :=
  (trm_for x t1 t2 t3)
  (at level 69, x ident, (* t1 at level 0, t2 at level 0, *)
   format "'[v' 'For'  x  ':='  t1  'To'  t2  'Do'  '/' '[' t3 ']' '/'  'Done' ']'")
  : trm_scope.



(* ---------------------------------------------------------------------- *)
(** Notation for declaring program variables *)

(* TODO: check if it is possible to use a recursive notation *)

Notation "'Vars' X1 'from' n 'in' t" :=
  (let X1 : var := n%nat in t)
  (at level 69, X1 ident).

Notation "'Vars' X1 , X2 'from' n 'in' t" :=
  (let X1 : var := n%nat in 
   let X2 : var := S n in t)
  (at level 69, X1 ident, X2 ident).

Notation "'Vars' X1 , X2 , X3 'from' n 'in' t" :=
  (let X1 : var := n%nat in 
   let X2 : var := S n in 
   let X3 : var := S (S n) in t)
  (at level 69, X1 ident, X2 ident, X3 ident).

Notation "'Vars' X1 , X2 , X3 , X4 'from' n 'in' t" :=
  (let X1 : var := n%nat in 
   let X2 : var := S n in 
   let X3 : var := S (S n) in
   let X4 : var := S (S (S n)) in t)
  (at level 69, X1 ident, X2 ident, X3 ident, X4 ident).

Notation "'Vars' X1 , X2 , X3 , X4 , X5 'from' n 'in' t" :=
  (let X1 : var := n%nat in 
   let X2 : var := S n in 
   let X3 : var := S (S n) in
   let X4 : var := S (S (S n)) in
   let X5 : var := S (S (S (S n))) in t)
  (at level 69, X1 ident, X2 ident, X3 ident, X4 ident, X5 ident).

Notation "'Vars' X1 'in' t" :=
  (let X1 : var := 0%nat in t)
  (at level 69, X1 ident).

Notation "'Vars' X1 , X2 'in' t" :=
  (let X1 : var := 0%nat in 
   let X2 : var := 1%nat in t)
  (at level 69, X1 ident, X2 ident).

Notation "'Vars' X1 , X2 , X3 'in' t" :=
  (let X1 : var := 0%nat in 
   let X2 : var := 1%nat in 
   let X3 : var := 2%nat in t)
  (at level 69, X1 ident, X2 ident, X3 ident).

Notation "'Vars' X1 , X2 , X3 , X4 'in' t" :=
  (let X1 : var := 0%nat in 
   let X2 : var := 1%nat in 
   let X3 : var := 2%nat in
   let X4 : var := 3%nat in t)
  (at level 69, X1 ident, X2 ident, X3 ident, X4 ident).

Notation "'Vars' X1 , X2 , X3 , X4 , X5 'in' t" :=
  (let X1 : var := 0%nat in 
   let X2 : var := 1%nat in 
   let X3 : var := 2%nat in
   let X4 : var := 3%nat in
   let X5 : var := 4%nat in t)
  (at level 69, X1 ident, X2 ident, X3 ident, X4 ident, X5 ident).

Notation "'Vars' X1 , X2 , X3 , X4 , X5 , X6 'in' t" :=
  (let X1 : var := 0%nat in 
   let X2 : var := 1%nat in 
   let X3 : var := 2%nat in
   let X4 : var := 3%nat in
   let X5 : var := 4%nat in
   let X6 : var := 5%nat in t)
  (at level 69, X1 ident, X2 ident, X3 ident, X4 ident, X5 ident, X6 ident).

Notation "'Vars' X1 , X2 , X3 , X4 , X5 , X6 , X7 'in' t" :=
  (let X1 : var := 0%nat in 
   let X2 : var := 1%nat in 
   let X3 : var := 2%nat in
   let X4 : var := 3%nat in
   let X5 : var := 4%nat in
   let X6 : var := 5%nat in
   let X7 : var := 6%nat in t)
  (at level 69, X1 ident, X2 ident, X3 ident, X4 ident, X5 ident, X6 ident, X7 ident).


(* ********************************************************************** *)
(* ################################################################# *)
(* * Size of a term *)

(* ---------------------------------------------------------------------- *)
(** Size of a term, where all values counting for one unit. *)

Fixpoint trm_size (t:trm) : nat :=
  match t with
  | trm_var x => 1
  | trm_val v => 1
  | trm_fun x t1 => 1 + trm_size t1
  | trm_fix f x t1 => 1 + trm_size t1
  | trm_if t0 t1 t2 => 1 + trm_size t0 + trm_size t1 + trm_size t2
  | trm_seq t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_let x t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_app t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_while t1 t2 => 1 + trm_size t1 + trm_size t2
  | trm_for x t1 t2 t3 => 1 + trm_size t1 + trm_size t2 + trm_size t3
  end.

Lemma trm_size_subst : forall t x v,
  trm_size (subst x v t) = trm_size t.
Proof using.
  intros. induction t; simpl; repeat case_if; auto.
Qed.

(** Hint for induction on size. Proves subgoals of the form
    [measure trm_size t1 t2], when [t1] and [t2] may have some
    structure or involve substitutions. *) 

Ltac solve_measure_trm_size tt :=
  unfold measure in *; simpls; repeat rewrite trm_size_subst; math.

Hint Extern 1 (measure trm_size _ _) => solve_measure_trm_size tt.


(* ********************************************************************** *)
(* ################################################################# *)
(* * N-ary functions and applications *)


(** [trm_apps t ts] denotes a n-ary application of [t] to the
    arguments from the list [ts]. 
    
    [trm_funs xs t] denotes a n-ary function with arguments [xs]
    and body [t].
    
    [trm_fixs f xs t] denotes a n-ary recursive function [f]
    with arguments [xs] and body [t].
 
  The tactic [rew_nary] can be used to convert terms in the goal
  to using the nary constructs wherever possible.

  The operation [substs xs vs t] substitutes the variables [xs]
  with the values [vs] inside the term [t].
*)



(* ---------------------------------------------------------------------- *)
(** Types *)

Definition vars : Type := list var.
Definition vals : Type := list val.
Definition trms : Type := list trm.


(* ---------------------------------------------------------------------- *)
(** Coercions from values to terms *)

Coercion vals_to_trms (vs:vals) : trms :=
  List.map trm_val vs.

(** Tactic [rew_vals_to_trms] to fold the coercion where possible *)

Lemma vals_to_trms_fold_start : forall v,
  (trm_val v)::nil = vals_to_trms (v::nil).
Proof using. auto. Qed.

Lemma vals_to_trms_fold_next : forall v vs,
  (trm_val v)::(vals_to_trms vs) = vals_to_trms (v::vs).
Proof using. auto. Qed.

Hint Rewrite vals_to_trms_fold_start vals_to_trms_fold_next 
  : rew_vals_to_trms.

Tactic Notation "rew_vals_to_trms" :=
  autorewrite with rew_vals_to_trms.


(* ---------------------------------------------------------------------- *)
(** Distinct variables *)

(* TODO: use LibListExec *)

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if eq_var_dec x y then false else var_fresh y xs'
  end.

Fixpoint var_distinct (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => var_fresh x xs' && var_distinct xs'
  end.


(* ---------------------------------------------------------------------- *)
(** N-ary substitution *)

Fixpoint substs (ys:vars) (ws:vals) (t:trm) : trm :=
  match ys, ws with
  | y::ys', w::ws' => substs ys' ws' (subst y w t)
  | _, _ => t
  end.

Lemma subst_subst_cross : forall x1 x2 v1 v2 t,
  x1 <> x2 ->
  subst x2 v2 (subst x1 v1 t) = subst x1 v1 (subst x2 v2 t).
Proof using.
  introv N. induction t; simpl; try solve [ fequals;
  repeat case_if; simpl; repeat case_if; auto ].
  repeat case_if; simpl; repeat case_if~.
Qed. (* TODO: simplify *)

Lemma subst_substs : forall x v ys ws t,
  var_fresh x ys ->
  length ys = length ws ->
  subst x v (substs ys ws t) = substs ys ws (subst x v t).
Proof using.
  intros. gen t ws. induction ys as [|y ys']; introv L. simpls.
  { auto. }
  { destruct ws as [|w ws']; rew_list in *. { false; math. }
    simpls. case_if. rewrite~ IHys'. fequals. rewrite~ subst_subst_cross. }
Qed.


(* ---------------------------------------------------------------------- *)
(** N-ary applications and N-ary functions *)

Fixpoint trm_apps (tf:trm) (ts:trms) : trm :=
  match ts with
  | nil => tf
  | t::ts' => trm_apps (trm_app tf t) ts'
  end.

Fixpoint trm_funs (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => t
  | x::xs' => trm_fun x (trm_funs xs' t)
  end.

Definition val_funs (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x::xs' => val_fun x (trm_funs xs' t)
  end.

Definition trm_fixs (f:var) (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => t
  | x::xs' => trm_fix f x (trm_funs xs' t)
  end.

Definition val_fixs (f:var) (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x::xs' => val_fix f x (trm_funs xs' t)
  end.


(* ---------------------------------------------------------------------- *)
(** Properties of n-ary functions *)

Lemma red_funs : forall m xs t,
  xs <> nil ->
  red m (trm_funs xs t) m (val_funs xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. } 
  simpl. applys red_fun.
Qed.

Lemma subst_trm_funs : forall y w xs t,
  var_fresh y xs ->
  subst y w (trm_funs xs t) = trm_funs xs (subst y w t).
Proof using.
  introv N. induction xs as [|x xs']; simpls; fequals.
  { case_if. rewrite~ IHxs'. }
Qed.

Definition var_funs (n:nat) (xs:vars) : Prop := 
     var_distinct xs
  /\ length xs = n 
  /\ xs <> nil.

Lemma red_app_funs_val_ind : forall xs vs m1 m2 tf t r,
  red m1 tf m1 (val_funs xs t) ->
  red m1 (substs xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps tf vs) m2 r.
Proof using.
  hint red_val.
  intros xs. induction xs as [|x xs']; introv R M (N&L&P).
  { false. } clear P.
  { destruct vs as [|v vs']; rew_list in *. { false; math. }
    simpls. tests C: (xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys~ red_app_arg R. applys~ red_app_fun. }
    { rew_istrue in N. destruct N as [F N']. applys~ IHxs' M. 
      applys~ red_app_arg R. applys~ red_app_fun. 
      rewrite~ subst_trm_funs. applys~ red_funs. splits~. } }
Qed.

Lemma red_app_funs_val : forall xs vs m1 m2 vf t r,
  vf = val_funs xs t ->
  red m1 (substs xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv R M N. applys* red_app_funs_val_ind.
  { subst. apply~ red_val. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of n-ary recursive functions *)

Lemma red_fixs : forall m f xs t,
  xs <> nil ->
  red m (trm_fixs f xs t) m (val_fixs f xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. } 
  simpl. applys red_fix.
Qed.

Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst y w (trm_fixs f xs t) = trm_fixs f xs (subst y w t).
Proof using.
  introv N. unfold trm_fixs. destruct xs as [|x xs'].  
  { auto. }
  { simpls. do 2 case_if in N. rewrite~ subst_trm_funs. }
Qed.

Definition var_fixs (f:var) (n:nat) (xs:vars) : Prop := 
     var_distinct (f::xs)
  /\ length xs = n 
  /\ xs <> nil.

Lemma red_app_fixs_val : forall xs vs m1 m2 vf f t r,
  vf = val_fixs f xs t ->
  red m1 (subst f vf (substs xs vs t)) m2 r ->
  var_fixs f (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv E M (N&L&P). destruct xs as [|x xs']. { false. }
  { destruct vs as [|v vs']; rew_list in *. { false; math. } clear P.
    simpls. case_if*. rew_istrue in *. destruct N as (N1&N2&N3).
    subst vf. tests C':(xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys~ red_app_fix. }
    { applys~ red_app_funs_val_ind. 
      { applys~ red_app_fix. do 2 rewrite~ subst_trm_funs. applys~ red_funs. }
      { rewrite~ subst_substs in M. }
      { splits*. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** Folding of n-ary functions *)

Lemma trm_apps_fold_start : forall t1 t2,
  trm_app t1 t2 = trm_apps t1 (t2::nil).
Proof using. auto. Qed.

Lemma trm_apps_fold_next : forall t1 t2 t3s,
  trm_apps (trm_app t1 t2) t3s = trm_apps t1 (t2::t3s).
Proof using. auto. Qed.

Lemma trm_apps_fold_concat : forall t1 t2s t3s,
  trm_apps (trm_apps t1 t2s) t3s = trm_apps t1 (List.app t2s t3s).
Proof using.
  intros. gen t1; induction t2s; intros. { auto. }
  { rewrite <- trm_apps_fold_next. simpl. congruence. }
Qed.

Lemma trm_funs_fold_start : forall x t,
  trm_fun x t = trm_funs (x::nil) t.
Proof using. auto. Qed.

Lemma trm_funs_fold_next : forall x xs t,
  trm_funs (x::nil) (trm_funs xs t) = trm_funs (x::xs) t.
Proof using. auto. Qed.

Lemma trm_fixs_fold_start : forall f x t,
  trm_fix f x t = trm_fixs f (x::nil) t.
Proof using. auto. Qed.

(* subsumed by iteration of trm_funs_fold_next *)
Lemma trm_funs_fold_app : forall xs ys t, 
  trm_funs xs (trm_funs ys t) = trm_funs (List.app xs ys) t.
Proof using.
  intros. induction xs. { auto. } { simpl. congruence. }
Qed.

(* for innermost first rewriting strategy
Lemma trm_fixs_fold_next : forall f x xs t,
  trm_fixs f (x::nil) (trm_funs xs t) = trm_fixs f (x::xs) t.
Proof using. auto. Qed.
*)

Lemma trm_fixs_fold_app : forall f x xs ys t, 
  trm_fixs f (x::xs) (trm_funs ys t) = trm_fixs f (x :: List.app xs ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_funs_fold_start : forall x t,
  val_fun x t = val_funs (x::nil) t.
Proof using. auto. Qed.

Lemma val_funs_fold_app : forall x xs ys t,
  val_funs (x::xs) (trm_funs ys t) = val_funs (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_funs_fold_app' : forall x xs ys t,
  val_funs (List.app (x::nil) xs) (trm_funs ys t) = val_funs (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_start : forall f x t,
  val_fix f x t = val_fixs f (x::nil) t.
Proof using. auto. Qed.

Lemma val_fixs_fold_app : forall f x xs ys t,
  val_fixs f (x::xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_app' : forall f x xs ys t,
  val_fixs f (List.app (x::nil) xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Hint Rewrite  
  trm_apps_fold_start trm_apps_fold_next trm_apps_fold_concat
  trm_funs_fold_start trm_funs_fold_next 
  trm_fixs_fold_start trm_fixs_fold_app 
  val_funs_fold_start val_funs_fold_app val_funs_fold_app'
  val_fixs_fold_start val_fixs_fold_app val_fixs_fold_app' : rew_nary.

Tactic Notation "rew_nary" := 
  autorewrite with rew_nary; simpl List.app.
Tactic Notation "rew_nary" "in" hyp(H) := 
  autorewrite with rew_nary in H; simpl List.app in H.
Tactic Notation "rew_nary" "in" "*" := 
  autorewrite with rew_nary in *; simpl List.app in *.
  (* rewrite_strat (any (innermost (hints rew_nary))). 
     => way too slow! *)

Lemma rew_nary_demo_1 : forall f x y z t1 t2 t,
  val_fix f x (trm_fun y (trm_fun z (f t1 x y t2))) = t.
Proof using. intros. rew_nary. Abort.

Lemma rew_nary_demo_2 : forall f x y t,
  val_fun f (trm_fun x (trm_fun y (x y))) = t.
Proof using. intros. rew_nary. Abort.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Sequence of consecutive variables *)

(** [nat_seq i n] generates a list of variables [x1;x2;..;xn]
    with [x1=i] and [xn=i+n-1]. Such lists are useful for
    generic programming. *)

Fixpoint nat_seq (start:nat) (nb:nat) :=
  match nb with
  | O => nil
  | S nb' => start :: nat_seq (S start) nb'
  end.

Section Nat_seq.
Implicit Types start nb : nat.

Lemma var_fresh_nat_seq_lt : forall x start nb,
  (x < start)%nat ->
  var_fresh x (nat_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_if. { math. } { applys IHnb. math. } }
Qed.

Lemma var_fresh_nat_seq_ge : forall x start nb,
  (x >= start+nb)%nat ->
  var_fresh x (nat_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. case_if. { math. } { applys IHnb. math. } }
Qed.

Lemma var_distinct_nat_seq : forall start nb,
  var_distinct (nat_seq start nb).
Proof using. 
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. rew_istrue. split.
    { applys var_fresh_nat_seq_lt. math. }
    { auto. } }
Qed.

Lemma length_nat_seq : forall start nb,
  length (nat_seq start nb) = nb.
Proof using. 
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.

Lemma var_funs_nat_seq : forall start nb,
  (nb > 0%nat)%nat ->
  var_funs nb (nat_seq start nb).
Proof using.
  introv E. splits.
  { applys var_distinct_nat_seq. }
  { applys length_nat_seq. }
  { destruct nb. { false. math. } { simpl. auto_false. } }
Qed.

End Nat_seq.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Tactics  *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [fmap_red] for proving [red] goals modulo 
      equalities between states *)

Ltac fmap_red_base tt ::=
  match goal with H: red _ ?t _ _ |- red _ ?t _ _ =>
    applys_eq H 2 4; try fmap_eq end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [var_neq] for proving two concrete variables distinct;
      also registered as hint for [auto] *)

Ltac var_neq :=
  match goal with |- ?x <> ?y :> var => 
    solve [ let E := fresh in 
            destruct (eq_var_dec x y) as [E|E]; 
              [ false | apply E ] ] end.

Hint Extern 1 (?x <> ?y) => var_neq.


