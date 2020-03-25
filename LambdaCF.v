(** 

This file formalizes characteristic formulae for plain Separation Logic.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
Require Export LibFix.
Require Export LambdaSep.
Open Scope heap_scope.

Implicit Types v w : val.
Implicit Types t : trm.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Type of a formula *)

(** A formula is a binary relation relating a pre-condition
    and a post-condition. *)

Definition formula := hprop -> (val -> hprop) -> Prop.

Global Instance Inhab_formula : Inhab formula.
Proof using. apply (Inhab_of_val (fun _ _ => True)). Qed.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Characteristic formula generator *)


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic formula
    associated with each term construct. *)

Definition cf_fail : formula := fun H Q => 
  False.

Definition cf_val (v:val) : formula := fun H Q =>
  (fun (x:val) => \[x = v] \* H)  ===> Q.
  
Definition cf_seq (F1 F2:formula) : formula := fun H Q =>
  exists H1, 
      F1 H (fun r => \[r = val_unit] \* H1) 
   /\ F2 H1 Q.

(* TODO: maybe use the following alternative, like in [LambdaCFLifted]:
  Definition cf_seq (F1 : formula) (F2 : formula) : formula := fun H Q =>
    exists Q1, 
        F1 H Q1 
     /\ F2 H1 Q
     /\  (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False]).
*)

Definition cf_let (F1:formula) (F2of:val->formula) : formula := fun H Q =>
  exists Q1, 
      F1 H Q1 
   /\ (forall (X:val), (F2of X) (Q1 X) Q).

Definition cf_if_val (v:val) (F1 F2:formula) : formula := fun H Q =>
  exists (b:bool), (v = val_bool b)
                /\ (b = true -> F1 H Q)
                /\ (b = false -> F2 H Q).

Definition cf_if (F0 F1 F2 : formula) : formula := 
  cf_let F0 (fun v => local (cf_if_val v F1 F2)).

Definition cf_while (F1 F2:formula) : formula := fun H Q => 
  forall (R:formula), is_local R ->
  let F := (local (cf_if F1 (local (cf_seq F2 R)) (local (cf_val val_unit)))) in
  (forall H' Q', F H' Q' -> R H' Q') ->
  R H Q.

Definition cf_for (v1 v2:val) (F3:int->formula) : formula := fun H Q => 
  exists n1 n2, (v1 = val_int n1) /\ (v2 = val_int n2) /\
  (forall (S:int->formula), is_local_pred S ->
   let F i := local (If (i <= n2) then (cf_seq (F3 i) (S (i+1)))
                            else (cf_val val_unit)) in
   (forall i H' Q', F i H' Q' -> S i H' Q') -> 
   S n1 H Q).


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Definition of the CF generator *)

(** The CF generator is a recursive function, defined using the
    optimal fixed point combinator (from TLC). [cf_def] gives the
    function, and [cf] is then defined as the fixpoint of [cf_def]. 
    Subsequently, the fixed-point equation is established. *)

Definition cf_def cf (t:trm) :=
  match t with
  | trm_val v => local (cf_val v)
  | trm_var x => local (cf_fail) (* unbound variable *)
  | trm_fun x t1 => local (cf_val (val_fun x t1))
  | trm_fix f x t1 => local (cf_val (val_fix f x t1))
  | trm_if t0 t1 t2 => local (cf_if (cf t0) (cf t1) (cf t2))
  | trm_seq t1 t2 => local (cf_seq (cf t1) (cf t2))
  | trm_let x t1 t2 => local (cf_let (cf t1) (fun X => cf (subst x X t2)))
  | trm_app t1 t2 => local (triple t)
  | trm_while t1 t2 => local (cf_while (cf t1) (cf t2))
  | trm_for x t1 t2 t3 => local (
      match t1, t2 with 
      | trm_val v1, trm_val v2 => cf_for v1 v2 (fun X => cf (subst x X t3))
      | _, _ => cf_fail
      end)
  end.

Definition cf := FixFun cf_def.

Ltac fixfun_auto := try solve [ 
  try fequals; auto; try apply fun_ext_1; auto ].

Lemma cf_unfold_iter : forall n t,
  cf t = func_iter n cf_def cf t.
Proof using.
  applys~ (FixFun_fix_iter (measure trm_size)). auto with wf.
  intros f1 f2 t IH. unfold cf_def.
  destruct t; fequals.
  { fequals~. }
  { fequals~. }
  { fequals~. applys~ fun_ext_1. }
  { fequals~. }
  { destruct t1; fequals~. destruct t2; fequals~.
    applys~ fun_ext_1. }
Qed.

Lemma cf_unfold : forall t,
  cf t = cf_def cf t.
Proof using. applys (cf_unfold_iter 1). Qed.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Soundness proof *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Soundness of the CF generator *)

Lemma is_local_cf : forall T,
  is_local (cf T).
Proof.
  intros. rewrite cf_unfold. destruct T; try apply is_local_local.
Qed.

Definition sound_for (t:trm) (F:formula) := 
  forall H Q, F H Q -> triple t H Q.

Lemma sound_for_local : forall t (F:formula),
  sound_for t F ->
  sound_for t (local F).
Proof using.
  unfold sound_for. introv SF. intros H Q M.
  rewrite is_local_triple. applys local_weaken_body M. applys SF.
Qed.

Lemma sound_for_cf : forall (t:trm),
  sound_for t (cf t).
Proof using.
  intros t. induction_wf: trm_size t. 
  rewrite cf_unfold. destruct t; simpl;
   try (applys sound_for_local; intros H Q P).  
  { unfolds in P. applys~ rule_val. hchanges~ P. }
  { false. }
  { unfolds in P. applys rule_fun. hchanges~ P. }
  { unfolds in P. applys rule_fix. hchanges~ P. }
  { destruct P as (Q1&P1&P2). applys rule_if. 
    { applys* IH. }
    { intros v. specializes P2 v. applys sound_for_local (rm P2).
      clears H Q Q1. intros H Q (b&P1'&P2'&P3'). inverts P1'.
      case_if; applys* IH. }
    { intros v N. specializes P2 v. applys local_extract_false P2.
      intros H' Q' (b&E&S1&S2). subst. applys N. hnfs*. } }
  { destruct P as (H1&P1&P2). applys rule_seq' H1.
    { applys~ IH. }
    { intros X. applys~ IH. } } 
  { destruct P as (Q1&P1&P2). applys rule_let Q1.
    { applys~ IH. }
    { intros X. applys~ IH. } } 
  { applys P. }
  { hnf in P. simpls. applys P. { xlocal. } clears H Q. intros H Q P.
    applys rule_while_raw. applys sound_for_local (rm P). 
    clears H Q. intros H Q (Q1&P1&P2). applys rule_if.  
    { applys* IH. }
    { intros b. specializes P2 b. applys sound_for_local (rm P2).
      clears H Q1 Q. intros H Q (b'&P1&P2&P3). inverts P1. case_if.
      { forwards~ P2': (rm P2). applys sound_for_local (rm P2'). 
        clears H Q b'. intros H Q (H1&P1&P2). applys rule_seq'.
         { applys* IH. }
         { applys P2. } }
      { forwards~ P3': (rm P3). applys sound_for_local (rm P3'). 
        clears H Q b'. intros H Q P. hnf in P. applys rule_val.
         { hchanges* P. } } }
    { intros v N. specializes P2 v. applys local_extract_false P2.
      intros H' Q' (b&E&S1&S2). subst. applys N. hnfs*. } }
  { destruct t1; tryfalse. destruct t2; tryfalse.
    hnf in P. destruct P as (n1&n2&E1&E2&P). subst v0 v1.
    simpls. applys P. { xlocal. } 
    clears H Q. intros i H Q P. applys sound_for_local (rm P). 
    clears H Q. intros H Q P. applys rule_for. case_if as C.
    { destruct P as (H1&P1&P2). exists (fun r => \[r = val_unit] \* H1).
      splits.
      { applys* IH. }
      { xpull ;=> _. applys P2. }
      { intros v' N. hpull. } }
    { hnf in P. hchanges* P. } }
Qed.

Theorem triple_of_cf : forall t H Q, 
  cf t H Q -> 
  triple t H Q.
Proof using. intros. applys* sound_for_cf. Qed.

Lemma triple_trm_of_cf_iter : forall (n:nat) t H Q,
  func_iter n cf_def cf t H Q ->
  triple t H Q.
Proof using.
  introv M. rewrite <- cf_unfold_iter in M. applys* triple_of_cf.
Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Bonus : corrolary for demos *)

Lemma triple_app_fun_of_cf_iter : forall n F v x t H Q,
  F = val_fun x t ->
  func_iter n cf_def cf (subst x v t) H Q ->
  triple (F v) H Q.
Proof using.
  introv EF M. applys* rule_app_fun.
  applys* triple_trm_of_cf_iter.
Qed.

Lemma triple_app_fix_of_cf_iter : forall n F v f x t H Q,
  F = val_fix f x t ->
  func_iter n cf_def cf (subst f F (subst x v t)) H Q ->
  triple (F v) H Q.
Proof using.
  introv EF M. applys* rule_app_fix.
  applys* triple_trm_of_cf_iter.
Qed.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Practical proofs using characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Notation for characteristic formulae *)

Notation "'`Val' v" :=
  (local (cf_val v))
  (at level 69) : charac.

Notation "'`LetIf' F0 'Then' F1 'Else' F2" :=
  (local (cf_if F0 F1 F2))
  (at level 69, F0 at level 0) : charac.

Notation "'`If' v 'Then' F1 'Else' F2" :=
  (local (cf_if_val v F1 F2))
  (at level 69) : charac.

Notation "'`Seq' F1 ;; F2" :=
  (local (cf_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' '`Seq'  '[' F1 ']'  ;;  '/'  '[' F2 ']' ']'") : charac.

Notation "'`Let' x ':=' F1 'in' F2" :=
  (local (cf_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.

Notation "'`App' t " :=
  (local (triple t))
  (at level 68, t at level 0) : charac.

Notation "'`Fail'" :=
  (local cf_fail)
  (at level 69) : charac.

Notation "'`While' F1 'Do' F2 'Done'" :=
  (local (cf_while F1 F2))
  (at level 69, F2 at level 68,
   format "'[v' '`While'  F1  'Do'  '/' '[' F2 ']' '/'  'Done' ']'")
   : charac.

Notation "'`For' x '=' v1 'To' v2 'Do' F3 'Done'" :=
  (local (cf_for v1 v2 (fun x => F3)))
  (at level 69, x ident, (* t1 at level 0, t2 at level 0, *)
   format "'[v' '`For'  x  '='  v1  'To'  v2  'Do'  '/' '[' F3 ']' '/'  'Done' ']'")
  : charac.

Open Scope charac.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Lemmas for tactics *)

Section LemmasCf.
Implicit Types n : nat.
Implicit Types F : val.
Implicit Types f x : var.

(*-- LATER: move to TLC LibNatExec *)

Fixpoint nat_compare (x y : nat) :=
  match x, y with
  | O, O => true
  | S x', S y' => nat_compare x' y'
  | _, _ => false
  end.

Lemma nat_compare_eq : forall n1 n2,
  nat_compare n1 n2 = isTrue (n1 = n2).
Proof using.
  intros n1. induction n1; intros; destruct n2; simpl; rew_bool_eq; auto_false.
  rewrite IHn1. extens. rew_istrue. math.
Qed.

Definition var_funs_exec (n:nat) (xs:vars) : bool := (* --todo: use exec typeclass *)
     nat_compare n (List.length xs)
  && is_not_nil xs   (* --todo: rename to exec *)
  && var_distinct xs.

Lemma var_funs_exec_eq : forall n xs,
  var_funs_exec n xs = isTrue (var_funs n xs).
Proof using.
  intros. unfold var_funs_exec, var_funs.
  rewrite nat_compare_eq.
  rewrite is_not_nil_eq.
  rewrite List_length_eq.
  extens. rew_istrue. iff*.
Qed.

Lemma triple_apps_funs_of_cf_iter : forall n F (vs:vals) xs t H Q,
  F = val_funs xs t ->
  var_funs_exec (length vs) xs ->
  func_iter n cf_def cf (substs xs vs t) H Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_funs_exec_eq in N. rew_istrue in N.
  applys* rule_apps_funs. applys* triple_trm_of_cf_iter.
Qed.

Definition var_fixs_exec (f:var) (n:nat) (xs:vars) : bool := (* todo: use exec typeclass *)
     nat_compare n (List.length xs)
  && is_not_nil xs   (* todo: rename to exec *)
  && var_distinct (f::xs).

Lemma var_fixs_exec_eq : forall f n xs,
  var_fixs_exec f n xs = isTrue (var_fixs f n xs).
Proof using.
  intros. unfold var_fixs_exec, var_fixs.
  rewrite nat_compare_eq.
  rewrite is_not_nil_eq.
  rewrite List_length_eq.
  extens. rew_istrue. iff*.
Qed.

Lemma triple_apps_fixs_of_cf_iter : forall n f F (vs:vals) xs t H Q,
  F = val_fixs f xs t ->
  var_fixs_exec f (length vs) xs ->
  func_iter n cf_def cf (subst f F (substs xs vs t)) H Q ->
  triple (trm_apps F vs) H Q.
Proof using.
  introv EF N M. rewrite var_fixs_exec_eq in N. rew_istrue in N.
  applys* rule_apps_fixs. applys* triple_trm_of_cf_iter.
Qed.

End LemmasCf.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Database of specifications used by [xapp], through tactic  [xspec] *)

(** A name for the database *)

Definition database_spec := True.

(** We here use the notation [Register] and [Provide] from the TLC library.

  Usage of [RegisterSpecGoal], e.g.:

    Hint Extern 1 (RegisterSpecGoal (triple (trm_app2_val (val_prim val_eq) ?x ?y) ?H ?Q)) => 
      Provide rule_eq.

  Usage of [RegisterSpecApp], e.g.:

    Hint Extern 1 (RegisterSpecApp (trm_app2_val (val_prim val_eq) ?x ?y)) => 
      Provide rule_eq.

*)

Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : charac.

Notation "'Register_rule' t" := (Register_goal (triple t _ _))
  (at level 69) : charac.

Notation "'Register_spec' f" := (Register_rule (trm_apps (trm_val f) _))
  (at level 69) : charac.

(** [xspec G] retreives from the database [database_spec]
    the specification that could apply to a goal [G].
    It places the specification as hypothesis at the head of the goal. *)

Ltac xapp_basic_prepare tt := (* defined further *)
  idtac. 

Ltac xspec_context G := (* refined only in LambdaCFLifted *)
  fail.

Ltac xspec_registered G :=
  ltac_database_get database_spec G.

Ltac xspec_database G :=
   first [ xspec_registered G | xspec_context G ].

Ltac xspec_base tt :=
  match goal with
  | |- ?G => xspec_database G
  end.

Ltac xspec_core tt :=
  xapp_basic_prepare tt;
  xspec_base tt.

Tactic Notation "xspec" :=
  xspec_core tt.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(** ** Registering specification of primitive functions *)

Hint Extern 1 (Register_spec (val_prim val_ref)) => Provide rule_ref.
Hint Extern 1 (Register_spec (val_prim val_get)) => Provide rule_get.
Hint Extern 1 (Register_spec (val_prim val_set)) => Provide rule_set.
Hint Extern 1 (Register_spec (val_prim val_alloc)) => Provide rule_alloc.
Hint Extern 1 (Register_spec (val_prim val_eq)) => Provide rule_eq.
Hint Extern 1 (Register_spec (val_prim val_add)) => Provide rule_add.
Hint Extern 1 (Register_spec (val_prim val_sub)) => Provide rule_sub.
Hint Extern 1 (Register_spec (val_prim val_ptr_add)) => Provide rule_ptr_add.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Tactics for progressing through proofs *)


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic [xcf] *)

Ltac xcf_get_fun_remove_encs f :=
  constr:(f).

Ltac xcf_get_fun_from_trm t :=
  match t with 
  | trm_apps (trm_val ?f) _ => xcf_get_fun_remove_encs f
  | trm_app ?t1 ?t2 => 
      match t1 with
      | trm_app ?t11 ?t12 => xcf_get_fun_from_trm t1
      | ?f => xcf_get_fun_remove_encs f
      end
  end.

Ltac xcf_get_fun_from_goal tt :=
  match goal with |- triple ?t _ _ => xcf_get_fun_from_trm t end.

Ltac xcf_get_fun tt :=
  xcf_get_fun_from_goal tt.

Ltac xcf_reveal_fun tt :=
  try (let f := xcf_get_fun tt in
       first [ unfold f   
             | match goal with H: f = _ |- _ => rewrite H end ]).

(* TODO: reimplement using LambdaCFLifted strategy *)

Ltac xcf_prepare tt :=
  intros;
  rew_nary; 
  xcf_reveal_fun tt;
  rew_nary; 
  rew_vals_to_trms.

Ltac xcf_post tt := 
  simpl.

Ltac xcf_core n :=
  xcf_prepare tt;
  match goal with |- triple ?t _ _ =>
  match t with  
  | trm_apps (trm_val (val_funs _ _)) _ =>
      applys triple_apps_funs_of_cf_iter n; [ reflexivity | reflexivity | xcf_post tt ]      
  | trm_apps (trm_val (val_fixs _ _ _)) _ =>
      applys triple_apps_fixs_of_cf_iter n; [ reflexivity | reflexivity | xcf_post tt ]
  | _ =>
      applys triple_trm_of_cf_iter n; [ xcf_post tt ]
  end end.

Tactic Notation "xcf" :=
  xcf_core 100%nat.

Tactic Notation "xcf_depth" constr(depth) :=
  xcf_core depth.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic [xseq] *)

Ltac xseq_core tt :=
  applys local_erase; esplit; split.

Tactic Notation "xseq" := 
  xseq_core tt.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic [xlet] *)

Ltac xlet_core tt :=
  applys local_erase; esplit; split.

Tactic Notation "xlet" := 
  xlet_core tt.

Ltac xlet_as_core X :=
  xlet_core tt; [ | intros X ].

Tactic Notation "xlet" "as" simple_intropattern(X) := 
  xlet_as_core X.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic [xif] *)

Ltac xif_post tt :=
  rew_bool_eq.

Ltac xif_core tt :=
  applys local_erase; esplit; splits; 
  [ try reflexivity 
  | xif_post tt
  | xif_post tt ].

Tactic Notation "xif" :=
  xif_core tt.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic [xfail] *)

Ltac xfail_core tt :=
  applys local_erase; unfold cf_fail.

Tactic Notation "xfail" :=
  xfail_core tt.


(* ---------------------------------------------------------------------- *)
(* ################################################################# *)
(* * [xapp] and [xapps] and [xapp as] *)

(** Basic [xapp] implementation 

  Tactic Notation "xapp" constr(E) := 
    applys local_erase; xapplys E.

  Tactic Notation "xapp" := 
    try applys local_erase; 
    xspec;
    let H := fresh "TEMP" in intros H; 
    xapplys H;
    clear H.

*)

Ltac xapp_let_cont tt :=
  let X := fresh "X" in intros X;
  instantiate; try xpull; gen X.

Ltac xapp_as_let_cont tt :=
  instantiate; try xpull.

Ltac xapps_let_cont tt :=
  let X := fresh "X" in intros X;
  instantiate; try xpull; 
  first [ intro_subst | gen X ].

Ltac xapp_template xlet_tactic xapp_tactic xlet_cont :=
  match goal with
  | |- local (cf_let _ _) _ _ => xlet_tactic tt; [ xapp_tactic tt | xlet_cont tt ]
  | |- local (cf_if _ _ _) _ _ => xlet_tactic tt; [ xapp_tactic tt | xlet_cont tt ]
  | |- local (cf_seq _ _) _ _ => xseq; [ xapp_tactic tt | ]
  | _ => xapp_tactic tt
  end.

Ltac xapp_xapply E cont_post :=
  match goal with
  | |- ?F ?H ?Q => is_evar Q; xapplys E
  | |- ?F ?H (fun r => \[r = val_unit] \* ?H') => is_evar H'; xapplys E
    (* TODO: might not be needed *)
  | _ => xapply_core E ltac:(fun tt => hcancel) ltac:(cont_post)
  end.

Ltac xapp_basic_prepare tt ::= 
  try match goal with |- local _ _ _ => apply local_erase end;
  rew_nary.

Ltac hpull_cont tt :=
  try hpull.

Ltac hsimpl_cont tt :=
  hsimpl.

Ltac xapp_with_args E cont_xapply :=
  match E with
  | __ => (* no spec provided *)
     let S := fresh "Spec" in 
     xspec;
     intros S;
     cont_xapply S;
     clear S
  | _ => 
      match list_boxer_of E with 
      | cons (boxer ltac_wild) ?E' => (* only args provided *)
         let S := fresh "Spec" in 
         xspec;
         intros S;
         cont_xapply ((boxer S)::E');
         clear S
      | _ => (* spec and args provided *)
         cont_xapply E
      end 
  end.

Ltac xapp_basic E cont_post tt :=
  xapp_basic_prepare tt; 
  xapp_with_args E ltac:(fun H =>
    xapp_xapply H cont_post).

Ltac xapp_debug tt :=
  xapp_basic_prepare tt; 
  xapp_with_args __ ltac:(fun H => generalize H).

Ltac xapp_core tt :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic __ idcont) ltac:(xapp_let_cont).

Ltac xapp_arg_core E :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic E idcont) ltac:(xapp_let_cont).

Ltac xapp_as_core X :=
  xapp_template ltac:(fun tt => xlet as X) ltac:(xapp_basic __ idcont) ltac:(xapp_as_let_cont).

Ltac xapp_arg_as_core E X :=
  xapp_template ltac:(fun tt => xlet as X) ltac:(xapp_basic E idcont) ltac:(xapp_as_let_cont).

Ltac xapps_core tt :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic __ hpull_cont) ltac:(xapps_let_cont).

Ltac xapps_arg_core E :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic E hpull_cont) ltac:(xapps_let_cont).

Tactic Notation "xapp" := 
  xapp_core tt.
Tactic Notation "xapp" "~" := 
  xapp; auto_tilde.
Tactic Notation "xapp" "*"  := 
  xapp; auto_star.

Tactic Notation "xapp" constr(E) := 
  xapp_arg_core E.
Tactic Notation "xapp" "~" constr(E) := 
  xapp E; auto_tilde.
Tactic Notation "xapp" "*" constr(E) := 
  xapp E; auto_star.

Tactic Notation "xapps" := 
  xapps_core tt.
Tactic Notation "xapps" "~" := 
  xapps; auto_tilde.
Tactic Notation "xapps" "*" := 
  xapps; auto_star.

Tactic Notation "xapps" constr(E) := 
  xapps_arg_core E.
Tactic Notation "xapps" "~" constr(E) := 
  xapps E; auto_tilde.
Tactic Notation "xapps" "*" constr(E) := 
  xapps E; auto_star.

Tactic Notation "xapp" "as" simple_intropattern(X) := 
  xapp_as_core X.
Tactic Notation "xapp" "~" "as" simple_intropattern(X) := 
  xapp as X; auto_tilde.
Tactic Notation "xapp" "*" "as" simple_intropattern(X) := 
  xapp as X; auto_star.

Tactic Notation "xapp" constr(E) "as" simple_intropattern(X) := 
  xapp_arg_as_core E X.
Tactic Notation "xapp" "~" constr(E) "as" simple_intropattern(X) := 
  xapp E as X; auto_tilde.
Tactic Notation "xapp" "*" constr(E) "as" simple_intropattern(X) := 
  xapp E as X; auto_star.

(* TODO: xapps should do hsimpl if not in a let *)


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic [xval] and [xvals] *)

Ltac xval_nohtop_core tt :=
  applys local_erase; unfold cf_val.

Tactic Notation "xval_nohtop" :=
  xval_nohtop_core tt.

Lemma xval_htop_lemma : forall v H Q,
  H ==> Q v \* \Top ->
  local (cf_val v) H Q.
Proof using.
  intros v H Q M. unfold cf_val.
  applys~ local_htop_post (Q \*+ \Top).
  applys local_erase. intros x.
  hpull. intro_subst. hchanges~ M.
Qed. 

Lemma xval_htop_as_lemma : forall v H Q,
  (forall x, x = v -> H ==> Q x \* \Top) ->
  local (cf_val v) H Q.
Proof using. intros v H Q M. applys~ xval_htop_lemma. Qed. 

Ltac xval_template xlet_tactic xval_tactic xlet_cont :=
  match goal with
  | |- local (cf_let _ _) _ _ => xlet_tactic tt; [ xval_tactic tt | xlet_cont tt ]
  | |- local (cf_if _ _ _) _ _ => xlet_tactic tt; [ xval_tactic tt | xlet_cont tt ]
  | _ => xval_tactic tt
  end.

Ltac xval_basic tt :=
  match goal with
  | |- local ?F ?H ?Q => is_evar Q; applys local_erase; applys refl_rel_incl'
  | _ => applys xval_htop_lemma 
  end.

Ltac xval_as_basic X EX :=
  match goal with
  | |- local ?F ?H ?Q => is_evar Q; applys local_erase; applys refl_rel_incl'
  | _ => applys xval_htop_as_lemma; intros X EX
  end.

Ltac xval_core tt :=
  xval_template ltac:(fun tt => xlet) ltac:(xval_basic) ltac:(xapp_let_cont).

Ltac xval_as_core X :=
  match goal with
  | |- local (cf_val _) _ _ => let EX := fresh "E" X in xval_as_basic X EX
  | _ => xval_template ltac:(fun tt => xlet as X) ltac:(xval_basic) ltac:(xapp_as_let_cont)
  end.

Ltac xvals_core tt :=
  match goal with
  | |- local (cf_val _) _ _ => xval_basic tt; hsimpl
  | _ => xval_template ltac:(fun tt => xlet) ltac:(xval_basic) ltac:(xapps_let_cont)
  end.

Tactic Notation "xval" := 
  xval_core tt.
Tactic Notation "xval" "~" := 
  xval; auto_tilde.
Tactic Notation "xval" "*"  := 
  xval; auto_star.

Tactic Notation "xvals" := 
  xvals_core tt.
Tactic Notation "xvals" "~" := 
  xvals; auto_tilde.
Tactic Notation "xvals" "*" := 
  xvals; auto_star.

Tactic Notation "xval" "as" simple_intropattern(X) := 
  xval_as_core X.
Tactic Notation "xval" "~" "as" simple_intropattern(X) := 
  xval as X; auto_tilde.
Tactic Notation "xval" "*" "as" simple_intropattern(X) := 
  xval as X; auto_star.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic [xwhile] *)

Ltac xwhile_template xwhile_tactic xseq_cont :=
  match goal with
  | |- local (cf_seq _ _) _ _ => xseq; [ xwhile_tactic tt | xseq_cont tt ]
  | _ => xwhile_tactic tt
  end.

Ltac xwhile_intros_all R LR HR :=
  intros R LR; hnf; intros HR.

Ltac xwhile_intros R :=
  let LR := fresh "L" R in
  let HR := fresh "H" R in
  xwhile_intros_all R LR HR.
  
Ltac xwhile_basic xwhile_intros_tactic :=
  applys local_erase;
  xwhile_intros_tactic tt.

Ltac xwhile_core xwhile_tactic :=
  xwhile_template ltac:(xwhile_tactic) ltac:(fun tt => xpull).

Tactic Notation "xwhile" "as" ident(R) := 
  xwhile_core ltac:(fun tt => xwhile_basic ltac:(fun tt => xwhile_intros R)).

Tactic Notation "xwhile" "as" ident(R) ident(LR) ident(HR) := 
  xwhile_core ltac:(fun tt => xwhile_basic ltac:(fun tt => xwhile_intros_all R LR HR)).




(* ********************************************************************** *)
(* ################################################################# *)
(* * Bonus *)

Lemma triple_app_fun2_of_cf_iter : forall n F v1 v2 x1 x2 t H Q,
  F = val_fun2 x1 x2 t ->
  x1 <> x2 ->
  func_iter n cf_def cf (subst x2 v2 (subst x1 v1 t)) H Q ->
  triple (F v1 v2) H Q.
Proof using.
  introv EF N M. applys* rule_app_fun2.
  applys* triple_trm_of_cf_iter.
Qed.

