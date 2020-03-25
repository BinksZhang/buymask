(** 

This file formalizes:
- heap entailement, written [H ==> H'],
- a functor that may be instantiated con construct, e.g. 
  -- a standard Separation Logic,
  -- a Separation Logic extended with credits,
  -- a Separation Logic extended with temporary read-only permissions.

The functor in this file assumes:
- a type for heaps
- a definition of \[P] (lifting of pure predicates) and of \* (star)
- five properties of these operators
  (neutral element, commutativity and associativity of star,
   extrusion of existentials, and frame property for entailment).

The functor provides:
- derived heap operators: \[], (Hexists _,_), \Top
- a number of useful lemmas for reasoning about these operators
- notation for representation predicates: [x ~> R X].

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
Require Export LibCore.
Require Export TLCbuffer.


(* ********************************************************************** *)
(* ################################################################# *)
(** * Predicate extensionality, specialized to heap predicates *)

(** Predicate extensionality follows from functional extensional
    and propositional extensionality, which we take as axiom 
    (in TLC's LibAxioms file). *)

Lemma hprop_extens : forall A (H1 H2:A->Prop),
  (forall h, H1 h <-> H2 h) ->
  (H1 = H2).
Proof using.
  introv M. apply fun_ext_1. intros h. apply* prop_ext.
Qed.


(* ********************************************************************** *)
(* ################################################################# *)
(** * Entailment *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Definition of entailment *)

(* --TODO: define [himpl] to mean [pred_incl] and [pimpl] to mean [rel_incl'] *)

(** TLC defines [pred_le P Q] as [forall x, P x -> Q x]. *)

Notation "P ==> Q" := (pred_incl P Q) 
  (at level 55, right associativity) : heap_scope.

(* [rel_incl'] is like TLC's [rel_incl] but defined in terms of [pred_incl]
   so that after [intros r] we get an entailment. *)

Definition rel_incl' A B (P Q:A->B->Prop) :=  
  forall r, pred_incl (P r) (Q r).

Notation "P ===> Q" := (rel_incl' P Q) 
  (at level 55, right associativity) : heap_scope.

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Properties of entailment *)

(*--LATER: update names to match new naming conventions *)

Section HimplProp.
Variable A : Type.
Implicit Types H : A -> Prop.

Hint Unfold pred_incl.

(** Entailment is reflexive, symmetric, transitive *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) -> 
  (H2 ==> H3) -> 
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) -> 
  (H2 ==> H1) -> 
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

(** Paragraphe of the definition, used by tactics *)

Lemma himpl_inv : forall H1 H2 (h:A),
  (H1 ==> H2) -> 
  (H1 h) -> 
  (H2 h).
Proof using. auto. Qed.

(** Reformulation of reflexivity, used by tactics *)

Lemma himpl_of_eq : forall H1 H2,
  H1 = H2 -> 
  H1 ==> H2.
Proof. intros. subst. applys~ himpl_refl. Qed.

Lemma himpl_of_eq_sym : forall H1 H2,
  H1 = H2 -> 
  H2 ==> H1.
Proof. intros. subst. applys~ himpl_refl. Qed.

End HimplProp.

Arguments himpl_of_eq [A] [H1] [H2].
Arguments himpl_of_eq_sym [A] [H1] [H2].
Arguments himpl_antisym [A] [H1] [H2].

Hint Resolve himpl_refl.

(** Reflexivity for postconditions *)

Lemma refl_rel_incl' : forall A B (Q:A->B->Prop),
  Q ===> Q.
Proof using. apply refl_rel_incl. Qed.

Hint Resolve refl_rel_incl'.



(* ********************************************************************** *)
(* ################################################################# *)
(** * Assumptions of the functor *)

Module Type SepLogicCore.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Types *)

(** Type of heaps *)

Parameter heap : Type.

(** Type of heap predicates *)

Definition hprop := heap -> Prop.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Operators *)

(** Empty heap predicate, written [ \[] ]. *)

Parameter hempty : hprop.

Notation "\[]" := (hempty) 
  (at level 0) : heap_scope.

(** Separation Logic star, written [H1 \* H2]. *)

Parameter hstar : hprop -> hprop -> hprop.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

(** Notation for applying star to a post-condition,
  written [Q \*+ H], short for [fun x => (Q x \* H)]. *)

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.

(** Existential lifted to heap predicates, 
  written [Hexists x, H] *)

Definition hexists A (J:A->hprop) : hprop := 
  fun h => exists x, J x h.

(** Pure propositions lifted to heap predicates,
  written [ \[P] ].

  Remark: the definition below is equivalent to
  [fun h => (hempty h /\ P)]. *)

Definition hpure (P:Prop) : hprop := 
  hexists (fun (p:P) => hempty).

Notation "\[ P ]" := (hpure P) 
  (at level 0, P at level 99, format "\[ P ]") : heap_scope.

(** The "Top" predicate, written [\Top], which holds of any heap,
  implemented as [Hexists H, H]. *)

Definition htop : hprop := 
  hexists (fun (H:hprop) => H).

Notation "\Top" := (htop) : heap_scope. 

(* Remark: disjunction on heap predicates is not needed in practice, 
  because we use pattern matching and conditional construct from the 
  logic. If we wanted, we could define it as follows:

  Definition hor (H1 H2 : hprop) : hprop := 
    fun h => H1 h \/ H2 h.
*)

(* Remark: non-separating conjunction is not defined, because we 
  never need it. If we wanted, we could define it as follows:
 
  Definition hand (H1 H2 : hprop) : hprop := 
    fun h => H1 h /\ H2 h.
*)

(* Remark: magic wand construct is not defined here, because we 
  rarely need it. If we wanted, we could define it as follows:
 
  Definition hwand (H1 H2 : hprop) : hprop := 
    Hexists H, (H \* [H \* H1 ==> H2]).
*)

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Properties *)

(** Empty is left neutral for star *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** Star is commutative *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** Star is associative *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** Extrusion of existentials out of star *)

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).

(** The frame property (star on H2) holds for entailment *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' -> 
  (H1 \* H2) ==> (H1' \* H2).

(** One additional technical lemma, useful for helping with 
    the setup of tactics for Separation Logic goals.
    It essentially asserts that the predicate called [local],
    and defined later in [SepTactics.v], is idempotent. *)

Parameter local_local_aux : forall B,
  let local := fun (F:(hprop->(B->hprop)->Prop)) (H:hprop) (Q:B->hprop) =>
    ( forall h, H h -> exists H1 H2 Q1,
       (H1 \* H2) h
    /\ F H1 Q1
    /\ Q1 \*+ H2 ===> Q \*+ \Top) in
  (\Top \* \Top = \Top) ->
  forall (F:(hprop->(B->hprop)->Prop)) (H:hprop) (Q:B->hprop),
  local (local F) H Q -> 
  local F H Q.

End SepLogicCore.


(* ********************************************************************** *)
(* ################################################################# *)
(** * Functor *)

Module SepLogicSetup (SL : SepLogicCore).
Export SL.

Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types P : Prop.

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Additional notation for entailment *)

Delimit Scope heap_scope with heap.

(** [H1 ==+> H2] is short for [H1 ==> H1 \* H2] *)

Notation "H1 ==+> H2" := (H1%heap ==> H1%heap \* H2%heap) 
  (at level 55) : heap_scope.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Additional notation for lifted existentials *)

Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
  (at level 39, x1 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
  (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 x4 , H" :=
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, H at level 50) : heap_scope.
Notation "'Hexists' x1 x2 x3 x4 x5 , H" :=
  (Hexists x1, Hexists x2, Hexists x3, Hexists x4, Hexists x5, H)
  (at level 39, x1 ident, x2 ident, x3 ident, x4 ident, x5 ident, H at level 50) : heap_scope.

Notation "'Hexists' x1 : T1 , H" := (hexists (fun x1:T1 => H))
  (at level 39, x1 ident, H at level 50, only parsing) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) , H" := (hexists (fun x1:T1 => H))
  (at level 39, x1 ident, H at level 50, only parsing) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) ( x2 : T2 ) , H" := (Hexists (x1:T1), Hexists (x2:T2), H)
  (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
Notation "'Hexists' ( x1 : T1 ) ( x2 : T2 ) ( x3 : T3 ) , H" := (Hexists (x1:T1), Hexists (x2:T2), Hexists (x3:T3), H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Properties of [hprop] *)

Global Instance hinhab : Inhab hprop.
Proof using. intros. apply (Inhab_of_val hempty). Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Derived properties of [hempty], [hstar], [hpure], and [hexists] *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. 
  applys~ hstar_comm. 
  applys~ hstar_hempty_l.
Qed.

Lemma hstar_pure : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. extens. unfold hpure.
  rewrite hstar_hexists. 
  rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hpure_intro : forall P h,
  \[] h ->
  P -> 
  \[P] h.
Proof using. 
  introv M N. rewrite <- (hstar_hempty_l \[P]).
  rewrite hstar_comm. rewrite~ hstar_pure.
Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using. 
  introv M. rewrite <- hstar_pure. 
  rewrite~ hstar_hempty_r. 
Qed.

Lemma hempty_eq_hpure_true : 
  \[] = \[True].
Proof using. 
  applys pred_ext_1. intros h. iff M.
  { applys* hpure_intro. }
  { forwards*: hpure_inv M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using. 
  intros. applys pred_ext_1. intros h. rewrite hstar_pure. iff M.
  { false*. } { lets: hpure_inv M. false*. }
Qed.

Lemma hpure_eq_hexists_empty : forall P,
  \[P] = (Hexists (p:P), \[]).
Proof using. auto. Qed.

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,  
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,  
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Derived properties of [himpl] *)

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' -> 
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_hprop_l : forall P H H',
  (P -> H ==> H') -> 
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_pure in Hh. applys* W. 
Qed.

Lemma himpl_hprop_r : forall P H H',
  P -> 
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using.
  introv HP W. intros h Hh. rewrite~ hstar_pure.
Qed.

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) -> 
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) -> 
  H ==> (hexists J).
Proof using. introv W h. exists x. apply~ W. Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Properties of [htop] *)

Lemma htop_intro : forall h, 
  \Top h.
Proof using. intros. exists~ (=h). Qed.

Lemma htop_eq : 
  \Top = (Hexists H, H).
Proof using. auto. Qed.

Lemma himpl_htop_r : forall H H',
  H ==> H' ->
  H ==> H' \* \Top.
Proof using.
  introv M. unfold htop. rewrite (hstar_comm H').
  rewrite hstar_hexists.
  applys himpl_hexists_r \[]. rewrite~ hstar_hempty_l.
Qed.

Lemma htop_hstar_htop : 
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym. 
  { unfold htop. rewrite hstar_hexists.
    applys himpl_hexists_l. intros H.
    rewrite hstar_comm.
    rewrite hstar_hexists.
    applys himpl_hexists_l. intros H'.
    applys~ himpl_hexists_r (H' \* H). }
  { applys~ himpl_htop_r. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary lemma showing that reasoning rule for extracting 
   pure propositions from preconditions is just a special case 
   of the reasoning rule for extracting existentials from preconditions. *)

Lemma rule_extract_hprop_from_extract_hexists :
  forall (T:Type) (F:hprop->(T->hprop)->Prop),
  (forall (A:Type) (J:A->hprop) (Q:T->hprop),
    (forall x, F (J x) Q) ->
    F (hexists J) Q) ->
  (forall P H Q,
    (P -> F H Q) ->
    F (\[P] \* H) Q).
Proof using.
  introv M. introv N. rewrite hpure_eq_hexists_empty.
  rewrite hstar_hexists.
  applys M. rewrite~ hstar_hempty_l.
Qed.

Arguments rule_extract_hprop_from_extract_hexists [T].


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Notation for representation predicates *)

(** The arrow notation typically takes the form [x ~> R x],
   to indicate that [X] is the logical value that describes the
   heap structure [x], according to the representation predicate [R].
   It is just a notation for the heap predicate [R X x]. *)

Definition repr (A:Type) (S:A->hprop) (x:A) : hprop :=
  S x.

Notation "x '~>' S" := (repr S x)
  (at level 33, no associativity) : heap_scope.

(** [x ~> Id X] holds when [x] is equal to [X] in the empty heap.
   [Id] is called the identity representation predicate. *)

Definition Id {A:Type} (X:A) (x:A) :=
  \[ X = x ].


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Set operators to be opaque *)

Global Opaque hempty hpure hstar hexists htop repr. 


End SepLogicSetup.


