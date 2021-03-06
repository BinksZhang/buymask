(**

This file formalizes standard Separation Logic. It contains:
- a definition of heaps as finite maps from location to values,
- an instantiation of the functor from the file [SepFunctor.v],
- an instantiation of the functor from the file [SepTactics.v],
- a definition of triples,
- statement and proofs of structural rules,
- statement and proofs of rules for terms,
- statement and proofs of rules for primitive operations,
- bonuses: an alternative definition of triples, and derived rules.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
Require Export LambdaSemantics SepTactics.
Open Scope fmap_scope.

Ltac auto_star ::= jauto.

Implicit Types v w : val.
Implicit Types t : trm.
Implicit Types n : int.
Implicit Types l : loc.
Implicit Types f : field.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Construction of the logic *)

Module SepBasicCore.

(** All the definitions from this section are explained in the
  [Module Type SepLogicCore], from file [SepFunctor.v]. *)


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Types *)

(** A heap is a state (a finite map from location to values)
   as defined in [LambdaSemantics.v]. *)

Definition heap : Type := (state)%type.

(** A heap predicate, type [hprop] is a predicate over such heaps. *)

Definition hprop := heap -> Prop.

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Operations on heaps *)

(** For uniformity with other instantiations of the Separation Logic
  functor, we introduce local names for operations and lemmas on heaps. *)

Notation "'heap_empty'" := (fmap_empty : heap) : heap_scope.

Notation "h1 \u h2" := (fmap_union h1 h2)
   (at level 37, right associativity) : heap_scope.

Definition heap_union_empty_l := fmap_union_empty_l.

Definition heap_union_empty_r := fmap_union_empty_r.

Definition heap_union_comm := fmap_union_comm_of_disjoint.

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Operators *)

(** Empty heap predicate: [ \[] ] *)

Definition hempty : hprop := 
  fun h => h = heap_empty.

(** Separating conjunction: [H1 \* H2] *)

Definition hstar (H1 H2 : hprop) : hprop := 
  fun h => exists h1 h2, H1 h1 
                      /\ H2 h2 
                      /\ (\# h1 h2)
                      /\ h = h1 \+ h2.

(** Lifting of existentials: [Hexists x, H] *)

Definition hexists A (J : A -> hprop) : hprop := 
  fun h => exists x, J x h.

(** Lifting of pure predicates: [ \[P] ] *)

Definition hpure (P:Prop) : hprop := 
  hexists (fun (p:P) => hempty).

(** The top heap predicate: [ \Top ], same as [Hexists H, H] *)

Definition htop := 
  hexists (fun (H:hprop) => H).


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Notation *)

Notation "\[]" := (hempty) 
  (at level 0) : heap_scope.

Notation "\[ P ]" := (hpure P) 
  (at level 0, P at level 99, format "\[ P ]") : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.

Notation "\Top" := (htop) : heap_scope. 

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Tactic for automation *)

(* TODO: check how much is really useful *)

Hint Extern 1 (_ = _ :> heap) => fmap_eq.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (\# _ _) => fmap_disjoint_pre.
Hint Extern 1 (\# _ _ _) => fmap_disjoint_pre.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Properties of empty *)

Lemma hempty_intro : 
  \[] heap_empty.
Proof using. hnfs~. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = heap_empty.
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Properties of star *)

Section Properties.

Hint Resolve hempty_intro.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  \# h1 h2 ->
  (H1 \* H2) (h1 \+ h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_hempty_l : forall H,
  hempty \* H = H.
Proof using.
  intros. applys hprop_extens. intros h.
  iff (h1&h2&M1&M2&D&U) M.
  { forwards E: hempty_inv M1. subst.
    rewrite~ heap_union_empty_l. }
  { exists~ heap_empty h. }
Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using. 
  intros H1 H2. unfold hprop, hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U); rewrite~ heap_union_comm in U; exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using. 
  intros H1 H2 H3. applys hprop_extens. intros h. split.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { exists* h2 h3. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { exists* h1 h2. } }
Qed. 


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Interaction of star with other operators *)

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys hprop_extens. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. exists~ x. }
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' -> 
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma local_local_aux : forall (B:Type),
  let local := fun (F:(hprop->(B->hprop)->Prop)) (H:hprop) (Q:B->hprop) =>
    ( forall h, H h -> exists H1 H2 Q1,
       (H1 \* H2) h
    /\ F H1 Q1
    /\ Q1 \*+ H2 ===> Q \*+ \Top) in
  (\Top \* \Top = \Top) ->
  forall F (H:hprop) (Q:B->hprop),
  local (local F) H Q -> 
  local F H Q.
Proof using.
  intros B local R F H Q M. introv PH.
  lets (H1&H2&Q1&PH12&N&Qle): M (rm PH).
  lets (h1&h2&PH1&PH2&Ph12&Fh12): (rm PH12).
  lets (H1'&H2'&Q1'&PH12'&N'&Qle'): N (rm PH1).
  exists H1' (H2' \* H2) Q1'. splits.
  { rewrite <- hstar_assoc. exists~ h1 h2. }
  { auto. }
  { intros x. lets R1: himpl_frame_l \Top ((rm Qle) x).
    lets R2: himpl_frame_l H2 ((rm Qle') x).
    rewrite <- R. repeat rewrite hstar_assoc in *.
    applys himpl_trans R1. applys himpl_trans R2.
    rewrite~ (@hstar_comm H2). }
Qed.

End Properties.

End SepBasicCore.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Properties of the logic *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Functor instantiations *)

(** Here, we instantiate the functors to obtained derived definitions,
  lemmas, notation, and tactics. *)

Module Export SepBasicSetup := SepLogicSetup SepBasicCore.
Module Export SepBasicTactics := SepLogicTactics SepBasicCore.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Singleton heap *)

(** Definition of the singleton heap predicate, written [r ~~~> v] *)

Definition hsingle (l:loc) (v:val) : hprop := 
  fun h => h = fmap_single l v /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma hstar_hsingle_same_loc_disjoint : forall l v1 v2,
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* fmap_disjoint_single_single_same_inv.
Qed.

Lemma hsingle_not_null : forall l v,
  (l ~~~> v) ==> (l ~~~> v) \* \[l <> null].
Proof using.
  introv. intros h (Hh&Nl).
  exists h heap_empty. splits~. 
  { unfold hsingle. splits~. }
  { applys~ hpure_intro. applys~ hempty_intro. } 
Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Singleton field heap *)

(** Definition of the heap predicate describing a single record field,
  written [l `.` f ~> v]. *)

Definition hfield (l:loc) (f:field) (v:val) : hprop := 
  (l+f)%nat ~~~> v \* \[ l <> null ]. 

Notation "l `.` f '~~~>' v" := (hfield l f v)
  (at level 32, f at level 0, no associativity,
   format "l `.` f  '~~~>'  v") : heap_scope.

Lemma hstar_hfield_same_loc_disjoint : forall l f v1 v2,
  (l`.`f ~~~> v1) \* (l`.`f ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hfield. hpull ;=> N1 N2.
  applys hstar_hsingle_same_loc_disjoint.
Qed.

Lemma hfield_not_null : forall l f v,
  (l`.`f ~~~> v) ==> (l`.`f ~~~> v) \* \[l <> null].
Proof using.
  intros. subst. unfold hfield. hchanges~ hsingle_not_null.
Qed.

Arguments hfield_not_null : clear implicits.

Lemma hfield_eq_fun_hsingle : 
  hfield = (fun l f v => ((l+f)%nat ~~~> v) \* \[l <> null]).
Proof using. intros. auto. Qed.

Lemma hfield_to_hsingle : forall l f v,
  (l`.`f ~~~> v) ==> ((l+f)%nat ~~~> v) \* \[l <> null].
Proof using. intros. auto. Qed.

Lemma hsingle_to_hfield : forall l f v,
  l <> null ->
  ((l+f)%nat ~~~> v) ==> l`.`f ~~~> v.
Proof using. intros. unfold hfield. hsimpl~. Qed.

Arguments hsingle_to_hfield : clear implicits.

Global Opaque hsingle hfield.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Configuration of [hsimpl] *)

(* ================================================================= *)
(* ** Configure [hsimpl] to make it aware of [hsingle] *)

Ltac hcancel_hook H ::=
  match H with 
  | hsingle _ _ => hcancel_try_same tt 
  | hfield _ _ _ => hcancel_try_same tt 
  end.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Auxiliary definitions for [rule_if] and [rule_seq] *)

Definition is_val_bool (v:val) : Prop :=
  exists b, v = val_bool b.

Definition is_val_unit (v:val) : Prop :=
  v = val_unit.

  
(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Auxiliary definitions for [rule_alloc] *)

Fixpoint Alloc (k:nat) (l:loc) := 
  match k with
  | O => \[]
  | S k' => (Hexists v, l ~~~> v) \* (Alloc k' (S l)%nat)
  end.

Lemma Alloc_zero_eq : forall l,
  Alloc O l = \[].
Proof using. auto. Qed.

Lemma Alloc_succ_eq : forall l k,
  Alloc (S k) l = (Hexists v, l ~~~> v) \* Alloc k (S l)%nat.
Proof using. auto. Qed.

Global Opaque Alloc.

Hint Rewrite Alloc_zero_eq Alloc_succ_eq : rew_Alloc.

Tactic Notation "rew_Alloc" := 
  autorewrite with rew_Alloc.

Lemma Alloc_fmap_conseq : forall l k v, 
  l <> null ->
  (Alloc k l) (fmap_conseq l k v).
Proof using.
  Transparent loc null.
  introv N. gen l. induction k; intros; rew_Alloc.
  { rewrite fmap_conseq_zero. applys~ hempty_intro. }
  { rewrite fmap_conseq_succ. applys hstar_intro.
    { applys hexists_intro. split~. }
    { applys IHk. unfolds loc, null. math. }
    { applys~ fmap_disjoint_single_conseq. } }
Qed.

Lemma Alloc_split_eq : forall k1 (k:nat) p,
  (k1 <= k)%nat ->
  Alloc k p = Alloc k1 p \* Alloc (k-k1)%nat (p + k1)%nat.
Proof using.
  Transparent loc. 
  intros k1 k. gen k1. induction k; introv N. 
  { math_rewrite (k1 = 0%nat). rew_Alloc. rew_heap~. }
  { destruct k1 as [|k1']; rew_nat. 
    { rew_Alloc. rew_heap~. }
    { rew_Alloc. rewrite (IHk k1'); [|math]. rew_heap~. } }
Qed.

Arguments Alloc_split_eq : clear implicits.

Lemma Alloc_split_inv : forall k1 k2 p,
  Alloc k1 p \* Alloc k2 (p + k1)%nat ==> Alloc (k1+k2)%nat p.
Proof using.
  intros. rewrites (Alloc_split_eq k1 (k1+k2)%nat p); [|math]. rew_nat~.
Qed.

(** Tactic for helping reasoning about concrete calls to [alloc] *)

Ltac simpl_abs := (* TODO: will be removed once [abs] computes *)
  match goal with 
  | |- context [ abs 0 ] => change (abs 0) with 0%nat
  | |- context [ abs 1 ] => change (abs 1) with 1%nat
  | |- context [ abs 2 ] => change (abs 2) with 2%nat
  | |- context [ abs 3 ] => change (abs 3) with 3%nat
  end.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Reasoning Rules *)


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Definition of triples *)

(** This is a total-correctness definition of a triple, for a
  deterministic language. (Remark: our definition makes sense even though
  technically allocation picks fresh locations in a non-deterministic
  manner, because identity of locations do not influence program 
  behaviors.) 
  
  Below, the evaluation of [t] in state [h] terminates on value [v]
  in state [h'], when [h] satisfies the pre-condition [H] starred 
  with a heap predicate [H'] describing the framed part, and where
  the final state [h'] satisfies the post-condition [Q] applied to the 
  result value [v], starred with the framed part [H'], and starred
  with [\Top] to account for garbage collection.
  
  Remark: in a C-style language, [\Top] needs to be defined in a
  more restrictive way to enforce deallocation of malloc-ed blocks. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall H' h,  
  (H \* H') h -> 
  exists h' v, 
       red h t h' v
    /\ (Q v \* \Top \* H') h'.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Triples satisfy the [local] predicate *)

(** This lemma is exploited indirectly by tactics such as [xapply],
  which perform application of lemmas modulo framing. *)

Lemma is_local_triple : forall t,
  is_local (triple t).
Proof using. 
  intros. applys pred_ext_2. intros H Q. iff M.
  { intros h Hh. forwards (h'&v&N1&N2): M \[] h. { hhsimpl. } 
    exists H \[] Q. splits~. { hhsimpl. } { hsimpl. } }
  { intros H' h Hh. lets (h1&h2&N1&N2&N3&N4): Hh. hnf in M.
    lets (H1&H2&Q1&R1&R2&R3): M N1.
    forwards (h'&v&S1&S2): R2 (H2\*H') h.
    { subst h. rewrite <- hstar_assoc. exists~ h1 h2. }
    exists h' v. splits~. rewrite <- htop_hstar_htop.
    applys himpl_inv S2.
    hchange (R3 v). rew_heap.
    rewrite (hstar_comm_assoc \Top H'). hsimpl. }  
Qed.

(** Make tactic [xlocal] aware that triples are local *)

Ltac xlocal_base tt ::=
  try first [ applys is_local_local 
            | applys is_local_triple ].


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Structural rules *)

Lemma rule_extract_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_hexists in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma rule_extract_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  intros t. applys (rule_extract_hprop_from_extract_hexists (triple t)).
  applys rule_extract_hexists.
Qed.

Lemma rule_consequence : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. 
  introv MH M MQ. intros HF h N.
  forwards (h'&v&R&K): (rm M) HF h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl. hchanges (MQ v). }
Qed.

Lemma rule_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using. 
  introv M. intros HF h N. rewrite hstar_assoc in N.
  forwards (h'&v&R&K): (rm M) (H' \* HF) h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. }
Qed.

Lemma rule_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v&R&K): (rm M) HF h.  
  exists h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. } 
Qed.

Lemma rule_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. applys rule_htop_post. applys~ rule_frame.
Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Term rules *)

Lemma rule_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF h N. exists h v. splits.
  { applys red_val. }
  { hhsimpl. hchanges M. }
Qed.

Lemma rule_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M. intros HF h N. exists___. splits.
  { applys red_fun. }
  { hhsimpl. hchanges M. }
Qed.

Lemma rule_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. intros HF h N. exists___. splits.
  { applys red_fix. }
  { hhsimpl. hchanges M. }
Qed.

Lemma rule_if : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (b:bool), triple (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. intros HF h N.
  forwards* (h1'&v&R1&K1): (rm M1) HF h.
  tests C: (is_val_bool v).
  { destruct C as (b&E). subst. forwards* (h'&v'&R&K): (rm M2) h1'.
    exists h' v'. splits~. 
    { applys* red_if. }
    { rewrite <- htop_hstar_htop. rew_heap~. } }
  { specializes M3 C.
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange M3. hsimpl. hsimpl. } 
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. } (* TODO: shorten this *)
Qed.

Lemma rule_if_bool : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_if (fun r => \[r = val_bool b] \* H). 
  { applys rule_val. hsimpl~. }
  { intros b'. applys~ rule_extract_hprop. intros E. inverts E. case_if*. }
  { intros v' N. hpull. intros E. inverts~ E. false N. hnfs*. } 
Qed.

Lemma rule_seq : forall t1 t2 H Q Q1,
  triple t1 H Q1 ->
  triple t2 (Q1 val_unit) Q ->
  (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False]) ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 M3. intros HF h N.
  lets~ (h1'&v1&R1&K1): (rm M1) HF h.
  asserts E: (v1 = val_unit).
  { specializes M3 v1. applys not_not_inv. intros E. 
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange~ M3. hsimpl. } 
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. }
    (* TODO: shorten this, and factorize with rule_if *) 
  subst. forwards* (h2'&v2&R2&K2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_seq R2. }
  { rewrite <- htop_hstar_htop. hhsimpl. }  
Qed.

Lemma rule_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst x X t2) (Q1 X) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  lets~ (h1'&v1&R1&K1): (rm M1) HF h.
  forwards* (h2'&v2&R2&K2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_let R2. }
  { rewrite <- htop_hstar_htop. hhsimpl. } 
Qed.

Lemma rule_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  triple (substs xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using. 
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_app_funs_val. }
Qed.

Lemma rule_apps_fixs : forall xs f F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  triple (subst f F (substs xs Vs t1)) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using. 
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_app_fixs_val. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Rules for loops *)

Lemma rule_while_raw : forall t1 t2 H Q,
  triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  triple (trm_while t1 t2) H Q.
Proof using. 
  introv M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { applys* red_while. }
Qed.

Lemma rule_while : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.
Proof using. 
  introv M. applys M. introv K. applys rule_while_raw. applys K.
Qed.

Lemma rule_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2 H,
  let Q := (fun r => \[r = val_unit] \* Hexists Y, I false Y) in
  wf R ->
  (H ==> (Hexists b X, I b X) \* \Top) -> (* TODO: replace \top with H' *)
  (forall t b X,
      (forall b' X', R X' X -> triple t (I b' X') Q) ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q) ->
  triple (trm_while t1 t2) H Q. (* TODO: allow for weakening on Q *)
Proof using.
  introv WR H0 HX. xchange (rm H0). xpull ;=> b0 X0.
  rewrite hstar_comm. applys rule_htop_pre. gen b0.
  induction_wf IH: WR X0. intros. applys rule_while_raw. 
  applys HX. intros b' X' HR'. applys~ IH.
Qed.

Lemma rule_for_raw : forall (x:var) (n1 n2:int) t3 H (Q:val->hprop),
  triple (
    If (n1 <= n2) 
      then (trm_seq (subst x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using. 
  introv M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { applys~ red_for. }
Qed.

(* TODO: simplify proof using rule_for_raw *)
Lemma rule_for_gt : forall x n1 n2 t3 H Q,
  n1 > n2 ->
  (fun r => \[r = val_unit] \* H) ===> (Q \*+ \Top) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using. 
  introv N M. intros H' h Hf. exists h val_unit. splits~.
  { applys* red_for_gt. }
  { hhsimpl. hchange~ M. hsimpl. }
Qed.

(* TODO: simplify proof using rule_for_raw *)
Lemma rule_for_le : forall Q1 x n1 n2 t3 H Q,
  n1 <= n2 ->
  triple (subst x n1 t3) H Q1 ->
  triple (trm_for x (n1+1) n2 t3) (Q1 val_unit) Q ->
  (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False]) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using. 
  introv N M1 M2 M3. intros HF h Hf. forwards (h1'&v1&R1&K1): (rm M1) Hf.
  asserts E: (v1 = val_unit).
  { specializes M3 v1. applys not_not_inv. intros E. 
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange~ M3. hsimpl. } 
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. }
    (* TODO: shorten this, and factorize with rule_if *) 
  subst. forwards* (h2'&v2&R2&K2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys* red_for_le. }
  { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

(* TODO: simplify proof using rule_for_raw *)
Lemma rule_for : forall x (n1 n2:int) t3 H Q,
  (If (n1 <= n2) then
    (exists Q1,
      triple (subst x n1 t3) H Q1 /\
      triple (trm_for x (n1+1) n2 t3) (Q1 val_unit) Q /\
      (forall v, ~ is_val_unit v -> (Q1 v) ==> \[False])) 
  else 
    ((fun r => \[r = val_unit] \* H) ===> Q)) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. case_if.
  { destruct M. applys* rule_for_le. }
  { xapplys* rule_for_gt. { math. } intros r. hchanges* M. }
Qed.

(* TODO: simplify proof using rule_for_raw *)
Lemma rule_for_inv : forall (I:int->hprop) H' x n1 n2 t3 H Q,
  (n1 <= n2+1) ->
  (H ==> I n1 \* H') ->
  (forall i, n1 <= i <= n2 -> 
     triple (subst x i t3) (I i) (fun r => \[r = val_unit] \* I (i+1))) ->
  (I (n2+1) \* H' ==> Q val_unit \* \Top) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M1 M2 M3. xchange (rm M1). gen N M2.
  induction_wf IH: (wf_upto (n2+1)) n1; intros. 
  asserts M4: (triple (trm_for x (n2 + 1)%I n2 t3) (I (n2+1) \* H') Q).
  { applys rule_for_gt. { math. } 
    { intros r. hpull ;=> E. subst. hchanges M3. } } 
  tests C: (n1 = n2+1).
  { xapplys M4. }
  { applys rule_for_le. 
    { math. }
    { xapplys M2. { math. } }
    { simpl. xpull ;=> _. tests C': (n1 = n2).
      { xapplys M4. }
      { xapplys IH. { hnf; math. } { math. } { intros. applys M2. math. } } }
    { intros v Nv. hpull. } } 
Qed.


(* ---------------------------------------------------------------------- *)
(** Primitive functions over the state *)

Section RulesStateOps.
Transparent hstar hsingle hfield hexists loc null.

Lemma rule_ref : forall v,
  triple (val_ref v) 
    \[] 
    (fun r => Hexists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros HF h N.
  forwards~ (l&Dl&Nl): (fmap_single_fresh null h v).
  sets h1': (fmap_single l v).
  exists (h1' \u h) (val_loc l). splits~.
  { applys~ red_ref. }
  { exists h1' h. split. 
    { exists l. applys~ himpl_hprop_r. unfold h1'. hnfs~. }
    { splits~. hhsimpl~. } }
Qed.

Lemma rule_get : forall v l,
  triple (val_get (val_loc l)) 
    (l ~~~> v) 
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. intros HF h N. exists h v. splits~.
  { applys red_get. destruct N as (?&?&(?&?)&?&?&?).
    subst h. applys~ fmap_union_single_l_read. }
  { rew_heap. rewrite hstar_pure. split~. hhsimpl~. }
Qed.

Lemma rule_set : forall w l v,
  triple (val_set (val_loc l) w) 
    (l ~~~> v) 
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros HF h N. destruct N as (h1&h2&(N0&N1)&N2&N3&N4).
  hnf in N1. sets h1': (fmap_single l w).
  exists (h1' \u h2) val_unit. splits~.
  { applys red_set. subst h h1. applys~ fmap_union_single_to_update. }
  { rew_heap. rewrite hstar_pure. split~.
    { exists h1' h2. splits~.
      { hnfs~. }
      { hhsimpl~. }
      { subst h1. applys~ fmap_disjoint_single_set v. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** Alloc function *)

Lemma rule_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n) 
    \[] 
    (fun r => Hexists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
Proof using. (* Note: [abs n] currently does not compute in Coq. *)
  introv N Hh.
  forwards~ (l&Dl&Nl): (fmap_conseq_fresh null h (abs n) val_unit).
  sets h1': (fmap_conseq l (abs n) val_unit).
  exists (h1' \u h) (val_loc l). splits~.
  { applys (red_alloc (abs n)); eauto.
    rewrite~ abs_nonneg. }
  { exists h1' h. split. 
    { exists l. applys~ himpl_hprop_r. applys~ Alloc_fmap_conseq. }
    { splits~. hhsimpl~. } } 
Qed.

End RulesStateOps.


(* ---------------------------------------------------------------------- *)
(** Other primitive functions *)

Lemma rule_eq : forall v1 v2, 
  triple (val_eq v1 v2)
    \[] 
    (fun r => \[r = isTrue (v1 = v2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_eq. }
  { hhsimpl~. } 
Qed.

Lemma rule_add : forall n1 n2, 
  triple (val_add n1 n2)
    \[] 
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_add. }
  { hhsimpl*. } 
Qed.

Lemma rule_sub : forall n1 n2, 
  triple (val_sub n1 n2)
    \[] 
    (fun r => \[r = val_int (n1 - n2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_sub. }
  { hhsimpl*. } 
Qed.

Lemma rule_ptr_add : forall l n,
  l + n >= 0 ->
  triple (val_ptr_add l n)
    \[] 
    (fun r => \[r = val_loc (abs (l + n))]).
Proof using.
  introv N Hh. exists___. splits.
  { applys* red_ptr_add (abs (l + n)). rewrite~ abs_nonneg. }
  { hhsimpl*. } 
Qed.

Lemma rule_ptr_add_nat : forall l (f:nat), 
  triple (val_ptr_add l f)
    \[] 
    (fun r => \[r = val_loc (l+f)%nat]).
Proof using.
  intros. xapplys~ rule_ptr_add. { math. }
  { intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

(** Alternative direct proof for [rule_ptr_add_nat] *) 

Lemma rule_ptr_add_nat' : forall l (f:nat), 
  triple (val_ptr_add l f)
    \[] 
    (fun r => \[r = val_loc (l+f)%nat]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_ptr_add_nat. }
  { hhsimpl*. }
Qed.


(* ********************************************************************** *)
(* ################################################################# *)
(* * Bonus *)

(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Alternative, low-level definition of triples *)

Definition triple' t H Q :=
  forall h1 h2, 
  \# h1 h2 -> 
  H h1 -> 
  exists h1' h3' v, 
       \# h1' h2 h3'
    /\ red (h1 \u h2) t (h1' \u h3' \u h2) v
    /\ (Q v) h1'.

Lemma triple_eq_triple' : triple = triple'.
Proof using.
  hint htop_intro.
  applys pred_ext_3. intros t H Q.
  unfold triple, triple'. iff M.
  { introv D P1.
    forwards~ (h'&v&R1&R2): M (=h2) (h1 \u h2).
    { exists~ h1 h2. } 
    rewrite <- hstar_assoc in R2.
    destruct R2 as (h1''&h2'&N0&N1&N2&N3). subst h2'.
    destruct N0 as (h1'&h3'&T0&T1&T2&T3). 
    exists h1' h3' v. splits~. { fmap_red. } }
  { introv (h1&h2&N1&N2&D&U).
    forwards~ (h1'&h3'&v&R1&R2&R3): M h1 h2.
    exists (h1' \u h3' \u h2) v. splits~.
    { fmap_red. } 
    { exists~ h1' (h3' \u h2). splits~.
      exists h3' h2. splits~. } }
Qed.


(* ---------------------------------------------------------------------- *)
(* ================================================================= *)
(* ** Practical additional rules *)

(** Combination of [rule_val] and [rule_htop_post] *)

Lemma rule_val_htop : forall v H Q,
  H ==> Q v \* \Top ->
  triple (trm_val v) H Q.
Proof using.
  introv M. applys rule_htop_post. applys~ rule_val.
Qed.

(** Combination of [rule_frame] and [rule_consequence] *)

Lemma rule_frame_consequence : forall H2 H1 Q1 t H Q,
  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv WH M WQ. applys rule_consequence WH WQ. applys rule_frame M.
Qed.

(** Combination of [rule_let] and [rule_val] *)

Lemma rule_let_val : forall x v1 t2 H Q,
  (forall (X:val), X = v1 -> triple (subst x X t2) H Q) ->
  triple (trm_let x (trm_val v1) t2) H Q.
Proof using. 
  introv M. forwards~ M': (rm M).
  applys_eq~ (>> rule_let H (fun x => \[x = v1] \* H)) 2.
  { applys rule_val. hsimpl~. }
  { intros X. applys rule_extract_hprop. intro_subst. applys M'. }
Qed.

(** A rule of conditionals with case analysis already done *)

Lemma rule_if' : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  triple t1 (Q1 true) Q ->
  triple t2 (Q1 false) Q ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3 M4. applys* rule_if.
  { intros b. case_if*. }
Qed.

(** A direct proof for [rule_if_bool] *)

Lemma rule_if_bool' : forall v t1 t2 H Q,
  (v = true -> triple t1 H Q) ->
  (v = false -> triple t2 H Q) ->
  (is_val_bool v) ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M1 M2 (b&E). intros HF h N. subst v.
  destruct b.
  { forwards* (h'&v'&R&K): (rm M1) h.
    exists h' v'. splits~. 
    { applys* red_if_bool. } }
  { forwards* (h'&v'&R&K): (rm M2) h.
    exists h' v'. splits~. 
    { applys* red_if_bool. } }
Qed.

(** An alternative statement for [rule_seq] *)

Lemma rule_seq' : forall t1 t2 H Q H1,
  triple t1 H (fun r => \[r = val_unit] \* H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_seq.
  { applys M1. }
  { applys rule_extract_hprop. intros. applys M2. }
  { intros v E. hpull; false. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Reformulation of the rule for N-ary functions *)

Definition spec_funs (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:vals), length xs = length Xs ->
    triple (substs xs Xs t1) ===> triple (trm_apps F Xs).

Lemma spec_funs_val_funs : forall xs t1,
  var_distinct xs ->
  xs <> nil ->
  spec_funs xs t1 (val_funs xs t1).
Proof using. introv D N L M. applys* rule_apps_funs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Reformulation of the rule for N-ary recursive functions *)

Definition spec_fixs (f:var) (xs:vars) (t1:trm) (F:val) :=
  forall (Xs:vals), length xs = length Xs ->
    triple (subst f F (substs xs Xs t1)) ===> triple (trm_apps F Xs).

Lemma spec_fixs_val_fixs : forall f xs t1,
  var_distinct (f::xs) ->
  xs <> nil ->
  spec_fixs f xs t1 (val_fixs f xs t1).
Proof using. introv D N L M. applys* rule_apps_fixs. splits~. Qed.


(* ---------------------------------------------------------------------- *)
(** Functions of one argument *)

Lemma rule_app_fun : forall x F V t1 H Q,
  F = (val_fun x t1) ->
  triple (subst x V t1) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros HF h N.
  lets~ (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { applys~ red_app_fun. }
Qed.

Definition spec_fun (x:var) (t1:trm) (F:val) :=
  forall X, triple (subst x X t1) ===> triple (trm_app F X).

Lemma spec_fun_val_fun : forall x t1,
  spec_fun x t1 (val_fun x t1).
Proof using. introv. intros X H Q M. applys* rule_app_fun. Qed.

Lemma rule_fun_spec : forall x t1 H Q,
  (forall (F:val), spec_fun x t1 F -> H ==> Q F) ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fun x t1).
  { applys spec_fun_val_fun. }
  { applys~ rule_fun. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Recursive functions of one argument *)

Lemma rule_app_fix : forall f x F V t1 H Q,
  F = (val_fix f x t1) ->
  triple (subst f F (subst x V t1)) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros HF h N.
  lets~ (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { applys~ red_app_fix. }
Qed.

Definition spec_fix (f:var) (x:var) (t1:trm) (F:val) :=
  forall X, triple (subst f F (subst x X t1)) ===> triple (trm_app F X).

Lemma spec_fix_val_fix : forall f x t1,
  spec_fix f x t1 (val_fix f x t1).
Proof using. introv. intros X H Q M. applys* rule_app_fix. Qed.

Lemma rule_fix_spec : forall f x t1 H Q,
  (forall (F:val), spec_fix f x t1 F -> H ==> Q F) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. forwards M': (rm M) (val_fix f x t1).
  { applys spec_fix_val_fix. }
  { applys~ rule_fix. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Functions of two arguments *)

Notation "'val_fun2' x1 x2 t" := (val_fun x1 (trm_fun x2 t))
  (at level 69, x1 ident, x2 ident, only parsing).

Lemma red_app_fun2 : forall m1 m2 vf v1 v2 x1 x2 t r,
  vf = val_fun2 x1 x2 t ->
  red m1 (subst x2 v2 (subst x1 v1 t)) m2 r ->
  x1 <> x2 ->
  red m1 (vf v1 v2) m2 r.
Proof using. 
  hint red_val.
  introv E M N. subst. applys~ red_app_arg.
  { applys~ red_app_fun. simpl. case_if. applys red_fun. }
  { applys~ red_app_fun. }
Qed.

Definition spec_fun2 (x1 x2:var) (t1:trm) (F:val) :=
  forall X1 X2, triple (subst x2 X2 (subst x1 X1 t1)) ===> triple (F X1 X2).

Lemma rule_app_fun2 : forall x1 x2 F V1 V2 t1 H Q,
  F = val_fun2 x1 x2 t1 ->
  x1 <> x2 ->
  triple (subst x2 V2 (subst x1 V1 t1)) H Q ->
  triple (F V1 V2) H Q.
Proof using. 
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { applys* red_app_fun2. }
Qed.

Lemma spec_fun2_val_fun2 : forall x1 x2 t1,
  x1 <> x2 ->
  spec_fun2 x1 x2 t1 (val_fun2 x1 x2 t1).
Proof using. introv. intros X1 X2 H Q M. applys* rule_app_fun2. Qed.


(* ---------------------------------------------------------------------- *)
(** Combination of [rule_let] and [rule_fun] or [rule_fix] *)

(* not used, to update

Lemma rule_let_fun : forall f x t1 t2 H Q,
  (forall (F:val), spec_fun x t1 F -> triple (subst f F t2) H Q) ->
  triple (trm_let f (trm_fun x t1) t2) H Q.
Proof using.
  introv M. applys rule_let (fun F => \[spec_fun x t1 F] \* H).
  { applys rule_fun. introv HF. hsimpl~. }
  { intros F. applys rule_extract_hprop. applys M. }
Qed.

Lemma rule_let_fix : forall f x t1 t2 H Q,
  (forall (F:val), spec_fix f x t1 F -> triple (subst f F t2) H Q) ->
  triple (trm_let f (trm_fix f x t1) t2) H Q.
Proof using.
  introv M. applys rule_let (fun F => \[spec_fix f x t1 F] \* H).
  { applys rule_fix. introv HF. hsimpl~. }
  { intros F. applys rule_extract_hprop. applys M. }
Qed.

Lemma rule_let_fun2 : forall f x1 x2 t1 t2 H Q,
  (forall (F:val), spec_fun2 x1 x2 t1 F -> triple (subst f F t2) H Q) ->
  x1 <> x2 ->
  triple (trm_let f (trm_fun x1 (trm_fun x2 t1)) t2) H Q.
Proof using.
  introv M N. applys rule_let (fun F => \[spec_fun2 x1 x2 t1 F] \* H).
  { applys rule_func_val. hsimpl. applys~ spec_fun2_val_fun2. }
  { intros F. applys rule_extract_hprop. applys M. }
Qed.

*)

(* ---------------------------------------------------------------------- *)
(** Weakest precondition *)


Module WP.

Definition wp (t:trm) (Q:val->hprop) : hprop := 
  Hexists H, H \* \[triple t H Q].

Lemma wp_equiv : forall t H Q,
  triple t H Q <-> (H ==> wp t Q).
Proof using.
  intros. unfold wp. iff M.
  { hsimpl. rew_heap~. }
  { applys~ rule_consequence (rm M). xpull~. }
Qed.

End WP.

