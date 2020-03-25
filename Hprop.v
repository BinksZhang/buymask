(** * Hprop: Heap Predicates *)

(* ################################################################# *)
(** * Syntax and semantics *)

(** In order to give a formal presentation of assertions (a.k.a. 
    heap predicates) and triples, we need to introduce the syntax
    and semantics of the source language used throughout this course. *)

(* ================================================================= *)
(** ** Syntax of the source language *)

(** To begin with, we load appropriate definitions from the TLC library. *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Close Scope fmap_scope.

(** Program variables are represented using natural numbers. *)

Definition var := nat.

(** Locations are also represented as natural numbers. The [null] pointer
    corresponds to the address zero. *)

Definition loc := nat.
Definition null : loc := 0%nat.

(** The language includes a number of basic primitive functions. 
    The list of such builtin functions appears next. *)

Inductive prim : Type :=
  | val_get : prim      (* read in a memory cell *)
  | val_set : prim      (* write in a memory cell *)
  | val_ref : prim      (* allocate a single memory cell *)
  | val_alloc : prim    (* allocate a range of cells *)
  | val_eq : prim       (* comparison *)
  | val_add : prim      (* addition *)
  | val_sub : prim      (* substraction *)
  | val_mul : prim      (* multiplication *)
  | val_div : prim      (* division *)
  | val_ptr_add : prim. (* pointer addition *)

(** Values of the programming language include: 
    - the unit value (like in OCaml, similar to [void] type in C);
    - the boolean values (true and false);
    - integer values, which are assumed for simplicity to be idealized
      (unbounded) integers, without arithmetic overflow---the [int] type
      is provided by the TLC library, as an alias for the type [Z], which
      is the integer type provided by Coq's standard library;
    - locations, a.k.a. pointer values,
    - primitive functions, whose grammar was shown above,
    - functions, of the form [val_fun x t], with argument [x] and body [t],
    - and recursive functions, of the form [val_fix f x t], where [f]
      denotes the name of the function in recursive calls. 

    Due to the presence of functions, the grammars of values is mutually
    recursive with the grammar of terms. A term may be:
    - a value, i.e. one object from the above grammar of values;
    - a program variable, i.e. a token that may get replaced by a value
      during a substitution operation;
    - a function definition, of the form [trm_fun x t]; such functions
      are intended to become values of the form [val_fun x t], once 
      substitutions of the free variables of the function have been performed;
    - a recursive function definition, of the form [trm_fix f x t];
    - a conditional, of the form [trm_if t1 t2 t3], written in concrete
      syntax as [If t1 Then t2 Else t3]; 
    - a sequence, of the form [trm_seq t1 t2], also written [t1 ;; t2];
    - a let-binding, of the form [trm_let x t1 t2], also written
      [Let x := t1 in t2];
    - an application, of the form [trm_app t1 t2], which may be written
      simply as [t1 t2], thanks to the coercion mechanism introduced further;
    - a while loop, of the form [trm_while t1 t2], also written
      [While t1 Do t2 Done];
    - a for loop, of the form [trm_for x t1 t2 t3], also written
      [For x := t1 To t2 Do t3 Done]. 


    The corresponding grammar appears next.
*)

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


(* ================================================================= *)
(** ** Coercions for terms and values *)

(** _Coercions_ help writing concrete terms more succinctly. 
    For example, thanks to the coercions defined further below,
    instead of writing:

  trm_app (trm_val (val_prim val_ref)) (trm_val (val_int 3))
]] 
    it suffices to write:

  val_ref 3

    Coq is able to automatically insert the appropriate constructors where
    required for the term to type-check correctly. 

    The list of coercions in use appears next.
*)

Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(** Given an expression, we may ask Coq to display the coercions that it
    has automatically inferred. For example, consider the definition 
    shown below. Activate the [Set Printing Coercions] option, and observe
    the result of making the query [Print coercion_example]. *)

Example coercion_example : trm := 
  val_ref 3.
Set Printing Coercions.
Print coercion_example.


(* ================================================================= *)
(** ** Representation of the heap *)

(** The mutable state of a program is represented as a finite map from location 
    to values. *)

Definition state := fmap loc val.

(** The details of the implementation of finite maps (type [fmap]) is not
    relevant to the present course. The curious reader may find the definition
    in the file [Fmap.v]. In this chapter, we only need to know about the
    main operations for manipulating finite maps.
    
    - [fmap_empty] describes the empty finite map.
    
    - [fmap_single l v] describes a finite map with a single entry
      that binds location [l] to value [v].

    - [fmap_union h1 h2] describes the union of two finite maps;
      in case of overlap, bindings from the first argument are kept.

    - [fmap_disjoint h1 h2] asserts that two finite maps have disjoint 
      domains, i.e. that they do not overlap. 
      
*)

(* ================================================================= *)
(** ** Evaluation predicate *)

(** The evaluation rules are standard. They define an evaluation
    judgment, written [red h t h' v], which asserts that the
    evaluation of the term [t] starting in memory state [h] does
    terminate and produces the value [v] in the final state [h'].
    Note that the arguments [h] and [h'] of [red] describe the full
    memory state. *)

Parameter red : state -> trm -> state -> val -> Prop.

(** Rather than reproducing here pages of standard definitions, we will 
    present the evaluation rules as we need them. Details may be found in
    the file [LambdaSemantics.v], which contains the recursive definition of
    capture-avoiding substitution and the inductive definition of the
    evaluation rules. *)


(* ################################################################# *)
(** * From Hoare triples to Separation Logic triples *)

(** ** Hoare triples for terms with an output value **)

(** In what follows, we adapt Hoare triples to terms, which, unlike 
    commands, always produce an output value. 
       
    Recall the grammar of assertions: *)

Definition assertion := state -> Prop.

(** Recall the definition of a partial correctness Hoare triple for a 
    programming language based on commands (i.e. with statements that 
    do not return an output value) from Volume 2. It asserts that if the
    precondition is satisfied, and if the program terminates, then the 
    postcondition holds:


  Definition Hoare_triple_com_partial (H:assertion) (c:com) (Q:assertion) : Prop :=
    forall h h', H h -> ceval h c h' -> Q h'.


    In this course, we focus on total correctness, which brings stronger
    guarantees, as it enforces termination. The definition of Hoare triple
    may be easily adapted to total correctness, to assert the following:
    if the precondition is satisfied, then the program terminates, and
    the postcondition holds. In the formal definition below, observe
    that the output heap [h'] now gets quantified existentially in the
    conclusion.


  Definition Hoare_triple_com_total (H:assertion) (c:com) (Q:assertion) : Prop :=
    forall h, H h -> 
    exists h', ceval h c h' /\ Q h'.


   The definition above assumes a language of commands, in which terms do not
   produce any output value. How should the definition of Hoare triple be adapted 
   to handle terms that produce an output value? 
   
   The output value, call it [v], needs to be quantified existentially
   like the output heap. The evaluation predicate becomes [red h t h' v].
   The postcondition [Q h'] also needs to be extended, so that Hoare triple
   may be used to specify the output value of the term [t]. We achieve this
   by passing [v] as first argument to the postcondition [Q]. In other words, 
   we update the type of the postcondition from [assertion] to 
   [val -> assertion].

   In summary, the definition of Hoare triples gets adapted as follows.

*)

Definition Hoare_triple (H:assertion) (t:trm) (Q:val->assertion) : Prop :=
  forall h, H h -> 
  exists v h', red h t h' v /\ Q v h'.


(* ================================================================= *)
(** ** Definition of Separation Logic triples *)

(** We will give a definition of the separating conjunction operator (star)
    shortly afterwards. For the moment, let us assume a definition of [star]
    to exist, and let us exploit it to define the semantics of a SL triple. *)

Parameter star : assertion -> assertion -> assertion.

Notation "H1 '\*' H2" := (star H1 H2)
  (at level 41, right associativity).

(** Recall the definition of Separation Logic triples from the introduction. 


  Definition SL_triple (H:assertion) (t:trm) (Q:assertion) :=
    forall (H':assertion), Hoare_triple (H \* H') t (Q \* H').


    To adapt it to a language where terms output values, we need to
    define what it means to compute the star of a postcondition [Q] of
    type [val->assertion] and of an assertion [H].

    To that end, we let [Q \*+ H'] denote [fun x => (Q x \* H')].
    This postcondition characterizes the same output value as [Q],
    but in an output heap extended with [H'].
*)

Notation "Q \*+ H" := (fun x => (Q x) \* H)
  (at level 40).

(** Using this piece of notation, the definition of triples from the
    introduction is easily adapted. *)

Definition triple_1 (H:assertion) (t:trm) (Q:val->assertion) :=
  forall (H':assertion), Hoare_triple (H \* H') t (Q \*+ H').

(** The definition above defines SL triples in terms of Hoare triples.
    While this indirect definition is helpful for providing intuition,  
    a direct definition is better suited for conducting proofs.
    If we unfold the intermediate definition of Hoare triples and
    perform minor simplification, we obtain the definition shown below. *)

Definition triple_2 (H:assertion) (t:trm) (Q:val->assertion) : Prop :=
  forall H' h, (H \* H') h -> 
  exists v h', red h t h' v /\ (Q v \* H') h'.

(** This definition reads as follows: for any input heap [h], and any 
    heap predicate [H'] describing the part of the heap not covered
    by the precondition [H], there exists an output value [v] and an
    output heap [h'] to which the term [t] evaluates starting from the
    input heap [h], and such that a subset of the final heap is described 
    by the postcondition [Q] applied to the value [v], while the remaining
    subset of the output heap corresponds is described by [H']. *)

(* ================================================================= *)
(** ** Slight change in terminology *)

(** In Separation Logic, we usually manipulate only pieces of states,
    as opposed to complete state. It is convenient to keep track of
    the intention by using two distinct types:
    - [state] denotes a complete state,
    - [heap] denotes a piece of state. 


    In our formalism, both [state] and [heap] are represented as 
    finite maps from locations to values, so the distinction might
    appear a bit artificial. Nevertheless, this distinction proves
    very useful when extending Separation Logic with additional features,
    such as "time credits" or "read-only permissions". 
    Thus, we introduce the following alias. *)

Definition heap : Type := state. (* intended to represent a piece of state *)

(** In practice, we use type [state] when defining the evaluation rules,
    and we use the type [heap] to denote the argument of an assertion.
    In the rare cases where an entity is used at the same time in an 
    evaluation rule and as argument of an assertion, we use type [heap]. *)

(** A Separation Logic assertion is a predicate over a piece of state. 
    Thus, it has type [heap -> Prop]. The type of such _heap predicates_
    is written [hprop]. *)

Definition hprop := heap -> Prop.

(** With the new terminology, and with placing the term [t] as first
    argument, the definition of SL triples becomes: *)

Definition triple_3 (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall H' h, (H \* H') h -> 
  exists v h', red h t h' v /\ (Q v \* H') h'.

Notation "'triple'" := triple_3.

(** By convention, we let [H] range over heap predicates (of type [hprop]),
    and [Q] range over postconditions (of type [val->hprop]). *)


(* ################################################################# *)
(** * Fundamental heap predicates *)

(** We next present the definitions of the fundamental building blocks for 
    constructing heap predicates. These building blocks are:

    - [\[]] denotes the empty heap predicate.
    - [\[P]] denotes the empty heap predicate and asserts that [P] is true.
    - [l ~~> v] describes a single memory cell, at location [l], with
      contents [v].
    - [H1 \* H2] denotes the separating conjunction of two heap predicates.
    - [Hexists x, H] denotes an existential quantification at the level of 
      heap predicates.

    As we will see through this section, each of these heap predicates is 
    defined as a function of the form [fun (h:heap) -> (...:Prop)].

    What makes Separation Logic works so smoothly in practice is that 
    the aforementioned fundamental heap predicates are the only ones that are 
    defined directly as functions from heap to propositions. All user-defined 
    heap predicates are then defined as combination of these fundamental 
    heap predicates. It is thus essential to have a deep understanding of
    the meaning of the fundamental heap predicates. *)

(* ================================================================= *)
(** ** Points-to predicate *)

(** The points-to heap predicate is written [l ~~> v], which is a notation for  
    [hsingle l v]. This heap predicate characterizes a heap [h] that is made
    of a single memory cell, at location [l], with contents [v]. In addition, 
    [hsingle l v] captures the property that [l] is not the [null] location. 
    The formal definition is as follows: *)

Definition hsingle (l:loc) (v:val) : hprop := 
  fun h => h = fmap_single l v /\ l <> null.

Notation "l '~~>' v" := (hsingle l v)
  (at level 32, no associativity).

(** For example, the following specification of [incr r] indicates
    that it executes safely assuming that location [r] is allocated
    with contents [2], and that it updates this location to contain [3].
    The evaluation of [incr r] returns some value [v], which as we will
    see soon afterwards, may be specified to be the unit value. *)

Parameter (incr:val) (r:loc).

Parameter hsingle_demo :
  triple (incr r)
    (r ~~> 2) (* precondition *)
    (fun v => r ~~> 3). (* postcondition *)

(** The general specification of the [incr] function involves a universal
    quantification over the initial contents of the cell, as shown below. *)

Parameter rule_incr : forall (n:int),
  triple (incr r)
    (r ~~> n) 
    (fun v => r ~~> (n+1)). 

(** **** Exercise: 1 star, recommended (rule_augment)  *)
(** State a specification for the term [val_augment r m], which takes 
    as arguments a location [r] and an integer [m], and updates the cell 
    at location [r] by adding [m] to its original contents. *)

Parameter val_augment : val.

Parameter rule_augment : forall (m n o:int) (r:loc),
  triple (val_augment r m)
    (r ~~> n) 
    (fun v => r ~~> (m+n)).



(* ================================================================= *)
(** ** Star predicate *)

(** The star predicate is written [H1 \* H2], which is a notation for
    [hstar H1 H2]. This heap predicate characterizes a heap [h] that 
    is composed of two disjoint parts, call them [h1] and [h2], such that
    the first one satisfies [H1] and the second one satisfies [H2].
    Together, the propositions [state_disjoint h1 h2] and [h = state_union h1 h2]
    assert that [h1] and [h2] really constitute a partition of [h] in two
    disjoint parts. *)

Definition hstar (H1 H2:hprop) : hprop := 
  fun h => exists (h1 h2:heap),
       H1 h1 
    /\ H2 h2 
    /\ fmap_disjoint h1 h2
    /\ h = fmap_union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity).

(** Consider for example the following specification of [incr r] which captures
    the fact that it does not modify the contents of another reference [s]. *)

Parameter hstar_demo : forall (s:loc) (n m:int),
  triple (incr r)
    (r ~~> n \* s ~~> m) 
    (fun v => r ~~> (n+1) \* s ~~> m). 

(** **** Exercise: 2 stars, recommended (rule_swap)  *)
(** State a specification for the term [val_swap r s], which takes as argument
    two distinct locations [r] and [s], with respective contents two integers [n] 
    and [m], and that swaps the contents of the two locations. *)

Parameter val_swap : val.

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 1 star, recommended (hstar_comm)  *)
(** Prove that separating conjunction is commutative, in the sense that any
    heap satisfying [H1 \* H2] also satisfies [H2 \* H1]. The proof involves
    the two following results on finite maps: symmetry of the disjointness 
    predicate, and commutativity of the union of disjoint heaps. *)

Parameter fmap_disjoint_sym : forall (h1 h2:heap),
  fmap_disjoint h1 h2 -> 
  fmap_disjoint h2 h1.

Parameter fmap_union_comm_of_disjoint : forall (h1 h2:heap),
  fmap_disjoint h1 h2 ->
  fmap_union h1 h2 = fmap_union h2 h1.

Lemma hstar_comm : forall (H1 H2:hprop) (h:heap),
  ((H1 \* H2) h) -> 
  ((H2 \* H1) h).
Proof.
  unfold hstar.
  intros.
  destruct H as [h1 [h2 [HA [HB [HC HD]]]]].
  exists h2 h1.
  split; repeat split; auto.
  rewrite HD.
  apply fmap_union_comm_of_disjoint.
  auto.
Qed.

(** An essential property of Separation Logic is that it is never possible
    to construct a heap satisfying a heap predicate of the form
    [(r ~~> ..) \* (r ~~> ..)]. Indeed, there is no way to exhibit two
    disjoint heaps that both have [r] in their domain. *)

Lemma hstar_hsingle_same_loc_inv : forall (l:loc) (v1 v2:val) (h:heap),
  ((l ~~> v1) \* (l ~~> v2)) h ->
  False.
Proof.
  introv (h1&h2&P1&P2&D&E). destruct P1 as (E1&N1). destruct P2 as (E2&N2). 
  subst. applys* fmap_disjoint_single_single_same_inv.
Qed.

(** Now that the separating conjunction is properly defined,
    we update the definition of [triple] to use that definition,
    instead of the abstract [star] operator that assumed previously. *)

Definition triple_4 (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall H' h, (H \* H') h -> 
  exists v h', red h t h' v /\ (Q v \* H') h'.

(** Thereafter, [triple] is a shorthand for [triple_4]. *)

Notation "'triple'" := triple_4.

(* QUIZ *)
(** Is the following triple true or false? *)
Parameter rule_cell_twice : forall (r:loc) (n:int),
  triple (val_unit) 
    (r ~~> n \* r ~~> n) 
    (fun v => r ~~> (n+1) \* r ~~> (n+1)).
(* /QUIZ *)

(** **** Exercise: 2 stars, recommended (rule_cell_twice)  *)
(** Prove the above lemma.
    Hint: unfold the definition of [triple], a.k.a. [triple_4],
    and decompose the assumption on the input heap in order to
    derive a contradiction using lemma [hstar_hsingle_same_loc_inv]. *)

Lemma rule_cell_twice' : forall (r:loc) (n:int),
  triple (val_unit) 
    (r ~~> n \* r ~~> n) 
    (fun v => r ~~> (n+1) \* r ~~> (n+1)).
Proof.
  unfold triple_4.
  intros.
  destruct H as [h1 [h2 [H1 [H2 [H3 H4]]]]].
  apply hstar_hsingle_same_loc_inv in H1.
  destruct H1.
Qed.


(** [] *)


(* ================================================================= *)
(** ** Pure heap predicate *)

(** The _empty heap predicate_ is written [ \[] ], which is a notation for
    [hempty]. It characterizes exactly heaps that are empty. *)

Definition hempty : hprop := 
  fun h => h = fmap_empty.

Notation "\[]" := (hempty) 
  (at level 0).

(** The _pure heap predicate_ extends the empty heap predicate by capturing
    not just the fact that its argument is the heap is empty, but also that
    some proposition [P] is true. The pure heap predicate is written [ \[P] ], 
    which is a notation for [hpure P]. It is defined as follows: *)

Definition hpure (P:Prop) : hprop := 
  fun h => (h = fmap_empty /\ P).

Notation "\[ P ]" := (hpure P) 
  (at level 0, P at level 99, format "\[ P ]").

(** The empty heap predicate and the pure heap predicate are systematically
    involved in the precondition and the postcondition of pure functions, i.e.
    functions that do not involve side effects. Consider for example the 
    specification of the successor function. The precondition assumes
    an empty input heap. The postcondition asserts an empty input heap, and
    moreover asserts that the output value is one unit greater than the
    input argument. *)

Parameter rule_succ : forall (n:int), 
  triple (val_add (val_int n))
    \[] 
    (fun (r:val) => \[r = val_int (n + 1)]).
 
(** Observe by executing [Print rule_succ] that the [val_int] constructor 
    is in fact not displayed by Coq. Indeed, it is declared as a coercion.
    In fact, we do not need to write [val_int] in the triple, as Coq is
    able to infer its occurences. Thus, we may write more concisely: *)

Parameter rule_succ' : forall (n:int), 
  triple (val_add n)
    \[] 
    (fun (r:val) => \[r = n + 1]).

(** As another example, consider the specification of the addition primitive 
    function. The precondition assumes an empty input heap. The postcondition 
    asserts an empty input heap, and moreover asserts that the output value 
    is the sum of the two arguments. *)

Parameter rule_add : forall (n1 n2:int), 
  triple (val_add n1 n2)
    \[] 
    (fun (r:val) => \[r = n1 + n2]).

(** Note that the specification tells nothing about the behavior of
    addition in the case where the two arguments are not both integer values. *)

(** Symmetrically to its use in postconditions, the pure heap predicate may 
    appear in preconditions to describe requirements on the arguments. 
    For example, division expects a nonzero integer as second argument. *)

Parameter rule_div : forall (n1 n2:int), 
  triple (val_div n1 n2)
    \[n2 <> 0] 
    (fun (r:val) => \[r = n1 / n2]).

(** While the above formulation is perfectly valid, it is more convenient in
    practice to follow an alternative, logically equivalent presentation,
    whereby the pure preconditions appear as Coq hypotheses outside the triple.
    In the case of the division, this alternative presentation amounts to 
    asserting [n2 <> 0] as hypothesis prior to the triple: *)

Parameter rule_div' : forall (n1 n2:int), 
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[] 
    (fun (r:val) => \[r = n1 / n2]).

(** Throughout the course, we will follow the convention that pure preconditions
    appear as hypotheses prior to the triple. Thus, preconditions will only
    be used to describe the shape of the heap. *)

(** The pure heap predicate is useful not just for specifying pure functions, 
    but also for specifying effectful functions, to assert properties about
    the output value or the output heap. For example, in the specification 
    of [incr r] shown below, the pure heap predicate [ \[v = val_unit] ] asserts 
    that the evaluation of [incr r] returns the unit value. This heap predicate
    comes in addition to the points-to heap predicate that describes the output
    heap. *)

Parameter hpure_demo :
  triple (incr r)
    (r ~~> 2)
    (fun v => \[v = val_unit] \* (r ~~> 3)).

(** Above, observe that the two heap predicates from the postcondition
    are separated by the star operator. This operator asserts that the output
    heap decomposes into two disjoint parts: an empty heap, which satisfies
    the predicate [ \[v = val_unit] ], and a singleton heap, which satisfies 
    the assertion [r ~~> 3]. Such use of the separating conjunction, where one
    part corresponds to the empty heap, may appear somewhat unexpected at 
    first, but it is perfectly well-defined and corresponds to a specification
    pattern that we will see over and over again. 

    As another example, consider the specification below for the primitive 
    [val_get], used to read in a memory cell. Assuming the argument [l] to
    correspond to a location at which some value [v] is stored, the read
    operation executes safely and returns an output value, call it [x],
    which is such that [x = v]. The piece of heap, described by [l ~~> v],
    is returned unchanged in the postcondition. *)

Parameter rule_get : forall (v:val) (l:loc),
  triple (val_get l) 
    (l ~~> v) 
    (fun (r:val) => \[r = v] \* (l ~~> v)).

(** Remark: above, [val_get l] is interpreted using coercions, and stands for
    [trm_app (trm_val (val_prim val_get)) (trm_val (val_loc l))]. *)

(** **** Exercise: 2 stars, recommended (rule_set)  *)
(** State a specification for the term [val_set l v], which updates the
    location [l] with the value [v]. Make sure to specify that the update
    operation returns the unit value. *)

Parameter rule_set : forall (n v:val) (l:loc),
  triple (val_set l v) 
    (l ~~> n) 
    (fun (r:val) => \[r = v] \* (l ~~> v)).

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 2 stars, recommended (rule_free)  *)
(** State a specification for the term [val_free l], which assumes a 
    location [l] to be allocated, and explicitly disposes this location.
    Note that such a free operation usually does not appear in programming
    languages featuring a GC, but is commonplace in other languages.
    The postcondition should  assert that the return value is unit, and
    not mention the location [l] anymore, effectively banning any subsequent
    access to this location. *)

Parameter val_free : val.

Parameter rule_free : forall (v:val) (l:loc),
  triple (val_free l)
    (l ~~> v) 
    (fun (v:val) => \[v = val_unit]).

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 1 star, optional (hpure_true_iff_hempty)  *)
(** Prove that a heap satisfies the heap predicate [\[True]] if and only 
    if it satisfies the empty heap predicate. *)

Lemma hpure_true_iff_hempty : forall (h:heap),
  (\[True] h) <-> (\[] h).
Proof.
  split; intros.
  - destruct H. trivial.
  - hnf in H. hnf.
    split; trivial.
Qed.

(** [] *)

(** The next lemma establishes that the heap predicate [H \* \[]] 
    is equivalent to [H]. Its proof relies on two handy tactics,
    that will be useful for proving numerous metatheory results.     
    - The tactic [fmap_eq] proves equality between finite maps,
      e.g. [fmap_union h fmap_empty = h].
    - The tactic [fmap_disjoint] proves obvious disjointness results,
      e.g. [fmap_disjoint h fmap_empty], or [fmap_disjoint h1 h2]
      when [fmap_disjoint h2 h1] appears in the context.

    The proof is as follows. *)

Lemma hstar_hempty_iff : forall (H:hprop) (h:heap),
  ((H \* \[]) h) <-> (H h).
Proof.
  intros. split.
  { intros (h1&h2&P1&P2&D&E). hnf in P2. subst. fmap_eq. auto. }
  { intros M. exists h (fmap_empty:heap). splits.
    { auto. }
    { hnf. auto. }
    { fmap_disjoint. }
    { fmap_eq. } }
Qed.

(** Observe that we need to provide an explicit type annotation in
    [(fmap_empty:heap)], because [fmap_empty] is a polymorphic 
    constructor, and the "exists" tactic is too limited to figure out
    by itself the required types from the current proof obligation. *)

(** **** Exercise: 2 stars, optional (hstar_hpure_iff)  *)
(** Establish a generalization of the above lemma, proving that the heap
    predicate [H \* \[P]] is equivalent to [H] when proposition [P] holds. *)

Lemma hstar_hpure_iff : forall (H:hprop) (P:Prop) (h:heap),
  ((H \* \[P]) h) <-> ((H h) /\ P).
Proof.
  split; intros.
  - destruct H0 as (h1&h2&H1&H2&H3&H4).
    hnf in H2.
    destruct H2. subst; auto.
    fmap_eq. split;auto.
  - destruct H0.
    exists h (fmap_empty:heap).
    splits; auto.
    + hnf. split; auto.
    + fmap_eq.
Qed.
(** [] *)


(* ================================================================= *)
(** ** Existential heap predicate *)

(** The _existential heap predicate_ provides existential quantification
    at the level of heap predicates. It is written [Hexists x, H], which
    is a notation for [hexists (fun x => H)]. It is the counterpart of the 
    normal existential quantification on propositions, which is written
    [exists x, P], a notation for [ex (fun x => P)]. 

    The Coq definition of [hexists] is polymorphic in the type of [x].
    The type of [x] is called [A] below. The argument of [hexists], called [J]
    below, is typically of the form [fun x => H]. It has type [A->hprop]. *)

Definition hexists (A:Type) (J:A->hprop) : hprop := 
  fun h => exists x, J x h.

Notation "'Hexists' x1 , H" := (hexists (fun x1 => H))
  (at level 39, x1 ident, H at level 50).

(** The notation [Hexists x1 x2 x3, H] shows useful to quantify several 
    arguments at once. *)

Notation "'Hexists' x1 x2 , H" := (Hexists x1, Hexists x2, H)
  (at level 39, x1 ident, x2 ident, H at level 50).
Notation "'Hexists' x1 x2 x3 , H" := (Hexists x1, Hexists x2, Hexists x3, H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50).
(** The notation [Hexists (x:T), H] allows us to provide an explicit
    type annotation. *)

Notation "'Hexists' ( x1 : T1 ) , H" := (hexists (fun x1:T1 => H))
  (at level 39, x1 ident, H at level 50, only parsing).

Notation "'Hexists' ( '_' : T1 ) , H" := (hexists (fun _:T1 => H))
  (at level 39, H at level 50). (* useful when quantifying over proof terms *)

(** The main role of existential quantification is to introduce abstraction.  
    For example, assume that we want to specify the increment function
    by saying that it updates the contents of its target location to 
    some greater contents, without revealing that the new contents is exactly
    one unit greater. Then, for a precondition [r ~~> n], we would consider
    the postcondition [Hexists m, (r ~~> m) \* \[m > n]]. *)

Parameter hexists_demo : forall (n:int),
  triple (incr r)
    (r ~~> n)
    (fun v => \[v = val_unit] \* Hexists (m:int), (r ~~> m) \* \[m > n]).

(** Existential quantification is also useful to specify output values
    when they have a specific shape. For example, consider the operation
    called [val_ref], which allocates and initializes one memory cell
    with some contents [v]. A call to [val_ref] executes safely in the
    empty heap. The output value of its evaluation is a value, call it [r],
    which is of the form [val_loc l] for _some_ location [l]. The output
    heap satisfies [l ~~> v] for that particular [l]. As shown below, the
    location [l] gets existentially quantified in the postcondition. *)

Parameter rule_ref : forall (v:val),
  triple (val_ref v) 
    \[] 
    (fun (r:val) => Hexists (l:loc), \[r = val_loc l] \* (l ~~> v)).

(** **** Exercise: 2 stars, recommended (rule_ref_of_ref)  *)
(** Consider the term [val_ref (val_ref 3)], which allocates a memory
    cell with contents [3], at some location [l], then allocates a
    another memory cell with contents [l], at some location [l'], and
    finally returns the location [l']. State a specification for that
    term. *)

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 1 star, optional (hexists_permut)  *)
(** Prove that [Hexists x, Hexists y, K x y] is equivalent to
    [Hexists y, Hexists x, K x y]. *)

Lemma hexists_permut : forall (A B:Type) (K:A->B->hprop) (h:heap),
  ((Hexists x, Hexists y, K x y) h) ->
  ((Hexists y, Hexists x, K x y) h).
Proof.
  intros.
  destruct H as (x&y&H).
  hnf.
  (*pay attention*)
  exists y.
  hnf. exists x.
  auto.
Qed.

(** [] *)

(** **** Exercise: 2 stars, optional (hpure_iff_hexists_prop)  *)
(** Prove that a heap satisfies the heap predicate [\[P]] for some
    proposition [P] if and only if it satisfies the heap predicate
    [Hexists (p:P), \[]]. The latter describes a empty heap and
    asserts the existence of a proof term [p] of type [P]. In Coq,
    asserting the existence of such a proof term of type [P] is 
    equivalent to asserting that [P] is a true proposition. *)

Lemma hpure_iff_hexists_proof : forall (P:Prop) (h:heap),
  (\[P] h) <-> ((Hexists (p:P), \[]) h).
Proof.
  split; intros.
  - destruct H as (HA&p).
    exists p.
    hnf. auto.
  - destruct H.
    hnf. split; auto.
Qed.

(* ================================================================= *)
(** ** Summary *)

(** The fundamental heap predicates are written: 
    - [\[]] 
    - [\[P]] 
    - [l ~~> v]
    - [H1 \* H2] 
    - [Hexists x, H]. 

    and they are defined as follows. *)

Module Type Fundamental.

Definition hempty : hprop := 
  fun h => h = fmap_empty.

Definition hpure (P:Prop) : hprop := 
  fun h => h = fmap_empty /\ P.

Definition hsingle (l:loc) (v:val) : hprop := 
  fun h => h = fmap_single l v /\ l <> null.

Definition hstar (H1 H2:hprop) : hprop := 
  fun h => exists h1 h2,
       H1 h1 
    /\ H2 h2 
    /\ fmap_disjoint h1 h2
    /\ h = fmap_union h1 h2.

Definition hexists (A:Type) (J:A->hprop) : hprop := 
  fun h => exists x, J x h.

End Fundamental.



(* ################################################################# *)
(** * Triples adapted for languages with garbage collection *)

(* ================================================================= *)
(** ** Motivating example *)

(** Consider the program [Let x := val_ref 3 in 5], abbreviated below
    as [t]. This program allocates a memory cell with contents [3], at some 
    location [x], and then returns [5]. In this program, the address 
    of the allocated memory cell is not returned, so it cannot be
    subsequently accessed. Thus, one may argue that a natural specification 
    for this program is the same as that of a program that simply returns 
    the value [5], that is: *)

Parameter t : trm. (* := [Let x := val_ref 3 in 5]. *)

Parameter htop_example_1 : 
  triple t
    \[]
    (fun (r:val) => \[r = 5]).

(** However, it turns out that the above triple cannot be derived with
    respect to the definition of triples that we have considered so far.
    The reason is simple: the memory cell that is allocated by the term
    belongs to the heap structure, thus it must be described in the 
    postcondition. As a result, with the current definition, only the 
    following triple may be established: *)

Parameter htop_example_2 : 
  triple t
    \[]
    (fun (r:val) => \[r = 5] \* Hexists l, l ~~> 3).

(** The remaining of this chapter describes a simple patch to the 
    definition of triple that would allow establishing the first
    specification, which is much more natural. In short, we introduce
    a mechanism that allows to discard any desired piece of state
    from the postcondition. *)

(* ================================================================= *)
(** ** Patching triples using the top predicate *)

(** To allow discarding any desired piece of state, we introduce a handy
    heap predicate called "top", which is a predicate that holds of any 
    heap. This predicate is written [\Top], and defined as follows. *)

Definition htop : hprop := 
  fun (h:heap) => True.

Notation "\Top" := (htop).

(** In the definition of triples, we modify the specification of the
    output heap from [(Q v \* H') h'] to [(Q v \* \Top \* H') h'].
    Adding a [\Top] component effectively allows to _not describe_
    in the postcondition pieces of state that have been allocated 
    during the execution of the term. *)

Definition triple_5 (H:hprop) (t:trm) (Q:val->hprop) : Prop :=
  forall H' h, (H \* H') h -> 
  exists v h', red h t h' v /\ (Q v \* \Top \* H') h'.

(** Throughout the remaining of this course, the definition of
    the predicate [triple] corresponds to the above definition.
    It is defined in file [LambdaSep.v]. *)

(** **** Exercise: 2 stars, recommended (htop_hstar_htop)  *)
(** Prove that [\Top \* \Top] is equivalent to [\Top], i.e., that
    [\Top] is idempotent. Tactics [fmap_disjoint] and [fmap_eq] 
    are useful to complete the proof. *)

Lemma htop_hstar_htop : forall (h:heap),
  ((\Top \* \Top) h) <-> (\Top h).
Proof.
  split; intros.
  - hnf. trivial.
  - exists h (fmap_empty:heap).
    splits; hnf; auto.
    fmap_eq.
Qed.

(** **** Exercise: 2 stars, optional (htop_iff_hexists_heap)  *)
(** Prove that a heap satisfies the heap predicate [\[Top]] if and
    only if it satisfies the predicate [Hexists (H:hprop), H]. *)

Lemma htop_iff_hexists_hprop : forall (h:heap),
  (\Top h) <-> (Hexists H, H) h.
Proof.
  split;intros.
  - exists \Top.
    trivial.
  - hnf. auto.
Qed.
  (* FILL IN HERE *) Admitted.

(** [] *)

