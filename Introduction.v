(** * Introduction *)

(* ################################################################# *)
(** * Separation Logic in the real world *)


(* ================================================================= *)
(** ** Origins of Separation Logic *)

(** Separation Logic (SL) was introduced by three seminal papers:

    - "Intuitionistic Reasoning about Shared Mutable Data Structure"
      by John Reynolds (2000), a paper that builds on and extend
      earlier ideas from Burstall (1972).
    
    - "Local reasoning about programs that alter data structures"
      by John Reynolds, Peter O'Hearn, and Hongseok Yang (2001).  
   
    - "Separation Logic: A logic for shared mutable data structure" 
      by John Reynolds (2002). 

*) 


(* ================================================================= *)
(** ** Success story *)

(** Separation Logic was quite rapidly adopted by a number  
    of researchers as a basis for conducting practical program 
    verification, both on low-level and high-level code.
    The (non-exhaustive) list below mentions a number of projects
    that have scaled to the verification of thousands of lines of code.
    This list highlights in particular the diversity of the languages targeted.

    - Klein et al at NICTA verified micro-controller code using Isabelle.
    - Shao et al at Yale verified operating system code using Coq.
    - Chlipala et al at MIT verified assembly code using Coq.
    - Appel et al at Princeton verified C-light programs using Coq.
    - Jacobs et al at KU Leuven verified C and Java programs using the tool Verifast.
    - Morrisett et al at Harvard verified monadic ML code using Coq.
    - Charguéraud at Inria verified OCaml code using Coq.
    - etc...

*)


(* ################################################################# *)
(** * Scope of this course *)

(* ================================================================= *)
(** ** Practice and theory *)

(** This course gives an introduction to the key ideas of Separation Logic,
    and also presents a practical approach to conducting interactive program 
    verification using Separation Logic.

    Regarding the fundamentals of Separation Logic, this course relies
    on many examples to demonstrate the profound implications of 
    following the Separation Logic discipline when reasoning about:
    - allocation and deallocation, 
    - traversal of tree-shaped data structures using either recursive 
      functions or while loops, 
    - local state captured by closures,
    - iteration using iterators, either first-order or higher-order.
    

    Regarding practical program verification, this course leverages two key
    tools that significantly decrease program verification overheads:
    - _Characteristic formulae_ provide a technique to avoid the manipulation 
      of program variables and substitutions during verification proofs.
      The construction of the characteristic formula amounts to applying
      all at once all the reasoning rules from the logic following the
      structure of the code, replacing in particular all program variables with 
      Coq variables.
    - _Lifted specifications_ enables, instead of specifying heap values and
      result values as values from (deep embedding of) the programming language,
      to state specification directly in terms of the corresponding Coq values.
      Concretely, instead of specifying that a return value is the programming
      language boolean value [val_bool true], one may simply write that the
      return value is the Coq boolean [true]. The mechanism of lifted 
      specifications can be seen as a generalization of the coercion mechanism
      available in Coq.


    The course includes numerous examples demonstrating that the two 
    aforementioned techniques make it practical to verify realistic 
    algorithms and data structures entirely within Coq, through 
    reasonably short proof scripts.
*)


(* ================================================================= *)
(** ** Beyond the scope of this course *)

(** This course focuses on the reasoning about sequential programs.
    It does not cover Concurrent Separation Logic, which is
    a hot topic of research. Reasoning about concurrent programs
    involving locks and critical section is very challenging, and
    even more so for programs involving concurrent accesses in 
    a weak memory model.

    This course focuses mainly on practical use of Separation Logic.
    It does include the formalization of a syntactic proof of soundness.
    However, it does not present mathematical models involving theoretical 
    objects such as "BI-algebras" or "ultrametric spaces". *)
 

(* ################################################################# *)
(** * Key insights of Separation Logic *)

(* ================================================================= *)
(** ** The quest for modularity *)

(** In Hoare Logic, the precondition and postcondition of a term
    are expressed using assertions, which are predicate over the 
    _entire_ state. Yet, in a large program, one would ideally like to 
    verify the various program components in isolation, and be
    able to ignore, during the verification of one given component,
    the existence of the pieces of state associated with all the other
    components. Component-by-component verification, better known as
    _modular verification_, is the primary motivation for Separation
    Logic.

    Separation Logic is set up in such a way that the precondition and 
    postcondition of a term may describe only the piece of the state 
    that is actually involved in the execution of that term.
    - Pieces of state that are not mentioned in the precondition
      cannot be accessed or modified by the term.
    - Pieces of state that are described in the postcondition
      but not in the precondition necessarily correspond to memory
      cells that have been allocated by the term.
    - Conversely, pieces of state that are mentioned in the 
      precondition but do not appear in the postcondition correspond
      to memory cells that have been deallocated, or, in the case of 
      language equipped with a garbage collector, cells that have been
      discarded during the proof.      


    The strength of Separation Logic is that a verified term (program 
    component) is guaranteed to behave according to its specification
    when executed in any context. In other words, as soon as the precondition 
    is satisfied by a particular subset of the input state, the term
    will execute correctly, modifying and possibly extending this
    piece of input state, but not accessing or modifying any of the 
    rest of the input state. *)


(* ================================================================= *)
(** ** Separation Logic assertions *)

(** In Separation Logic, assertions are constructed using two 
    fundamental building blocks: the _points-to_ assertion
    and the _separating conjunction_. 
    
    The points-to assertion, written [r ~~> v], describes a piece of 
    state made of a single memory cell, at location [r], with contents [v]. 
    For example, a term that increments a reference [r] with initial
    contents [2] is specified using the following Separation Logic 
    triple.


   {r ~~> 2} (incr r) {r ~~> 3}
]]    
    
    More generally, the term [incr r] increments the contents of the
    cell [r] by one unit, thus taking its contents from [n] to [n+1]
    for any integer [n]. Formally:


    forall n, {r ~~> n} (incr r) {r ~~> (n+1)}
]]    
    
    The second fundamental building block is the separation conjunction, 
    written [H \* H']. This assertion describes the disjoint union of two 
    pieces of states, one described by [H] and the other described by [H']. 
    For example, the assertion:
 

    (r ~~> 2) \* (s ~~> 3)


    describes a state made of two distinct memory cells, one at location
    [r] with contents [2], and one at location [s] with contents [3]. 
  
*)

(* ================================================================= *)
(** ** The frame rule *)

(** In Separation Logic, one can prove that the execution of the term 
    [incr r] does not alter the contents any other memory cell than [r].
    For example, if [s] is another cell with contents [m], then [s] still
    has contents [m] after the evaluation of [incr r], as captured
    by the following Separation Logic triple.


    {r ~~> n \* s ~~> m} (incr r) {r ~~> (n+1) \* s ~~> m}
]]  

    The principle of non-interference with other cells illustrated above 
    is general. Separation Logic includes an extremely powerful reasoning 
    rule called the _frame rule_, which states that, given any specification, 
    this specification remains valid when augmenting both the precondition 
    and the postcondition with a same assertion [H]. For example, given
    a correct triple:


    {r ~~> n} (incr r) {r ~~> (n+1)}
]]    

    we may deduce that, for any assertion [H], the following triple is 
    also correct:


    {(r ~~> n) \* H} (incr r) {(r ~~> (n+1)) \* H}
]]    

The formal statement of the frame rule is as shown below, where both
the precondition [H1] and the postcondition [H1'] get extended with [H2].


              {H1} t {H1'}
      ---------------------------- (frame)
        {H1 \* H2} t {H1' \* H2}



*)

(* ################################################################# *)
(** * From Hoare Logic to Separation Logic *)

(* ================================================================= *)
(** ** Definition of Separation Logic triples *)

(** Separation Logic may be seen as adding a layer 
    of sophistication on top of Hoare Logic. A Separation Logic 
    triple is equivalent to a Hoare triple that systematically
    quantifies over "the rest of the world". In the formal definition, 
    shown below, the "rest of the world" is described by the assertion [H'].


  Definition {H} t {Q} :=  
     forall H',  {{H \* H'}} t {{Q \* H'}}.


    Presented like this, Separation Logic may be seen as a trivial 
    enhancement of Hoare Logic. What makes the strength of 
    Separation Logic is to follow a specific discipline, whereby:
    - Specifications of nontrivial pieces of state are systematically
      constructed using the separating conjunction operator,
      a.k.a. _the star_.
    - The precondition of a triple generally describes only the memory 
      cells that are actually involved in the execution of the term 
      being specified. Specifications that avoid describing unneeded 
      memory cells are called _small-footprint specifications_.


    Unsurprisingly, many reasoning rules from Separation Logic look
    alike their counterpart from Hoare Logic. Only the frame rule
    introduces a significant novelty. As we will see through the course,
    the implications of the frame rule are profound, and of major
    practical interest. *)

(* ================================================================= *)
(** ** Establishing the soundness of the frame rule *)

(** Given the important of the frame rule in Separation Logic, 
    it is very useful to understand how the above definition of 
    Separating Logic triples, which quantifies over "the rest of the world",
    inherently integrates support for the frame rule. Establishing 
    the connection between the definition of triples and the frame
    rule is the matter of what comes next.
   
    Consider the following axiomatization of assertions and of the
    star operator over assertions. *)

Parameter assertion : Type.

Parameter star : assertion -> assertion -> assertion.

Notation "H1 '\*' H2" := (star H1 H2)
  (at level 41, right associativity).

(** Assume moreover the star operator to be commutative and associative. *)

Parameter star_comm : forall H1 H2,
  H1 \* H2 = H2 \* H1.

Parameter star_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).  

(** Finally, assume the semantics of terms and the notion of Hoare triple 
    to be already defined, and consider the definition of Separation Logic
    triple suggested earlier. *)

Parameter trm : Type.

Parameter Hoare_triple : assertion -> trm -> assertion -> Prop.

Definition SL_triple (H:assertion) (t:trm) (Q:assertion) :=
  forall (H':assertion), Hoare_triple (H \* H') t (Q \* H').

(** In that setting, establish a proof that the frame rule 
    holds in Separation Logic, by completing the following exercise. *)

(** **** Exercise: 2 stars, recommended (frame_rule)  *)

Lemma frame_rule : forall (H1 H2 Q : assertion) (t:trm),
  SL_triple H1 t Q ->
  SL_triple (H1 \* H2) t (Q \* H2).
Proof.
  unfold SL_triple.
  intros.
  specialize H with (H' := (H2 \* H') ).
  repeat rewrite star_assoc.
  trivial.
Qed.

(** [] *)

(* ################################################################# *)
(** * Organization of the course *)

(** TODO This paragraph will be written after all chapters are ready. *)

(* ################################################################# *)
(** * Bibliography notes *)

(** The _programming language_ considered in this course is a lambda-calculus
    with mutable state. Unlike command-based languages used in traditional
    presentations of Hoare Logic and Separation Logic, the terms of the language 
    used in this course systematically produce an output value. As a result,
    we will need to adapt triples to allow post-conditions to describe not just 
    output heaps, but also output values.

    The _mutable state_ associated with the programming language consists
    of a flat heap that binds locations (represented as natural numbers) 
    to values (not necessarily restricted to single-word values). Records
    and arrays are described as ranges of consecutive memory cells. 
    In that respect, we follow the same approach as the seminal papers 
    on Separation Logic, as this approach leads to simpler definitions 
    than with more structured heaps.

    With respect to _termination_, the Separation Logic presented in this course 
    differs from most formalizations and courses on Separation Logic in that
    it targets total correctness, and not just partial correctness.
    For a deterministic programming language, constructing a total
    correctness Separation Logic involves not much more work than 
    constructing a partial correctness one, and it brings much
    stronger guarantees: programs are proved to terminate.

    _Characteristic formulae_ were introduced in Charguéraud's PhD work 
    (ICFP'2011), but whereas in the original presentation characteristic formulae
    where generated as axioms using an external tool, the characteristic formulae 
    from this course are generated entirely within Coq, in an axiom-free fashion.
    This course includes a gentle, self-contained introduction to characteristic
    formulae.

    _Lifted specifications_ is a particular variant of a classic and popular
    methodology that consists in establishing relationships between values
    from the (deep embedding of the) programming language and values from
    the logic of the theorem prover. The presentation followed in this course 
    relies on a new (as of 2017), lightweight implementation based on type-classes.
    More precisely, Coq values whose type have instances of the "encoding" 
    type-class may be automatically interpreted as the corresponding programming 
    language value. Note that this course does not assume prior knowledge of
    type-classes.

*)
