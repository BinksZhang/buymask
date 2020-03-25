(** * Repr: Representation Predicates *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Require Import LambdaSemantics LambdaSep Hprop.


(* ################################################################# *)
(** * Representation predicate for mutable linked lists *)

(* ================================================================= *)
(** ** Layout of linked lists in memory *)

(** Consider mutable linked lists, as traditionnaly implemented in the 
    C language. The empty lists is represented by the null pointer.
    A nonempty list consists of a two-cell structure, made of head cell
    that stores a value, and a tail pointer to the next cell.  
    In C syntax, we would define the structure as follows.

  typedef struct node {
    val hd;
    node* tl;
  } node;
*)

(** In the memory model that we consider in this course, a list cell at
    location [p] spans over two consecutive memory cells:
    - at location [p] is stored the item carried by that cell,
    - at location [p+1] is stored the tail pointer, i.e. the location of
      the next cell in the list; this pointer may be null.


    The heap predicate [Mcell v q p] describes such a cell in Separation
    Logic: the cell at location [p] stores a value [v] (at location [p]) 
    and a tail pointer [q] (at location [p+1]). Formally: 
*)

Definition MCell (v:val) (q:loc) (p:loc) : hprop :=
  (p ~~> v) \* ((p+1)%nat ~~> q).

(** For example, a linked list at location [p], storing as single element
    the value [8], is represented using the following heap predicate. *)

Definition list_one (p:loc) : hprop :=
  MCell 8 null p.

(** Observe that the above definition makes implicit use of the coercion
    [val_int] for converting the integer [8] into a value of type [val]. *)

Definition list_one_explicit (p:loc) : hprop :=
  MCell (val_int 8) null p.


(** **** Exercise: 2 stars, optional (MCell_not_null)  *)
(** Prove that if a heap satisfies [MCell v q p], then the pointer [p] 
    cannot [null].
    Hint: unfold the definition of [MCell], [hstar], and [hsingle]. *)

Lemma MCell_not_null : forall (p:loc) (v:val) (q:loc) (h:heap),
  (MCell v q p) h -> 
  p <> null.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)


(* ================================================================= *)
(** ** Representation of a list of length three *)

(** Consider for example a linked list that stores three items: 8, 5 and 6;
    in three cells, at locations [p], [p1], and [p2], respectively.
    Such a list is described in Separation Logic by the following 
    heap predicate: *)

Definition list_three_1 (p p1 p2:loc) : hprop :=
  (MCell 8 p1 p) \* (MCell 5 p2 p1) \* (MCell 6 null p2).

(** Note that the order of the three [MCell] predicates has no importance:
    the separating conjunction operator is commutative (recall [hstar_comm]). 
    It would be totally equivalent to write the components in a different
    order, e.g.: *)
    
Definition list_three_2 (p p1 p2:loc) : hprop :=
  (MCell 6 null p2)\* (MCell 5 p2 p1) \* (MCell 8 p1 p).

(** In general, when manipulating a linked list, only the location of the
    head of the list is relevant. The locations of the intermediate cells
    can be deduced by following tail pointers, starting from the head cell.

    When the locations of the intermediate cells are not relevant, they 
    should not be exposed in the specifications. These intermediate 
    locations may be effectively hidden by quantifying them existentially.
    To illustrate how, consider the following heap predicate, which 
    describes exactly the same three-cell list as before, simply not
    exposing the intermediate pointers [p1] and [p2] to the outside world. *)

Definition list_three_3 (p:loc) : hprop :=
  Hexists (p1:loc), (MCell 8 p1 p) \* 
  Hexists (p2:loc), (MCell 5 p2 p1) \*
                    (MCell 6 null p2).

(** Above, the tail pointers [p1] and [p2] are quantified existentially,
    however the last tail pointer, which is null, is not quantified as
    a varaible. For increased uniformity, and to ease the generalization
    to lists of arbitrary sizes, we reformulate the heap predicate by
    quantifying over the last tail pointer, call it [p3], and subsequently
    assert that [p3] is equal to [null]. We obtain: *)

Definition list_three_4 (p:loc) : hprop :=
  Hexists (p1:loc), (MCell 8 p1 p) \* 
  Hexists (p2:loc), (MCell 5 p2 p1) \*
  Hexists (p3:loc), (MCell 6 p3 p2) \*
  \[p3 = null].

(** The above heap predicate shows a recursive pattern that may be 
    generalized to arbitrary lists, as explained next. *)

(* ================================================================= *)
(** ** List representation *)

(** In what follows, we define a heap predicate of the form [MList L p],
    describeing a heap that contains a linked list with head cell at 
    location [p], and whose values are described by the Coq list [L].    
    This predicate is called a _representation predicate_ because it
    makes the connection between the heap representation of the list
    data structure and its logical model, namely a Coq list.

    The predicate [MList L p] is defined recursively following the structure 
    of the list [L]. It describes exactly one [MCell] for each item from [L].
    All theses cells are separated by the star operator. The locations of
    these intermediate cells are existentially quantified, and the last 
    tail pointer is asserted to be null, as illustrated previously.

    The recursive definition of [MList L p] appears below. When [L] is [nil],
    the pointer [p] must be [null]. When [L] is of the form [x::L'],
    there must exist a head cell that stores the value [x], and that is
    disjoint from the representation of the tail of the list, namely [L']. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => Hexists (p':loc), (MCell x p' p) \* (MList L' p')
  end.

(** We may ask Coq to check that the representation predicate
    [MList (8::5::6::nil) p] describes exactly the same heap
    as the previously-considered manual definition ([list_three_4]). *)

Lemma list_three_eq : forall (p:loc),
  let L := (val_int 8)::(val_int 5)::(val_int 6)::nil in
    (MList L p)
  = list_three_4 p. 
Proof.
  (* [reflexivity] would prove the goal directly. For details: *)
  intros. unfold L. unfold list_three_4. simpl.
  reflexivity. (* same, up to alpha-conversion *)
Qed.

(** The recursive definition of [MList] presented above in a cornerstone 
    of Separation Logic. Let's take a step back for a second.

    Recall that [MList L p] is a heap predicate, that is, a predicate 
    over the heap. Thus, [MList L p h], for some heap [h], is a proposition.
    This proposition establishes a relationship between:
    - [p]: the entry point of the linked list,
    - [L]: the (logical) list of items stored in the list, 
    - [h]: the piece of state that contains exactly the memory cells
           involved in the layout of the linked list in memory.


    Thus, [MList L p] _exposes_ what we need to know about the linked list:
    its entry point and its contents, while it _hides_ the implementation
    details that are usually irrelevant to the client of the linked list:
    the exact locations of the intermediate list cells. The ability to
    abstract away from these details is an essential feature of Separation
    Logic.

    Another essential feature of Separation Logic is... _separation_.
    Consider three independent linked lists. The heap predicate:


    (MList L1 p1) \* (MList L2 p2) \* (MList L3 p3)


    asserts that these three lists are completely disjoint from each other.
    In particular, they do not share any tail, and they do not involve any
    cycle (i.e., each list is null terminated). Indeed, the instances of the
    [MList] representation predicate are separated by a star, and each of
    the [MList] instances is defined as an iterated star over a number of
    memory cells. Thus, all the list cells involved in the three lists are
    necessarily disjoint from each other. *)

(** A linked list represented by a heap predicate [MList L p] is empty
    if and only if [L = nil], and, equivalently, if and only [p = null]. 
    In the case of an empty list, the predicate [MList L p] covers no
    list cells at all, that is, it characterizes the empty heap. *)

(** **** Exercise: 1 star, recommended (MList_nil)  *)
(** Prove that [MList nil null] is equivalent to [\[]]. *)

Lemma MList_nil : forall (h:heap),
  ((MList nil null) h) <-> (\[] h).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, optional (MList_nil_iff_null)  *)
(** Prove that if a heap satisfies [MList p L] then [p] is [null]
    if and only if [L] is [nil].
    Hint: use lemma [MCell_not_null]. *)

Lemma MList_nil_iff_null : forall (p:loc) (L:list val) (h:heap),
  ((MList L p) h) ->
  (p = null <-> L = nil).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)


(** A nonempty linked list is represented by a heap predicate 
    [MList L p] with [L <> nil] and [p <> null].
    
    In the particular case where the linked list contains a single item,
    that is, if [L] is of the form [v::nil], then the predicate [MList L p]
    covers exactly one list cell. *)

(** **** Exercise: 3 stars, optional (MList_one)  *)
(** Prove that [MList (v::nil) p] is equivalent to [MCell v null p].

    Hint: use tactic [rew_fmap] to simplify [fmap_union h fmap_empty] as [h]. *)

Lemma MList_one : forall (p:loc) (h:heap) (v:val),
  ((MList (v::nil) p) h) <-> ((MCell v null p) h).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)


(* ################################################################# *)
(** * Specifications using representation predicates *)

(* ================================================================= *)
(** ** Access to the head of a list cell *)

(** The function [val_get_hd] takes as input a nonempty linked list 
    and returns its head value, that is, the item stored in its head cell.
    In C syntax, it would be written:

  val get_hd(node* p) {
    return p->hd;
  }
*)

Parameter val_get_hd : val.

(** In what follows, we investigate the specification of [val_get_hd].
    Recall from the previous chapter the specification of the function
    [val_get], which reads in a memory cell. Its specification is copied
    below. *)
    
Parameter rule_get : forall (v:val) (l:loc),
  triple (val_get l) 
    (l ~~> v) 
    (fun r => \[r = v] \* (l ~~> v)).

(** The function [val_get_hd] performs a similar task: it reads in a memory
    cell. In fact, given our encoding of list cells as pair of two consecutive 
    memory cells, the function [val_get_hd] could be implemented simply as
    a call to [val_get]. 

    The following specification assigns [val_get_hd] a precondition that
    describes a list cell, of the form [MCell v q p], which covers both 
    the head and the tail fields of the list cell. The postcondition 
    asserts that this cell is unmodified, and that the output is exactly
    the value [v]. *)

Parameter rule_get_hd_1 : forall (p:loc) (v:val) (q:loc),
  triple (val_get_hd p) 
    (MCell v q p)
    (fun r => \[r = v] \* (MCell v q p)).

(** It is interesting to investigate the relationship between the specification
    [rule_get] and the specification [rule_get_hd_1]. If we take the latter
    and unfold the definition of [MCell], we get: *)

Parameter rule_get_hd_2 : forall (p:loc) (v q:val),
  triple (val_get_hd p) 
    ((p ~~> v) \* ((p+1)%nat ~~> q))
    (fun r => \[r = v] \* (p ~~> v) \* ((p+1)%nat ~~> q)).

(** The above specification corresponds to the result of applying the
    frame rule to the specification [rule_get], to add the heap predicate
    [(p+1)%nat ~~> q] to both the precondition and the postcondition.
    (And also performing a renaming from [l] to [p].) *)


(* ================================================================= *)
(** ** Access to the head of a nonempty list *)

(** So far, we have shown that the function [val_get_hd], when provided a single
    list cell of the form [MCell v q p], does return its head value [v].
    Going one step further, we would like to state a higher-level specification
    for that same function. This new specification asserts that, when provided
    in the precondition a nonempty linked list of the form [MList L p], the 
    output value is equal to the head value of [L]. 
    
    When the list [L] is nonempty, it may be decomposed in the form [v::L'].
    In that case, calling [val_get_hd] should return the value [v].
    The specification stated below formalizes this idea. *)

Parameter rule_get_hd_3 : forall (p:loc) (v:val) (L':list val),
  triple (val_get_hd p) 
    (MList (v::L') p)
    (fun r => \[r = v] \* (MList (v::L') p)).

(** This new specification is, again, derivable using the frame rule,
    essentially by framing over all the cells from the linked lists
    except the head cell. Yet, the technical details of this proof
    involve rules that we have not yet studied, so we postpone this
    proof to a latter chapter. *)

(** There exists an alternative and slightly more practical way to state
    that specification. Rather than requiring upfront [L] to be of the form
    [v::L'], we only require a precondition [L <> nil]. In the postcondition,
    we assert that [L] decomposes as [r::L'], where [r] denotes the result
    value produced by the function, and [L'] denotes the tail of [L].
    The corresponding specification appears next. *)

Parameter rule_get_hd_4 : forall (p:loc) (L:list val),
  L <> nil ->
  triple (val_get_hd p) 
    (MList L p)
    (fun r => Hexists L', \[L = r::L'] \* (MList L p)).

(** According to the author's experience in interactive program verification,
    specifications such as [rule_get_hd_4], which describe the state using a
    precondition of the form [MList L p] together with a side-condition [L <> nil] 
    are usually much more convenient to exploit in practice than specifications
    such as [rule_get_hd_3], which describe the state directly in the constrained
    form [MList (v::L') p], imposing the list to be a cons. Although it is true
    that any nonempty list [L] can be decomposed in the form [v::L'], forcing
    the user to perform this decomposition manually prior to reasoning on the
    function call often adds unnecessary noise to the proof. *)

(** Remark: since [L'] is only used inside a pure heap predicate, the 
    postcondition above may be equivalently stated using a standard 
    existential quantification inside the pure heap predicate, as follows:

    (fun r => \[exists L', L = r::L'] \* (MList L p)).

    Yet, we find it more convenient in practice to pull out such existential
    quantifiers to the head of the postcondition.
*)


(* ================================================================= *)
(** ** Access to the tail of a list *)

(** Reading the tail pointer of a list is trickier than reading the head.
    Let [val_get_tl] be the function that, given a pointer [p] associated with
    the head of a nonempty list, returns the pointer on the tail of the list, 
    i.e., on the subsequent cell in the linked list. In C syntax:

  val get_hd(node* p) {
    return p->tl;
  }
*)

Parameter val_get_tl : val.

(** Consider a list of the form [MList L p] for some nonempty list [L].
    If we decompose [L] as [v::L'], the state is described as [MList (v::L') p],
    which is equivalent to [Hexists q, MCell v q p \* MList L' q]. The invokation
    of [val_get_tl] on [p] is supposed to return the pointer [q], yet the 
    identity of this pointer is not exposed in the representation predicate 
    [MList (v::L') p]. 

    Let us consider several candidate specifications to highlight the difficulty.
    What is the problem with the following specification?
*)

Parameter rule_get_tl_proposal_1 : forall (p:loc) (L:list val),
  L <> nil ->
  triple (val_get_tl p) 
    (MList L p)
    (fun r => Hexists q, \[r = val_loc q] \* (MList L p)).

(** What about the next one, which attempts to add the information that [q]
    is the tail pointer of the cell at location [p]? *)

Parameter rule_get_tl_proposal_2 : forall (p:loc) (L:list val),
  L <> nil ->
  triple (val_get_tl p) 
    (MList L p)
    (fun r => Hexists q v, \[r = val_loc q] \* (MList L p) \* (MCell v q p)).

(** Thus, it appears that the only way to properly specify the output value [q]
    is to state a postcondition that separates the head cell from the representation
    of the tail of the list. In other words, we have to give up on the idea that
    the function [val_get_tl], which does not modify the input list, can have a
    postcondition describing the full list [MList L p] like the precondition does. 
    A correct specification of [val_get_tl] appears next. *)

Parameter rule_get_tl : forall (p:loc) (L:list val),
  L <> nil ->
  triple (val_get_tl p) 
    (MList L p)
    (fun r => Hexists q v L', \[r = val_loc q] \* \[L = v::L'] 
                              \* MCell v q p \* MList L' q).

(** **** Exercise: 1 star, optional (rule_get_tl_cons)  *)
(** Reformulate the specification [rule_get_tl] using a precondition of the form
    [MList (v::L') p]. *)

(* FILL IN HERE *)

(** [] *)


(* ================================================================= *)
(** ** Extension of a list *)

(** The function [val_mcell_new] expects a value [v] and a pointer [q].
    It allocates a fresh cell with head value [v] and tail pointer [q],
    then returns the pointer, call it [p], on the fresh cell. Technically, 
    it returns a value, call it [r], of the form [val_loc p] for some [p]. 
    In C syntax:

  node* mcell_new(val v, node* q) {
    node* p = malloc(sizeof(node));
    p->hd = v;
    p->tl = q;
    return p;
  }
*)

Parameter val_mcell_new : val.

(** Let us assign two distinct specifications to this function. *)

(** **** Exercise: 2 stars, recommended (rule_mcell_new)  *)
(** Give a specification to [val_mcell_new] featuring an empty precondition, 
    and a postcondition of the form [MCell v q p]. *)

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 2 stars, recommended (rule_mlist_cons)  *)
(** Give a specification to [val_mcell_new] featuring a precondition of the
    form [MList L' q] and a postcondition of the form [MList (v::L') p]. *)

(* FILL IN HERE *)

(** [] *)


(** Remark: in a subsequent chapter, we will prove in the next chapter that the
    second specification ([rule_mcell_new_mlist]) is derivable from the first one
    ([rule_mcell_new_mcell]), by an application of the frame rule. Intuitively,
    [MCell v q p] and [MList L' q] can be folded into [MList (v::L') p]. *)


(* ################################################################# *)
(** * Reasoning about a list traversal *)

(* ================================================================= *)
(** ** Recursive computation of the length of a list *)

(** Consider a recursive function that computes the length of a list.
    In C syntax, such a function would be written as follows.

  int mlist_length(cell* p) {
    if (p == null) {
      return 0;
    } else {
      cell* q = p->tl;
      return 1 + mlist_length(q);
    }
*)

Parameter val_mlist_length : val.

(** This function can be specified with a precondition describing the input
    list, in the form [MList L p], and a similar postcondition, which moreover
    asserts that the output value corresponds to the length of the list [L]. *)

(* WORK IN CLASS *) Admitted.

(** Reminder: \[r = length L] actually stands for \[r = val_int (length L)]. *)

(** In a subsequent chapter, we will prove that the code satisfies the claimed
    specification. For the moment, let us describe at a high level the Separation
    Logic reasoning at play here.

    The proof goes by induction on the structure of the list [L].

    In the base case, [p] is null, the list [L] is empty, and [MList L p]
    is equal to [\[]] (by lemma [MList_nil]). The code returns the value [0].
    Thus, for the base case, we need to establish the triple: *)

Parameter proof_mlist_length_nil_case :
  triple 0
    \[]
    (fun (r:val) => \[r = length (@nil val)] \* \[]).

(** The above amounts to proving that [0 = length nil]. Easy enough.

    The case of the recursive call is much more interesting. In that case,
    [L] decomposes as [v::L'], and the representation predicate [MList L p]
    thus unfolds to [MCell v q p \* MList L' q]. At this point, we can frame
    out the heap predicate [MCell v q p], and focus on the tail of the list,
    described by [MList L' q]. This heap predicate is exactly what we need
    to reason about the recursive call of the length function on [q].

    By induction hypothesis, we know that the specification already holds
    for the list [L']. More precisely, we may assume [val_mlist_length] to
    be well-behaved when applied to any pointer [p'] under a precondition
    of the form [MList L' p']. *)

Section MListLengthRecCase.
Variable (v:val) (L L':list val) (p q:loc).

Parameter proof_mlist_length_induction_hypothesis : forall (p':loc), 
  triple (val_mlist_length p')
    (MList L' p')
    (fun (r:val) => \[r = length L'] \* MList L' p').

(** By specializing this induction hypothesis, instantiating [p'] as [q], we get: *)

Parameter proof_mlist_length_recursive_call : 
  triple (val_mlist_length q)
    (MList L' q)
    (fun (r:val) => \[r = length L'] \* MList L' q).

(** By applying the frame rule, we can add [MCell v q p] to both the precondition
    and the postcondition. *)

Parameter proof_mlist_length_recursive_call_framed : 
  triple (val_mlist_length q)
    (MCell v q p \* MList L' q)
    (fun (r:val) => \[r = length L'] \* MCell v q p \* MList L' q).

(** As mentioned previously, [MCell v q p \* MList L' q] is equal to [MList L p].
    Thus, the above triple can be rewritten into: *)

Parameter proof_mlist_length_recursive_call_folded : 
  triple (val_mlist_length q)
    (MList L p)
    (fun (r:val) => \[r = length L'] \* MList L p).

(** So far, we have assigned a triple for the recursive call on [q].
    The result of [val_mlist_length p] is equal to [1 + val_mlist_length q].
    Thus, we can derive the following triple for the outer call: *)

Parameter proof_mlist_length_cons_case : 
  triple (val_mlist_length p)
    (MList L p)
    (fun (r:val) => \[r = 1 + length L'] \* MList L p).

(** There remains to argue that \[r = 1 + length L'] entails [r = length L]
    when [L = v::L']. Easy enough. This concludes the proof *)

End MListLengthRecCase.

(** This proof illustrates a standard pattern of Separation Logic reasoning
    on a recursive function used to traverse a recursive list structure
    (and, more generally, any tree-shaped data structure):
    (1) unfold the definition of a recursive representation predicate,
    (2) apply the frame rule,
    (3) invoke the induction hypothesis,
    (4) fold back everything.

    Such "frame process" can be summarized into a table, as shown in the slide
    below. *)



(* ================================================================= *)
(** ** In place increment *)

(** Consider a recursive function that increments each of the integers stored
    in a list of integers. In C syntax, this function could be written as follows.

  int mlist_incr(cell* p) {
    if (p != null) {
      int x = q->hd;
      q->hd = x + 1;
      cell* q = p->tl;
      mlist_incr(q);
    }
*)

Parameter val_mlist_incr : val.

(** A call to [val_mlist_incr] on a list described by [L] has for effect
    to change it, in place, to a list described by [LibList.map succ L], 
    where [succ] is adding one unit to a value, assuming it is an integer
    (else it is unspecified). *)
    
Definition succ v :=
  match v with
  | val_int n => val_int (n + 1)
  | _ => v (* arbitrary result *)
  end.


(** **** Exercise: 2 stars, recommended (rule_mlist_incr)  *)
(** Give a specification for the function [val_mlist_incr], with a postcondition
    involving a list of the form [map succ L]. *)

Parameter rule_mlist_incr : forall (L:list val) (p:loc), 
  triple (val_mlist_incr p)
    (MList L p)
    (fun (r:val) => \[r = val_unit] \* MList (LibList.map succ L) p).

(** [] *)


(** **** Exercise: 2 stars, recommended (proof_mlist_incr_recursive_call_framed)  *)
(** Write down on paper the "frame process" at play here. For conciseness,
    you may abbreviate [LibList.map succ L] as [map (+1) L]. 
    The last proof step should explicitly exploit the equality:
    [(v+1) :: (map (+1) L')  =  map (+1) (v::L')].

    Then, state formally the lemma [proof_mlist_incr_recursive_call_framed],
    counterpart of [proof_mlist_length_recursive_call_framed] in the previous
    example, to describe the state after the recursive call and after applying
    the frame rule to the head cell. *)

Section MListIncrRecCase.
Variable (v:val) (L L':list val) (p q:loc).

(* FILL IN HERE *)

End MListIncrRecCase.

(** [] *)



(* ================================================================= *)
(** ** Imperative list length *)

(** Using a recursive function is not the only way to traverse a linked list.
    In fact, in C code, it is idiomatic to use a while loop for that purpose.
    Consider the following alternative implementation of the function that
    computes the length of a linked list.


  int mlist_length_loop(cell* p) {
    cell* r = p;
    int t = 0;
    while (r != null) {
      t++;
      r = r->tl;
    }
    return t;
  }


  Using ML syntax makes it clearer that [r] and [t] correspond to ref cells.
  Let us pretend for a minute that ML features null pointers, so that we may
  focus on the following code.


  let mlist_length_loop p =
    let r = ref p in
    let t = ref 0 in
    while !r <> null do
      t := t + 1;
      let q = !r in
      r := q.tl;
    done;
    !t


  Let us now try to describe the initial state, the final state, and the state 
  at every iteration of the loop.
*)

Section MListLengthLoop.
Variable (p:loc) (t:loc) (L:list val).

(** Just before the loop, the state consists of the input list, described by
    [MList L p] and two reference cells, [r] with contents [p], and [t] with
    contents [0]. The following Separation Logic assertion describes the 
    state just before the first iteration of the loop. *)

Definition mlist_length_loop_initial_state : hprop :=
(* WORK IN CLASS *) Admitted.

(** Just after the loop, the state consists of the input list, unchanged,
    and the two reference cells have updated contents: [r] has contents [null], 
    and [t] has contents [length L]. The following Separation Logic assertion
    describes the state just after the last iteration of the loop. *)

Definition mlist_length_loop_final_state : hprop :=
(* WORK IN CLASS *) Admitted.

(** Consider now the state at an arbitrary iteration of the loop. The reference
    [r] stores the pointer on a cell denoting the current position in the
    traversal, and the reference [t] stores the number of cells already passed by.
    Try to state a Separation Logic assertion describing the invariant just
    after the i-th iteration of the loop. *)

(* WORK IN CLASS *) Admitted.

End MListLengthLoop.



(* ################################################################# *)
(** * List segments *)

(* ================================================================= *)
(** ** Representation predicate for list segments *)

(** In what follows, we present the formal definition of [MListSeg]. Let us first
    recall the definition of [MList L p], because [MListSeg q L p] is just a
    generalization of that definition. *)

Module RecallMList.

  Fixpoint MList (L:list val) (p:loc) : hprop :=
    match L with
    | nil => \[p = null]
    | x::L' => Hexists (p':loc), (MCell x p' p) \* (MList L' p')
    end.

End RecallMList.

(** Whereas [MList L p] decribes a sequence of linked cells terminated by a null
    tail pointer, the predicate [MListSeg q L p] describes a sequence of linked
    cells terminated by some tail pointer [q], which is not necessarily null.
    Thus, to generalize, the definition, all we have to do is add an argument [q]
    and replace [p = null] with [p = q] in the base case, as shown below. *)

Fixpoint MListSeg (q:loc) (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = q]
  | x::L' => Hexists (p':loc), (MCell x p' p) \* (MListSeg q L' p')
  end.

(** We may formally prove that any full list, described by a predicate of the
    form [MList L p], can be converted into a null-terminated list segment
    [MListSeq null L p], and reciprocally. *)

Lemma MListSeg_null_eq_MList : forall (L:list val) (p:loc),
  MListSeg null L p = MList L p.
Proof using.  
  intros L. induction L; intros; simpl.
  { auto. }
  { fequal. applys fun_ext_1. intros x. rewrite IHL. auto. }
Qed.

(** The above equality shows that we could just as well define [MList]
    on top of [MListSeg], as follows. *)

Definition MList' (L:list val) (p:loc) := 
  MListSeg null L p.

(** In the next chapter, we will prove additional results about list segments,
    such as rules for splitting and merging list segments. For the moment,
    let us investigate further use of list segments to express specifications
    and invariants. *)


(* ================================================================= *)
(** ** Representation of a mutable queue *)

(** Consider a particular implementation of a mutable queue data structure,
    represented in memory as described next. The queue essentially consists
    of a linked list of cells, plus one "structure" cell with two pointers: one pointing
    to the first cell in the linked list, and one pointing to the last cell of the
    linked list. The linked list contains one cell per item in the queue, plus
    one spare cell. This spare cell is used to ensure that the linked list always
    contains at least one cell, even when the queue is empty. In the case of an
    empty queue, both the head pointer and the tail pointer point to that spare cell. *)

(** Let us try to define the predicate [MQueue L p], which describes a mutable
    queue, whose structure cell is at location [p] and whose items correspond to
    the values in the list [L]. Hint: use [MCell] twice, to describe the structure
    cell and the spare cell, and use [MListSeg] to describe the linked list.
    Make sure to properly quantify all variables that are needed. *)

Definition MQueue (L:list val) (p:loc) :=
(* WORK IN CLASS *) Admitted.


(* ================================================================= *)
(** ** Interface for a mutable queue *)

Section MQueueInterface.

(** Let us now forget about the particular implementation of a mutable queue
    considered above, and focus on the specification the interface that any
    mutable queue data structure should satisfy. (In a subsequent chapter,
    we will prove that the particular queue implementation considered above
    indeed satisfies the formal interface described below.) 

    The operations described by the interface are listed below and described next. *)

Variables 
  val_create 
  val_is_empty 
  val_push_back
  val_push_front
  val_pop_front
  val_transfer 
  : val.

Implicit Types p : loc.
Implicit Types r v : val.
Implicit Types L : list val.

(** The operation [create()] builds an empty queue. Its precondition is empty
    and its postcondition asserts that [MQueue nil p] holds. *)

Parameter rule_create : forall p L,
  triple (val_create val_unit)
    \[]
    (fun r => Hexists p, \[r = val_loc p] \* MQueue nil p).

(** The operation [is_empty p] returns a boolean value indicating whether
    the queue at location [p] is empty. The precondition requires the queue
    [MQueue L p] and returns it unchanged. The output value [r] is a boolean
    value, which is true if and only if [L = nil]. In other words, [r] is equal
    to [val_bool (isTrue (L = nil))], where [val_bool] is a coercion which can
    be left implicit and where [isTrue] converts a [Prop] into a [bool]. *)

Parameter rule_is_empty : forall p L,
  triple (val_is_empty p)
    (MQueue L p)
    (fun r => \[r = isTrue (L = nil)] \* MQueue L p).

(** The operation [push_back v p] adds [v] to the tail of the queue [q].
    The input state is [MQueue L p]. The output state is [MQueue (L&v) p],
    where [L&v] is a shorthand of [L ++ (v::nil)], describing the fact that
    the value [v] is added to the tail of [L]. *)

Parameter rule_push_back : forall v p L,
  triple (val_push_back v p)
    (MQueue L p)
    (fun r => \[r = val_unit] \* MQueue (L&v) p).

(** The operation [push_front v p] adds [v] to the front of the queue [q]. *)

(** **** Exercise: 2 stars, recommended (rule_push_front)  *)
(** Give a specification for the function [push_front]. *)

(* FILL IN HERE *)

(** [] *)


(** The operation [pop_front p] extracts and returns the value at the front of [q]. *)

(** **** Exercise: 2 stars, recommended (rule_pop_front)  *)
(** Give a specification for the function [pop_front].
    Hint: you may get inspiration from the specification of the tail function
    on lists ([rule_get_tl]). *)

(* FILL IN HERE *)

(** [] *)


(** The operation [transfer p1 p2] extracts all the elements from [p2] and adds
    them to the tail of [p1]. Its precondition describes two disjoint queues,
    as [MQueue L1 p1] and [MQueue L2 p2], respectively. The postcondition asserts
    that [p2] is emptied, and that [p1] contains items from both [L1] and [L2]. *)

(* WORK IN CLASS *) Admitted.

End MQueueInterface.

(* ################################################################# *)
(** * Binary trees *) 

(* ================================================================= *)
(** ** Representation of binary trees *)

(** In what follows, we generalize the definition of a representation predicate
    for lists, of the form [MList p L], where [L] denotes a Coq list, to a
    representation predicate for binary trees, of the form [MTree p T], where
    [T] denotes a Coq binary tree. Binary trees are defined by the following
    inductive definition: a tree is either a leaf, or a node made of an integer
    and two subtrees. 

  typedef struct node {
    int item;
    node* left;
    node* right;
  } node;
*)

Inductive tree : Type :=
  | Leaf : tree
  | Node : int -> tree -> tree -> tree.

(** Remark: the definition can be generalized to _polymorphic_ trees, with nodes
    storing values of some arbitrary type, however for simplicity we here restrict
    ourselves to nodes storing integer values. *)

(** For mutable lists, we used the null pointer to describe empty lists, and
    introduce the representation predicate [MCell v q p] to describe a list
    cell at location [p] storing a value [v] and a tail pointer [q].
    Similarly, for mutable trees, we use the null pointer to describe
    an empty tree (i.e., a leaf), and introduce a new representation predicate
    written [TCell x p1 p2 p] to describe a tree node at location [p]
    storing an integer value [x] and two child pointers [p1] and [p2],
    pointing to the left branch and the right branch, respectively. 
    [TCell] is defined as follows: *)

Definition TCell (x:val) (p1 p2:loc) (p:loc) : hprop :=
  (p ~~> x) \* ((p+1)%nat ~~> p1) \* ((p+2)%nat ~~> p2).

(** Remark: the above definition is rather clumsy, but don't worry, in a
    subsequent chapter, we will introduce support for a clean, generic
    notation for describing records in Separation Logic, in the form:
      [Record`{ item := x; left := p1; right := p2 }]. 
*)

(** We are now ready to define [MTree T p], akin to the definition of [MList L p].
    The definition is recursive on the structure of the tree [T].
    When the tree is a leaf, we require [p] to be null.
    When the tree is a node of the form [x T1 T2], we require the location [p]
    to correspond to an allocated node cell, described as [TCell x p1 p2 p],
    and we require [p1] and [p2] to be the entry point of the two subtrees,
    described as [MTree T1 p1] and [MTree T2 p2}], respectively.
    Note that both [p1] and [p2] are existentially quantified.
*)

(* WORK IN CLASS *) Admitted.


(* ================================================================= *)
(** ** Construction of a tree *)

(** The function [val_tcell_new] expects a integer [x] and two pointers
    [p1] and [p2], and it allocates a fresh node cell storing [x], [p1] and
    [p2], and returns the location, call it [p], of that fresh node.
    
    In C syntax, the function could be implemented as follows:

  node* tcell_new(int x, node* p1, node* p2) {
    node* p = malloc(sizeof(node));
    p->item = x;
    p->left = q1;
    p->right = q2;
    return p;
  }
*)

Parameter val_tcell_new : val.

(** **** Exercise: 1 star, optional (rule_tcell_new)  *)
(** Taking inspiration from the specification [rule_mcell_new] describing
    the allocation of a list cell, give a specification for [val_tcell_new],
    with an empty precondition and a postcondition expressed using [TCell]. *)

(* FILL IN HERE *)

(** [] *)

(** **** Exercise: 2 stars, recommended (rule_mtree_node)  *)
(** Taking inspiration from the specification [rule_mlist_cons] describing
    the extension of a list with a head item, give an alternative specification
    for [val_tcell_new], with a precondition describing the existence of
    two disjoint subtrees, and a postcondition of the form [MTree (Node x T1 T2) p]. *)

(* FILL IN HERE *)

(** [] *)

(** The function [val_mtree_copy] takes as argument a pointer on a binary tree,
    and it produces a fresh, independent copy of that tree. In C syntax, this
    function could be implemented as follows.

  node* mtree_copy(node* p) {
    if (p == null) {
      return null; 
    } else {  
      node* q1 = mtree_copy(p->left);
      node* q2 = mtree_copy(p->right);
      return tcell_new(p->item, q1, q2);
    }
  }
*)

Parameter val_mtree_copy : val.

(** **** Exercise: 2 stars, recommended (rule_mtree_copy)  *)

(** Give a specification for [val_mtree_copy].
    Hint: the postcondition should describe two disjoint mutable trees,
    both with the same logical description, that is, the same Coq tree [T]. *)

(* FILL IN HERE *)

(** [] *)

(** Let us study, at a high level, the mechanisms at play in the verification
    of the code of the tree copy function. In the leaf case, [p] is null
    and the heap predicate [MTree null Leaf] is equivalent to the empty
    heap predicate \[]. Thus, no allocation is needed to make a copy of
    an empty tree. In the case of a node, the representation predicate
    [MTree T p] can be unfolded to [TCell x p1 p2 p \* MTree T1 p1 \* MTree T2 p2].
    Then, three steps are involved.
    - First, recursively make a copy of the left subtree; during that phase,
      the current node and the right subtree are "framed out".
    - Second, recursively make a copy of the right subtree; during that phase,
      the current node, the left subtree, and the copy of the left subtree
      are framed out.
    - Third, call the function [val_tcell_new] to allocate a fresh node;
      during that phase, the current node, the left and right subtrees,
      as well as their copies, are framed out.

    At the return point, the description of the input tree can be folded
    back to its original form [MTree T p] and, similarly, the fresh copy
    can be folded into the form [MTree T p'], where [p'] denotes the
    location of the fresh node.

    The "frame process" at play here (recall [rule_mlist_length]) is
    summarized by the following table. *)


(* ================================================================= *)
(** ** Complete binary trees *) 

(** A complete binary tree is a binary tree whose leaves are found at
    the same depth. In what follows, we investigate the Separation Logic
    specification of a complete binary tree. *)

(** Our first goal is to define a representation predicate written
    [MTreeDepth n T p], extending [Mtree n T p] to assert that all
    leaves in the tree are found at a depth [n].
    Can you think of a definition for [MTreeDepth]? *)

(* WORK IN CLASS *) Admitted.

(** The above definitions are correct, yet impractical to work with.
    Intuitively, it duplicates a lot of the logic that is already
    captured by the predicate [MTree]. It is much more practical
    and satisfying to reuse the definition of [MTree] to define
    [MTreeDepth]. 

    Doing so is actually straightforward: [MTreeDepth n T p] is simply
    [MTree T p] augmented with the information that the _logical_ tree [T] 
    has all leaves at depth [n]. This latter property can be formalized
    by an induction definition, written [depth n T], and defined inductively
    as follows. *)

Inductive depth : nat -> tree -> Prop :=
  | depth_leaf :
      depth 0%nat Leaf
  | depth_node : forall n x T1 T2,
      depth n T1 ->
      depth n T2 ->
      depth (S n) (Node x T1 T2).

(** Then [MTreeDepth n T p] consists of the conjunction of [MTree T p]
    and [depth n T]. Formally: *)
 
Definition MTreeDepth (n:nat) (T:tree) (p:loc) : hprop :=
  (MTree T p) \* \[depth n T].


(** It is sometimes useful to assert that a tree is a complete binary tree
    without specifying its depth. The presentation predicate
    [MTreeComplete T p] asserts that the tree [T] satisfies [depth n T]
    for some [n]. It may be defined in three equivalent ways. *)
    
(* WORK IN CLASS *) Admitted.


(* ================================================================= *)
(** ** Binary search trees *) 

Require Import LibOrder LibSet.

(** To conclude this chapter, we investigate the specification of a
    mutable binary search tree. The goal here is to define a
    representation predicate, written [STree E p], to assert that
    the tree at location [p] describes a (valid) binary search tree,
    whose items stored in the node describe the set [E].

    Here, [E] has type [set int], where [set] is defined in TLC's
    [LibSet] file. For the purpose of this course, the following set
    definitions are used:
    - [\{}] describes the empty set.
    - [\{x}] describes the singleton set made of element [x] alone.
    - [E1 \u E2] describes set union.
    - [x \in E] asserts that [x] belongs to the set [E].
    - [foreach P E] asserts that all elements in [E] satisfy the 
      predicate [P]. 

    To define [STree E p], we are going to leverage the definition 
    of [MTree T p], and use an inductively-defined predicate,
    written [stree T E] in order to relate the tree [T] with the set [E].
    This predicate not only asserts that [E] consists of the set of
    items stored in the nodes of [T], it also enforces the "search tree"
    invariants on the tree [T]: smaller values are found in left subtrees,
    and greater values are found in right subtrees. *)

(** The predicate [stree T E] is defined as follows:
    - A leaf describes the empty set.
    - A node [Node x T1 T2] describes a set of the form [\{x} \u E1 \u E2],
      where [E1] is the set associated with the left subtree [T1], storing
      only values smaller than [x], and [E2] is the set associated with the
      right subtree [T2], storing only values greater than [x].

    Below, the predicate [foreach (fun y => y < x) E1] expresses that
    any element [y] that belongs to [E1] is smaller than [x].
 *)

Inductive stree : tree -> set int -> Prop :=
  | stree_leaf : 
      stree Leaf \{}
  | stree_node : forall x T1 T2 E1 E2,
      stree T1 E1 ->
      stree T2 E2 -> 
      foreach (fun y => y < x) E1 -> 
      foreach (fun y => y > x) E2 ->
      stree (Node x T1 T2) (\{x} \u E1 \u E2).

(** The representation predicate for binary search trees, [STree E p],
    is obtained by combining [MTree T p] with [stree T E], and 
    existentially quantifying over the tree [T]. *)

Definition STree (E:set int) (p:loc) :=
  Hexists (T:tree), (MTree T p) \* \[stree T E].

(** Finally, to illustrate a use case for the representation predicate
    [STree E p], consider a search function, which performs a search
    for a given integer [x] into a binary tree at location [p]. *)

Parameter val_btree_search : val.

(** The specification of this function has a precondition [STree E p],
    asserting that [p] is an entry point into a valid binary tree
    describing a set [E]. The postcondition asserts that this tree
    is unchanged, and that the output value is a boolean indicating
    whether [x] belongs to the set [E]. (Recall that [isTrue] converts
    a proposition (here [x \in E]) into a boolean value.) *)

Parameter rule_btree_search : forall (x:int) (p:loc) (E:set int),
  triple (val_btree_search x p)   
    (STree E p)
    (fun r => \[r = isTrue (x \in E)] \* STree E p).

(** In a subsequent chapter, we will prove that the recursive implementation
    of [val_btree_search] satisfies the above specification. The proof goes
    by induction on the underlying tree [T], which, although is not visible
    in the outer specification, guides the structure of the proof. *)


















































