(** * Hoare: Hoare Logic *)

(* $Date: 2012-03-15 18:29:29 -0400 (Thu, 15 Mar 2012) $ *)

Require Export ImpList.

(** In the past couple of chapters, we've begun applying the
    mathematical tools developed in the first part of the course to
    studying the theory of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than properties of particular programs in the language.
      These included:

        - determinacy of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g. functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the optional chapter
          [Equiv.v]).

      If we stopped here, we would still have something useful: a set
      of tools for defining and discussing programming languages and
      language features that are mathematically precise, flexible, and
      easy to work with, applied to a set of key properties.  All of
      these properties are things that language designers, compiler
      writers, and users might care about knowing.  Indeed, many of
      them are so fundamental to our understanding of the programming
      languages we deal with that we might not consciously recognize
      them as "theorems."  But properties that seem intuitively
      obvious can sometimes be quite subtle -- or, in some cases,
      actually even wrong!

      We'll return to this theme later in the course when we discuss
      _types_ and _type soundness_.

    - We saw a couple of examples of _program verification_ -- using
      the precise definition of Imp to prove formally that certain
      particular programs (e.g., factorial and slow subtraction)
      satisfied particular specifications of their behavior. *)

(** In this chapter, we'll take this last idea further.  We'll
    develop a reasoning system called _Floyd-Hoare Logic_ -- commonly
    shortened to just _Hoare Logic_ -- in which each of the syntactic
    constructs of Imp is equipped with a single, generic "proof rule"
    that can be used to reason about programs involving this
    construct.

    Hoare Logic originates in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a huge variety of tools that are now being
    used to specify and verify real software systems. *)

  
(* ####################################################### *)
(** * Hoare Logic *)

(** Hoare Logic combines two beautiful ideas: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that these specifications are met --
    where by "compositional" we mean that the structure of proofs
    directly mirrors the structure of the programs that they are
    about. *)

(* ####################################################### *)
(** ** Assertions *)

(** If we're going to talk about specifications of programs, the
    first thing we'll want is a way of making _assertions_ about
    properties that hold at particular points during a program's
    execution -- i.e., properties that may or may not be true of a
    given state of the memory. *)

Definition Assertion := state -> Prop.

(** **** Exercise: 1 star (assertions) *)
(** Paraphrase the following assertions in English.
[[
      fun st =>  asnat (st X) = 3 
      The states where [X] is equal to 3 hold.

      fun st =>  asnat (st X) = x
      The states where [X] is equal to [x] hold.

      fun st =>  asnat (st X) <= asnat (st Y)
      The states where [X] is less than or equal to [Y] hold.

      fun st =>  asnat (st X) = 3 \/ asnat (st X) <= asnat (st Y)
      The states where [X] is equal to 3 or X is less than or equal to 
      [Y] hold.

      fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x 
                 /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x)
      The states where [Z] is equal to the squre root of [x] hold, and we
      assume x >= 0.

      fun st =>  True
      Any states will hold.

      fun st =>  False
      No state holds.
]]
[] *)

(** This way of writing assertions is formally correct -- it
    precisely captures what we mean, and it is exactly what we will
    use in Coq proofs.  We'll also want a lighter, less formal
    notation for discussing examples, since this one is a bit
    heavy: (1) every single assertion that we ever write is going to
    begin with [fun st => ]; (2) this state [st] is the only one that
    we ever use to look up variables (we will never need to talk about
    two different memory states at the same time); and (3) all the
    variable lookups in assertions are cluttered with [asnat] or
    [aslist] coercions.  So, when writing down assertions informally,
    we'll make some simplifications: drop the initial [fun st =>],
    write just [X] instead of [st X], and elide [asnat] and
    [aslist]. *)
(** Informally, instead of writing
[[
      fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x 
                 /\ ~ ((S (asnat (st Z))) * (S (asnat (st Z))) <= x)
]]
    we'll write just
[[
         Z * Z <= x 
      /\ ~((S Z) * (S Z) <= x).
]]
*)

(* ####################################################### *)
(** ** Hoare Triples *)

(** Next, we need a way of specifying -- making claims about -- the
    behavior of commands. *)

(** Since we've defined assertions as a way of making claims about the
    properties of states, and since the behavior of a command is to
    transform one state to another, it is natural to express claims
    about commands in the following way:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates, then the final state is
        guaranteed to satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The property [P] is
    called the _precondition_ of [c], while [Q] is the _postcondition_
    of [c]. *)
 
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:
[[
       {{P}}  c  {{Q}}.
]]
*)
(** (Traditionally, Hoare triples are written [{P} c {Q}], but single
    braces are already used for other things in Coq.)  *)

Notation "{{ P }}  c" :=          (hoare_triple P c (fun st => True)) 
                                  (at level 90) 
                                  : hoare_spec_scope.
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.  The first notation -- with missing postcondition -- will
    not actually be used for a while; it's just a placeholder for a
    notation that we'll want to define later, when we discuss
    decorated programs.) *)

(** **** Exercise: 1 star (triples) *)
(** Paraphrase the following Hoare triples in English.  
[[
      {{True}} c {{X = 5}}
      [c] is started at any state, and it eventually terminates, 
      the finaly state satisfies that [X] is equal to 5.

      {{X = x}} c {{X = x + 5)}}
      [c] is started with a state satisfying [X] is equal to [x], and
      it eventually ternimates with the final state satisfying that
      [X] is equal to [x] + 5.

      {{X <= Y}} c {{Y <= X}}
      [c] is started with a state satisfying [X] <= [Y], and it eventually
      terminates with the final state satisfying that [Y] <= [X].

      {{True}} c {{False}}
      From any state with which [c] is started with, [c] never terminates.

      {{X = x}} 
      c
      {{Y = real_fact x}}.
      [c] is started with a state satisfying [X] = [x], and it eventually
      terminates with the final state satisfying that [Y] is the factorial
      of [x]

      {{True}} 
      c 
      {{(Z * Z) <= x /\ ~ (((S Z) * (S Z)) <= x)}}
      From any state with which [c] is started, [c] evetuanlly terminates
      with [Z] is the square root of [x], assuming [x] >= 0.
]]
 *)
(** [] *)

(** **** Exercise: 1 star (valid_triples) *)
(** Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?  
[[
      {{True}} X ::= 5 {{X = 5}}
      _valid_

      {{X = 2}} X ::= X + 1 {{X = 3}}
      _valid_

      {{True}} X ::= 5; Y ::= 0 {{X = 5}}
      _valid_

      {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}
      _valid_

      {{True}} SKIP {{False}}
      _invalid_

      {{False}} SKIP {{True}}
      _valid_

      {{True}} WHILE True DO SKIP END {{False}}
      _valid_

      {{X = 0}} 
      WHILE X == 0 DO X ::= X + 1 END 
      {{X = 1}}
      _valid_

      {{X = 1}} 
      WHILE X <> 0 DO X ::= X + 1 END 
      {{X = 100}}
      _valid_
]]
*)
(** (Note that we're using informal mathematical notations for
   expressions inside of commands, for readability.  We'll continue
   doing so throughout the chapter.) *)
(** [] *)

(** To get us warmed up, here are two simple facts about Hoare
    triples. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ####################################################### *) 
(** ** Weakest Preconditions *)

(** Some Hoare triples are more interesting than others.  For example,
[[
      {{ False }}  X ::= Y + 1  {{ X <= 5 }}
]]
    is _not_ very interesting: it is perfectly valid, but it tells us
    nothing useful.  Since the precondition isn't satisfied by any
    state, it doesn't describe any situations where we can use the
    command [X ::= Y + 1] to achieve the postcondition [X <= 5].

    By contrast, 
[[
      {{ Y <= 4 /\ Z = 0 }}  X ::= Y + 1 {{ X <= 5 }}
]]
    is useful: it tells us that, if we can somehow create a situation
    in which we know that [Y <= 4 /\ Z = 0], then running this command
    will produce a state satisfying the postcondition.  However, this
    triple is still not as useful as it could be, because the [Z = 0]
    clause in the precondition actually has nothing to do with the
    postcondition [X <= 5].  The _most_ useful triple (with the same
    command and postcondition) is this one:
[[
      {{ Y <= 4 }}  X ::= Y + 1  {{ X <= 5 }}
]]
    In other words, [Y <= 4] is the _weakest_ valid precondition of
    the command [X ::= Y + 1] for the postcondition [X <= 5]. *)
 
(** In general, we say that "[P] is the weakest precondition of
    [c] for [Q]" if

    - [{{P}} c {{Q}}], and

    - whenever [P'] is an assertion such that [{{P'}} c {{Q}}], we
      have [P' st] implies [P st] for all states [st].  *)

(** That is, [P] is the weakest precondition of [c] for [Q]
    if (a) [P] _is_ a precondition for [Q] and [c], and (b) [P] is the
    _weakest_ (easiest to satisfy) assertion that guarantees [Q] after
    executing [c]. *)

(** The second of the conditions above is essentially a form of
    logical implication at the level of assertions. Because of the
    frequency of its occurrence, it is useful to define a little
    notation: *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

(** We will write [P ~~> Q] (in ASCII, [P ~][~> Q]) for [assert_implies
    P Q]. *)

Notation "P ~~> Q" := (assert_implies P Q) (at level 80).
Notation "P <~~> Q" := (P ~~> Q /\ Q ~~> P) (at level 80).

(** **** Exercise: 1 star (wp) *)
(** What are the weakest preconditions of the following commands
   for the following postconditions?
[[
     {{ ? }}  SKIP  {{ X = 5 }}

     {{ ? }}  X ::= Y + Z {{ X = 5 }}

     {{ ? }}  X ::= Y  {{ X = Y }}

     {{ ? }}  
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

     {{ ? }}  
     X ::= 5
     {{ X = 0 }}

     {{ ? }}  
     WHILE True DO X ::= 0 END
     {{ X = 0 }}
]]
*)
(** [] *)

(* ####################################################### *) 
(** ** Proof Rules *)

(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of Hoare triples.  That is, the
    structure of a program's correctness proof should mirror the
    structure of the program itself.  To this end, in the sections
    below, we'll introduce one rule for reasoning about each of the
    different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules that are useful for gluing things
    together. *)

(* ####################################################### *) 
(** *** Assignment *)

(** The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this (valid) Hoare triple:
[[
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
]]
    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].  That is, the property of being equal
    to [1] gets transferred from [Y] to [X].

    Similarly, in
[[
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
]]
    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment.

    More generally, if [a] is _any_ arithmetic expression, then
[[
       {{ a = 1 }}  X ::= a {{ X = 1 }}
]]
    is a valid Hoare triple. 

    Even more generally, [a] is _any_ arithmetic expression and [Q] is
    _any_ property of numbers, then
[[
       {{ Q(a) }}  X ::= a {{ Q(X) }}
]]
    is a valid Hoare triple.

    Rephrasing this a bit gives us the general Hoare rule for
    assignment:
[[
      {{ Q where a is substituted for X }}  X ::= a  {{ Q }}
]]
    For example, these are valid applications of the assignment
    rule:
[[
      {{ (X <= 5) where X + 1 is substituted for X 
         i.e., X + 1 <= 5 }}  
      X ::= X + 1  
      {{ X <= 5 }}

      {{ (X = 3) where 3 is substituted for X 
         i.e., 3 = 3}}  
      X ::= 3  
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) where 3 is substituted for X 
         i.e., (0 <= 3 /\ 3 <= 5)}}  
      X ::= 3  
      {{ 0 <= X /\ X <= 5 }}
]]
*)

(** To formalize the rule, we begin with the notion of "substitution
    in an assertion": *)

Definition assn_sub X a Q : Assertion :=
  fun (st : state) =>
    Q (update st X (aeval st a)).

(** Now the precise proof rule for assignment: 
[[[
      ------------------------------ (hoare_asgn)
      {{assn_sub X a Q}} X::=a {{Q}}
]]]
*)

Theorem hoare_asgn : forall Q X a,
  {{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(** Here's a first formal proof using this rule. *)

Example assn_sub_example : 
  {{assn_sub X (ANum 3) (fun st => asnat (st X) = 3)}} 
  (X ::= (ANum 3)) 
  {{fun st => asnat (st X) = 3}}.
Proof.
  apply hoare_asgn.  Qed.

(** **** Exercise: 3 stars (hoare_asgn_examples) *)
(** Translate these informal Hoare triples...
[[
       {{ assn_sub X (X + 1) (X <= 5) }}  X ::= X + 1  {{ X <= 5 }}
       {{ assn_sub X 3 (0 <= X /\ X <= 5) }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
   ...into formal statements and use [hoare_asgn] to prove them. *)

Example assn_sub_1:
  {{ assn_sub X (APlus (AId X) (ANum 1)) 
                (fun st => asnat (st X) <= 5) }}  
  (X ::= APlus (AId X) (ANum 1))  
  {{fun st => asnat (st X) <= 5 }}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_2:
  {{ assn_sub X (ANum 3) 
              (fun st => 0 <= asnat (st X) /\ asnat (st X) <= 5) }}  
  (X ::= (ANum 3))  
  {{fun st => 0 <= asnat (st X) /\ asnat (st X) <= 5 }}.
Proof.
  apply hoare_asgn.  Qed.
(** If I directly apply [hoare_asgn], coq does not think
   [fun st => 0<=3<=5] and [fun st => 0<=X<=5], so I have to
   apply [hoare_asgn] in small steps.*)

(** [] *)

(** **** Exercise: 3 stars (hoarestate2) *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
[[
      {{ True }} X ::= a {{ X = a }}
]]
    Explain what is wrong with this rule.

    Because [a] is not bounded in the precondition, this triple
    seems to come out of thin air, making no sense.
*)
(** [] *)

(** **** Exercise: 3 stars, optional (hoare_asgn_fwd) *)
(** However, using an auxiliary variable [x] to remember the original
    value of [X] we can define a Hoare rule for assignment that does,
    intuitively, "work forwards" rather than backwards.
[[[
  ------------------------------------------ (hoare_asgn_fwd)
  {{fun st => Q st /\ st X = x}}
    X ::= a
  {{fun st => Q st' /\ st X = aeval st' a }}
  (where st' = update st X x)
]]]
    Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct (the first hypothesis is the functional extensionality
    axiom, which you will need at some point).
*)


Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y}, (forall (x: X), f x = g x) ->  f = g) ->
  forall x a Q,
  {{fun st => Q st /\ st X = x}}
    X ::= a
  {{fun st => Q (update st X x) /\ st X = aeval (update st X x) a }}.
Proof.
  intros functional_extensionality v a Q.
  unfold hoare_triple.
  intros st st' HE HQ.
  inversion HE. subst.
  inversion HQ as [HL HR].
  assert (update st X v = st) as Hst.
      apply functional_extensionality.
      intros. apply update_same.
      assumption.
  assert (update (update st X (aeval st a)) X v 
          = update st X v) as Hshadow.
      apply functional_extensionality.
      intros. apply update_shadow.
  split. 
  Case "left".
      rewrite Hshadow. rewrite Hst. assumption.
  Case "right".
      rewrite Hshadow. rewrite Hst. rewrite update_eq. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars (hoare_asgn_weakest) *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall P X a Q,
  {{P}} (X ::= a) {{Q}} ->
  P ~~> assn_sub X a Q.
Proof.
  intros P X a Q H.
  unfold hoare_triple in H.
  unfold assert_implies.
  intros. unfold assn_sub.
  assert ((X::=a)/st||update st X (aeval st a)).
  Case "Proof of assertion".
      apply E_Asgn. reflexivity.
  apply (H st (update st X (aeval st a))).
  assumption. assumption.
Qed.
(** [] *)

(* ####################################################### *) 
(** *** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.

    For instance, while
[[
      {{assn_sub X 3 (X = 3)}} X ::= 3 {{X = 3}},
]]
    follows directly from the assignment rule, 
[[
      {{True}} X ::= 3 {{X = 3}}.
]]
    does not.  This triple is also valid, but it is not an instance of
    [hoare_asgn] because [True] and [assn_sub X 3 (X = 3)] are not
    syntactically equal assertions.  However, they are logically
    equivalent, so if one triple is valid, then the other must
    certainly be as well.  We could capture this observation with the
    following rule:
[[[
                {{P'}} c {{Q}}
                  P <~~> P'
         -----------------------------   (hoare_consequence_eq)
                {{P}} c {{Q}}
]]]
    Generalizing this line of thought a bit further, if we can derive
    [{{P}} c {{Q}}], it is valid to change [P] to [P'] as long as [P']
    is strong enough to imply [P], and change [Q] to [Q'] as long as
    [Q] implies [Q'].  This observation is captured by two _Rules of
    Consequence_.
[[[
                {{P'}} c {{Q}}
                   P ~~> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ~~> Q 
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
]]]
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ~~> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ~~> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

(** For example, we might use the first consequence rule like this:
[[
                {{ True }} =>
                {{ 1 = 1 }} 
    X ::= 1
                {{ X = 1 }}
]]
    Or, formally... 
*)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => asnat (st X) = 1}}.
Proof.
  apply hoare_consequence_pre 
    with (P' := assn_sub X (ANum 1) (fun st => asnat (st X) = 1)).
  apply hoare_asgn. 
  intros st H. reflexivity.  Qed.

(** Finally, for convenience in some proofs, we can state a "combined"
    rule of consequence that allows us to vary both the precondition
    and the postcondition. 
[[[
                {{P'}} c {{Q'}}
                   P ~~> P'
                   Q' ~~> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
]]]
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ~~> P' ->
  Q' ~~> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q. apply (Hht st st'). assumption.
  apply HPP'. assumption. Qed.


(* ####################################################### *)
(** *** Digression: The [eapply] Tactic *)

(** This is a good moment to introduce another convenient feature of
    Coq.  We had to write "[with (P' := ...)]" explicitly in the
    second line of the example above, to make sure that all of the
    metavariables in the premises to the [hoare_consequence_pre] rule
    would be set to specific values; since [P'] doesn't appear in the
    conclusion of [hoare_consequence_pre], the process of unifying the
    conclusion with the current goal doesn't constrain [P'] to a
    specific assertion.

    This is a little annoying, both because the assertion is a bit
    long and also because the very next thing we are going to do --
    applying the [hoare_asgn] rule -- will tell us exactly what it
    should be!  We can use [eapply] instead of [apply] to tell Coq,
    essentially, "Be patient: The missing part is going to be filled
    in soon." *)

Example hoare_asgn_example1' :
  {{fun st => True}} 
  (X ::= (ANum 1)) 
  {{fun st => asnat (st X) = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. reflexivity.  Qed.

(** In general, [eapply H] tactic works just like [apply H]
    except that, instead of failing if unifying the goal with the
    conclusion of [H] does not determine how to instantiate all
    of the variables appearing in the premises of [H], [eapply H]
    will replace these variables with _existential variables_
    (written [?nnn]) as placeholders for expressions that will be
    determined (by further unification) later in the proof. 

    There is also an [eassumption] tactic that works similarly. *)

(** **** Exercise: 2 stars (hoare_asgn_examples) *)
(** Translate these informal Hoare triples...
[[
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
   ...into formal statements and use [hoare_asgn] to prove them. *)

Example hoare_asgn_1:
  {{fun st=>(asnat (st X)) + 1 <= 5}}
  (X::= APlus (AId X) (ANum 1))
  {{fun st=>(asnat (st X)) <= 5}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.
  assumption. 
Qed.

Example hoare_asgn_2:
  {{fun st => 0<=3<=5}}
  (X::=(ANum 3))
  {{fun st => 0<=asnat (st X)<=5}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assert_implies.
  intros st H. assumption.
Qed.
(** [] *)

(* ####################################################### *)
(** *** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    property P:
[[[
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
]]]
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ####################################################### *) 
(** *** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:
[[[
        {{ P }} c1 {{ Q }} 
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
]]]
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.  
  apply (H2 st st'0); try assumption. Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule: the natural way to construct a Hoare-logic proof is
    to begin at the end of the program (with the final postcondition)
    and push postconditions backwards through commands until we reach
    the beginning. *)

(** Informally, a nice way of recording a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
[[
      {{ a = n }}
    X ::= a;
      {{ X = n }}      <---- decoration for Q
    SKIP
      {{ X = n }}
]]
*)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}} 
  (X ::= a; SKIP) 
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H.  subst.  reflexivity. Qed.

(** **** Exercise: 2 stars (hoare_asgn_example4) *)
(** Translate this decorated program into a formal proof:
[[
                   {{ True }} =>
                   {{ 1 = 1 }}
    X ::= 1;
                   {{ X = 1 }} =>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
]]
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2)) 
  {{fun st => asnat (st X) = 1 /\ asnat (st Y) = 2}}.
Proof.
  eapply hoare_seq.
  Case "right part of seq".
      apply hoare_asgn.
  Case "left part of seq".
      unfold assn_sub. simpl.
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      intros st H. unfold assn_sub. simpl. 
      split; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars (swap_exercise) *)
(** Write an Imp program [c] that swaps the values of [X] and [Y]
    and show (in Coq) that it satisfies the following
    specification:
[[
      {{X <= Y}} c {{Y <= X}}


      {{X <= Y}}
      Z::= X
      {{X <= Y /\ Z = X}}
      X::= Y
      {{X <= Y /\ Z = X /\ X = Y}}
      Y::= Z
      {{Y <= X /\ Y = Z /\ X = Y /\ Z = X}}
]]
*)

Example swap_exec:
  {{fun st=> asnat (st X)<= asnat (st Y)}}
  (Z::=AId X;X::=AId Y;Y::=AId Z)
  {{fun st=> asnat (st Y)<= asnat (st X)}}.
Proof.
  eapply hoare_seq.
  Case "right".
      eapply hoare_seq.
      SCase "right".
          apply hoare_asgn.
      SCase "left".
          apply hoare_asgn.
  Case "left".
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      intros st H.
      unfold assn_sub. simpl.
      assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (hoarestate1) *)
(** Explain why the following proposition can't be proven:
[[
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}} (X ::= (ANum 3); Y ::= a) 
         {{fun st => asnat (st Y) = n}}.
]]
*)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *) 
(** *** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
[[[
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
]]]
   However, this is rather weak. For example, using this rule,
   we cannot show that:
[[
     {{True}} 
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1 
     FI
     {{ X <= Y }}
]]
   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches.
   
   But, actually, we can say something more precise.  In the "then"
   branch, we know that the boolean expression [b] evaluates to
   [true], and in the "else" branch, we know it evaluates to [false].
   Making this information available in the premises of the lemma
   gives us more information to work with when reasoning about the
   behavior of [c1] and [c2] (i.e., the reasons why they establish the
   postcondtion [Q]).
[[[
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
]]]
*)

(** To interpret this rule formally, we need to do a little work.

    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression, which
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example : 
    {{fun st => True}} 
  IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
  FI
    {{fun st => asnat (st X) <= asnat (st Y)}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update, assert_implies. simpl. intros. 
    inversion H.
       symmetry in H1; apply beq_nat_eq in H1. 
       rewrite H1.  omega. 
  Case "Else". 
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update, assert_implies; simpl; intros. omega. 
Qed.

(* ####################################################### *)
(** *** Loops *)

(** Finally, we need a rule for reasoning about while loops.  Suppose
    we have a loop
[[
      WHILE b DO c END
]]
    and we want to find a pre-condition [P] and a post-condition
    [Q] such that
[[
      {{P}} WHILE b DO c END {{Q}} 
]]
    is a valid triple.  

    First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write
[[
      {{P}} WHILE b DO c END {{P}}.
]]
    But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
[[
      {{P}} WHILE b DO c END {{P /\ ~b}}
]]
    What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule:
[[[
                   {{P}} c {{P}}
        -----------------------------------  
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]]
    The proposition [P] is called an _invariant_.

    This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state.  This gives us a little more information to use in
    reasoning about [c] (showing that it establishes the invariant by
    the time it finishes).  This gives us the final version of the rule:
[[[
               {{P /\ b}} c {{P}}
        -----------------------------------  [hoare_while]
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]]
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on He, because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom.
  ceval_cases (induction He) Case; try (inversion Heqwcom); subst.
  
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false.  assumption.

  Case "E_WhileLoop".
    apply IHHe2.  reflexivity.
    apply (Hhoare st st'); try assumption.
      split. assumption. apply bexp_eval_true. assumption.  Qed.

Example while_example : 
    {{fun st => asnat (st X) <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => asnat (st X) = 3}}.
Proof.
  eapply hoare_consequence_post. 
  apply hoare_while. 
  eapply hoare_consequence_pre. 
  apply hoare_asgn. 
  unfold bassn, assn_sub, assert_implies. intros. 
    rewrite update_eq. simpl.
    inversion H as [_ H0].  simpl in H0. apply ble_nat_true in H0.  
    omega. 
  unfold bassn, assert_implies. intros. 
    inversion H as [Hle Hb]. simpl in Hb.
    remember (ble_nat (asnat (st X)) 2) as le.  destruct le. 
    apply ex_falso_quodlibet. apply Hb; reflexivity.  
    symmetry in Heqle. apply ble_nat_false in Heqle. omega. 
Qed.

(** We can also use the while rule to prove the following Hoare
    triple, which may seem surprising at first... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. apply I. 
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.  Qed.

(** Actually, this result shouldn't be surprising.  If we look back at
    the definition of [hoare_triple], we can see that it asserts
    something meaningful _only_ when the command terminates. *)

Print hoare_triple. 

(** If the command doesn't terminate, we can prove anything we like
    about the post-condition.  Here's a more direct proof of the same
    fact: *)

Theorem always_loop_hoare' : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.  
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra.  inversion contra. 
Qed.

(** Hoare rules that only talk about terminating commands are often
    said to describe a logic of "partial" correctness.  It is also
    possible to give Hoare rules for "total" correctness, which build
    in the fact that the commands terminate. *)

(* ####################################################### *)
(** *** Exercise: [REPEAT] *)

Module RepeatExercise.

(** **** Exercise: 4 stars (hoare_repeat) *)
(** In this exercise, we'll add a new constructor to our language of
    commands: [CRepeat].  You will write the evaluation rule for
    [repeat] and add a new hoare logic theorem to the language for
    programs involving it.
 
    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CRepeat" ].

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall b1 st c1,
      beval st b1 = true ->
      ceval st (REPEAT c1 UNTIL b1 END) st
  | E_RepeatLoop : forall st st' st'' b1 c1,
      beval st b1 = false ->
      ceval st c1 st' ->
      ceval st' (REPEAT c1 UNTIL b1 END) st'' ->
      ceval st (REPEAT c1 UNTIL b1 END) st''
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" 
  | Case_aux c "E_RepeatEnd"| Case_aux c "E_RepeatLoop"
].

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '||' st'" := (ceval st c1 st') 
                                 (at level 40, st at level 39).
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) 
                        : Prop :=
  forall st st', (c / st || st') -> P st -> Q st'.
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

(** Now state and prove a theorem, [hoare_repeat], that expresses an
     appropriate proof rule for [repeat] commands.  Use [hoare_while]
     as a model. *)

Lemma hoare_repeat : forall P b c,
  {{fun st => P st /\ ~(bassn b st)}} c {{P}} ->
  {{P}} REPEAT c UNTIL b END {{fun st => P st /\ bassn b st}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (REPEAT c UNTIL b END) as rcom.
  ceval_cases (induction He) Case; try (inversion Heqrcom); subst.

  Case "E_RepeatEnd".
    split. assumption. apply bexp_eval_true.  assumption.

  Case "E_RepeatLoop".
    apply IHHe2.  reflexivity.
    apply (Hhoare st st'); try assumption.
      split. assumption. apply bexp_eval_false. assumption.  Qed.

End RepeatExercise.
(** [] *)

(* ####################################################### *)
(** ** Exercise: [HAVOC] *)

(** **** Exercise: 3 stars (himp_hoare) *)

(** In this exercise, we will derive proof rules for the [HAVOC] command
    which we studied in the last chapter. First, we enclose this work
    in a separate module, and recall the syntax and big-step semantics
    of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "HAVOC" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st || st
  | E_Ass : forall (st : state) (a1 : aexp) (n : val) (X : id),
            aeval st a1 = n -> (X ::= a1) / st || update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st || st' -> c2 / st' || st'' -> (c1 ; c2) / st || st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st || st' -> (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
  | E_Havoc : forall (st : state) (X : id) (v : val),
              (HAVOC X) / st || update st X v

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Havoc" ].

(** The definition of Hoare triples is exactly as before. Unlike our notion
    of equivalence, which had subtle consequences with occassionally
    nonterminating commands (exercise [havoc_diverge]), this definition
    is still satisfactory. Convince yourself of this before proceeding. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c" :=          (hoare_triple P c (fun st => True)) 
                                  (at level 90) 
                                  : hoare_spec_scope.
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.

(** All the proof rules (except the one involving [HAVOC]) are identical
    to the ones proved earlier in this chapter. The exercise is to
    state (and prove) a Hoare proof rule for [HAVOC] commands. In a
    comment, explain why your rule is the right one.  Optionally, as
    in exercise [hoare_asgn_weakest], show that your precondition is
    the weakest precondition. *)

Theorem hoare_havoc: forall P id v,
  {{fun st=>P st}} 
  (HAVOC id)
  {{fun st=>P (update st id v)}}.
Proof.
  unfold hoare_triple.
  intros. 
  inversion H. subst.
admit. Qed.
End Himp.
(** [] *)

