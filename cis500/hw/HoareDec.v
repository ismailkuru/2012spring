(** * Hoare: Hoare Logic *)

(* $Date: 2012-03-15 18:29:29 -0400 (Thu, 15 Mar 2012) $ *)

Require Export Hoare.

(* ####################################################### *)
(** * Decorated Programs *)

(** The whole point of Hoare Logic is that it is compositional -- the
    structure of proofs exactly follows the structure of programs.
    This fact suggests that we we could record the essential ideas of
    a proof informally (leaving out some low-level calculational
    details) by decorating programs with appropriate assertions around
    each statement.  Such a _decorated program_ carries with it
    an (informal) proof of its own correctness.

   For example, here is a complete decorated program:
[[
      {{ True }} =>
      {{ x = x }}
    X ::= x; 
      {{ X = x }} => 
      {{ X = x /\ z = z }}
    Z ::= z;              
      {{ X = x /\ Z = z }} =>
      {{ Z - X = z - x }}
    WHILE X <> 0 DO
        {{ Z - X = z - x /\ X <> 0 }} =>
        {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;               
        {{ Z - (X - 1) = z - x }}
      X ::= X - 1 
        {{ Z - X = z - x }} 
    END;
      {{ Z - X = z - x /\ ~ (X <> 0) }} =>
      {{ Z = z - x }} =>
      {{ Z + 1 = z - x + 1 }}
    Z ::= Z + 1
      {{ Z = z - x + 1 }}
]]
*)

(** Concretely, a decorated program consists of the program text
    interleaved with assertions.  To check that a decorated program
    represents a valid proof, we check that each individual command is
    _locally_ consistent with its accompanying assertions in the
    following sense:

    - [SKIP] is locally consistent if its precondition and
      postcondition are the same
[[
          {{ P }} 
          SKIP
          {{ P }} 
]]
    - The sequential composition of commands [c1] and [c2] is locally
      consistent (with respect to assertions [P] and [R]) if [c1]
      is (with respect to [P] and [Q]) and [c2] is (with respect to
      [Q] and [R]):
[[
          {{ P }} 
          c1;
          {{ Q }} 
          c2
          {{ R }}
]]

    - An assignment is locally consistent if its precondition is
      the appropriate substitution of its postcondition:
[[
          {{ P where a is substituted for X }}  
          X ::= a  
          {{ P }}
]]
    - A conditional is locally consistent (with respect to assertions
      [P] and [Q]) if the assertions at the top of its "then" and
      "else" branches are exactly [P/\b] and [P/\~b] and if its "then"
      branch is locally consistent (with respect to [P/\b] and [Q])
      and its "else" branch is locally consistent (with respect to
      [P/\~b] and [Q]):
[[
          {{ P }} 
          IFB b THEN
            {{ P /\ b }} 
            c1 
            {{ Q }}
          ELSE
            {{ P /\ ~b }} 
            c2
            {{ Q }}
          FI
]]

    - A while loop is locally consistent if its postcondition is
      [P/\~b] (where [P] is its precondition) and if the pre- and
      postconditions of its body are exactly [P/\b] and [P]:
[[
          {{ P }} 
          WHILE b DO
            {{ P /\ b }} 
            c1 
            {{ P }}
          END
          {{ P /\ ~b }} 
]]

    - A pair of assertions separated by [=>] is locally consistent if
      the first implies the second (in all states):
[[
          {{ P }} =>
          {{ P' }} 
]]          
*)

(* ####################################################### *)
(** * Sample Hoare Logic Proofs *)

(* ####################################################### *)
(** ** Example: Slow Subtraction *)

(** Informally:
[[
      {{ X = x /\ Z = z }} =>
      {{ Z - X = z - x }}
    WHILE X <> 0 DO
        {{ Z - X = z - x /\ X <> 0 }} =>
        {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;
        {{ Z - (X - 1) = z - x }}
      X ::= X - 1
        {{ Z - X = z - x }} 
    END
      {{ Z - X = z - x /\ ~ (X <> 0) }} =>
      {{ Z = z - x }}
]]
*)

(** Formally: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= AMinus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition subtract_slowly_invariant x z := 
  fun st => minus (asnat (st Z)) (asnat (st X)) = minus z x.
  
Theorem subtract_slowly_correct : forall x z,
  {{fun st => asnat (st X) = x /\ asnat (st Z) = z}} 
  subtract_slowly 
  {{fun st => asnat (st Z) = minus z x}}.
Proof.
  (* Note that we do NOT unfold the definition of hoare_triple
     anywhere in this proof!  The goal is to use only the hoare
     rules.  Your proofs should do the same. *)

  intros x z. unfold subtract_slowly.
  (* First we need to transform the pre and postconditions so
     that hoare_while will apply.  In particular, the
     precondition should be the loop invariant. *)
  eapply hoare_consequence with (P' := subtract_slowly_invariant x z).
  apply hoare_while.

  Case "Loop body preserves invariant".
    (* Split up the two assignments with hoare_seq - using eapply 
       lets us solve the second one immediately with hoare_asgn *)
    eapply hoare_seq. apply hoare_asgn.
    (* Now for the first assignment, transform the precondition
       so we can use hoare_asgn *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Finally, we need to justify the implication generated by
       hoare_consequence_pre (this bit of reasoning is elided in the
       informal proof) *)
    unfold subtract_slowly_invariant, assn_sub, update, bassn. simpl.
    intros st [Inv GuardTrue].
    (* There are several ways to do the case analysis here...this 
       one is fairly general: *)
    remember (beq_nat (asnat (st X)) 0) as Q; destruct Q. 
     inversion GuardTrue.
     symmetry in HeqQ.  apply beq_nat_false in HeqQ. 
     omega. (* slow but effective! *)
  Case "Initial state satisfies invariant".
    (* This is the subgoal generated by the precondition part of our
       first use of hoare_consequence.  It's the first implication
       written in the decorated program (though we elided the actual
       proof there). *)
    unfold subtract_slowly_invariant.
    intros st [HX HZ]. omega.  
  Case "Invariant and negated guard imply postcondition".
   (* This is the subgoal generated by the postcondition part of
      out first use of hoare_consequence.  This implication is
      the one written after the while loop in the informal proof. *)
    intros st [Inv GuardFalse].
    unfold subtract_slowly_invariant in Inv.
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* Here's a slightly different alternative for the case analysis that
       works out well here (but is less general)... *)
    destruct (asnat (st X)). 
      omega. 
      apply ex_falso_quodlibet.   apply GuardFalse. reflexivity. 
    Qed.

(* ####################################################### *)
(** ** Exercise: Reduce to Zero *)

(** Here is a while loop that is so simple it needs no invariant: 
[[
          {{ True }}
        WHILE X <> 0 DO
            {{ True /\ X <> 0 }} =>
            {{ True }}
          X ::= X - 1
            {{ True }}
        END
          {{ True /\ X = 0 }} =>
          {{ X = 0 }}
]]
   Your job is to translate this proof to Coq.  It may help to look
   at the [slow_subtraction] proof for ideas.
*)

(** **** Exercise: 2 stars (reduce_to_zero_correct) *)
Definition reduce_to_zero : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct : 
  {{fun st => True}}
  reduce_to_zero
  {{fun st => asnat (st X) = 0}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** ** Exercise: Slow Addition *)

(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z. *)

Definition add_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= APlus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

(** **** Exercise: 3 stars (add_slowly_decoration) *)
(** Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (add_slowly_formal) *)
(** Now write down your specification of [add_slowly] formally, as a
    Coq [Hoare_triple], and prove it valid. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Example: Parity *)

(** Here's another, slightly trickier example.  Make sure you
    understand the decorated program completely.  Understanding
    all the details of the Coq proof is not required, though it
    is not actually very hard -- all the required ideas are
    already in the informal version. *)
(** 
[[
    {{ X = x }} =>
    {{ X = x /\ 0 = 0 }}
  Y ::= 0;
    {{ X = x /\ Y = 0 }} =>
    {{ (Y=0 <-> ev (x-X)) /\ X<=x }} 
  WHILE X <> 0 DO
      {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} =>
      {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }} 
    Y ::= 1 - Y;
      {{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }} 
    X ::= X - 1
      {{ Y=0 <-> ev (x-X) /\ X<=x }} 
  END
    {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} =>
    {{ Y=0 <-> ev x }}
]]
*)

Definition find_parity : com :=
  Y ::= (ANum 0);
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= AMinus (ANum 1) (AId Y);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition find_parity_invariant x := 
  fun st => 
       asnat (st X) <= x
    /\ (asnat (st Y) = 0 /\ ev (x - asnat (st X)) \/ asnat (st Y) = 1 /\ ~ev (x - asnat (st X))). 

(* It turns out that we'll need the following lemma... *)
Lemma not_ev_ev_S_gen: forall n,
  (~ ev n -> ev (S n)) /\
  (~ ev (S n) -> ev (S (S n))).
Proof.
  induction n as [| n'].
  Case "n = 0".
    split; intros H.
    SCase "->".
      apply ex_falso_quodlibet. apply H. apply ev_0.
    SCase "<-".
      apply ev_SS. apply ev_0.
  Case "n = S n'".
    inversion IHn' as [Hn HSn]. split; intros H.
    SCase "->".
      apply HSn. apply H.
    SCase "<-".
      apply ev_SS. apply Hn. intros contra. 
      apply H. apply ev_SS. apply contra.  Qed.

Lemma not_ev_ev_S : forall n,
  ~ ev n -> ev (S n).
Proof.
  intros n.
  destruct (not_ev_ev_S_gen n) as [H _].
  apply H.
Qed.

Theorem find_parity_correct : forall x,
  {{fun st => asnat (st X) = x}} 
  find_parity
  {{fun st => asnat (st Y) = 0 <-> ev x}}.
Proof.
  intros x. unfold find_parity.
  apply hoare_seq with (Q := find_parity_invariant x).
  eapply hoare_consequence.
  apply hoare_while with (P := find_parity_invariant x).
  Case "Loop body preserves invariant".
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st [[Inv1 Inv2] GuardTrue].
    unfold find_parity_invariant, bassn, assn_sub, aeval in *.
    rewrite update_eq.
    rewrite (update_neq Y X). 
    rewrite (update_neq X Y).
    rewrite update_eq.
    simpl in GuardTrue. destruct (asnat (st X)). 
      inversion GuardTrue. simpl.
    split. omega. 
    inversion Inv2 as [[H1 H2] | [H1 H2]]; rewrite H1;
                     [right|left]; (split; simpl; [omega |]).
    apply ev_not_ev_S in H2. 
    replace (S (x - S n)) with (x-n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
    apply not_ev_ev_S in H2.
    replace (S (x - S n)) with (x - n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
    reflexivity. reflexivity.
  Case "Precondition implies invariant".
    intros st H. assumption.
  Case "Invariant implies postcondition".
    unfold bassn, find_parity_invariant. simpl.
    intros st [[Inv1 Inv2] GuardFalse].
    destruct (asnat (st X)).
      split; intro.   
        inversion Inv2.  
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega. 
           assumption.
           inversion H0 as [H0' _]. rewrite H in H0'. inversion H0'. 
        inversion Inv2. 
           inversion H0. assumption. 
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega. 
           apply ex_falso_quodlibet. apply H1. assumption.
      apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
  Case "invariant established before loop".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H.
    unfold assn_sub, find_parity_invariant, update. simpl.
    subst. 
    split.
    omega. 
    replace (asnat (st X) - asnat (st X)) with 0 by omega. 
    left. split. reflexivity.
    apply ev_0.  Qed.

(** **** Exercise: 3 stars (wrong_find_parity_invariant) *)
(** A plausible first attempt at stating an invariant for [find_parity]
    is the following. *)

Definition find_parity_invariant' x := 
  fun st => 
    (asnat (st Y)) = 0 <-> ev (x - asnat (st X)). 

(** Why doesn't this work?  (Hint: Don't waste time trying to answer
    this exercise by attempting a formal proof and seeing where it
    goes wrong.  Just think about whether the loop body actually
    preserves the property.) *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *) 
(** ** Example: Finding Square Roots *)

Definition sqrt_loop : com :=
  WHILE BLe (AMult (APlus (ANum 1) (AId Z)) 
                   (APlus (ANum 1) (AId Z))) 
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
  END.

Definition sqrt_com : com :=
  Z ::= ANum 0;
  sqrt_loop.

Definition sqrt_spec (x : nat) : Assertion := 
  fun st => 
       ((asnat (st Z)) * (asnat (st Z))) <= x 
    /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x).

Definition sqrt_inv (x : nat) : Assertion :=
  fun st => 
       asnat (st X) = x
    /\ ((asnat (st Z)) * (asnat (st Z))) <= x.

Theorem random_fact_1 : forall st,
     (S (asnat (st Z))) * (S (asnat (st Z))) <= asnat (st X) ->
     bassn (BLe (AMult (APlus (ANum 1) (AId Z)) 
                       (APlus (ANum 1) (AId Z))) 
                (AId X)) st.
Proof.
  intros st Hle.  unfold bassn. simpl.
  destruct (asnat (st X)) as [|x'].
  Case "asnat (st X) = 0".
    inversion Hle.
  Case "asnat (st X) = S x'".
    simpl in Hle. apply le_S_n in Hle.
    remember (ble_nat (plus (asnat (st Z)) 
                      ((asnat (st Z)) * (S (asnat (st Z))))) x')
      as ble.
    destruct ble. reflexivity. 
    symmetry in Heqble. apply ble_nat_false in Heqble.
    unfold not in Heqble. apply Heqble in Hle. inversion Hle.
Qed.

Theorem random_fact_2 : forall st,
     bassn (BLe (AMult (APlus (ANum 1) (AId Z)) 
                       (APlus (ANum 1) (AId Z))) 
                (AId X)) st ->
       asnat (aeval st (APlus (ANum 1) (AId Z))) 
     * asnat (aeval st (APlus (ANum 1) (AId Z))) 
     <= asnat (st X).
Proof.
  intros st Hble. unfold bassn in Hble. simpl in *.
  destruct (asnat (st X)) as [| x'].
  Case "asnat (st X) = 0".
    inversion Hble.
  Case "asnat (st X) = S x'".
    apply ble_nat_true in Hble. omega. Qed.

Theorem sqrt_com_correct : forall x,
  {{fun st => True}} (X ::= ANum x; sqrt_com) {{sqrt_spec x}}.
Proof.
  intros x.
  apply hoare_seq with (Q := fun st => asnat (st X) = x).
  Case "sqrt_com".
    unfold sqrt_com.
    apply hoare_seq with (Q := fun st => asnat (st X) = x 
                                      /\ asnat (st Z) = 0).

    SCase "sqrt_loop".
      unfold sqrt_loop.
      eapply hoare_consequence.
      apply hoare_while with (P := sqrt_inv x).

      SSCase "loop preserves invariant".
        eapply hoare_consequence_pre.
        apply hoare_asgn. intros st H.
        unfold assn_sub. unfold sqrt_inv in *.
        inversion H as [[HX HZ] HP]. split.
        SSSCase "X is preserved".
          rewrite update_neq; try assumption; try reflexivity.
        SSSCase "Z is updated correctly".
          rewrite (update_eq (aeval st (APlus (ANum 1) (AId Z))) Z st).
          subst. apply random_fact_2. assumption.

      SSCase "invariant is true initially".
        intros st H. inversion H as [HX HZ]. 
        unfold sqrt_inv. split. assumption. 
        rewrite HZ. simpl. omega.

      SSCase "after loop, spec is satisfied".
        intros st H. unfold sqrt_spec.
        inversion H as [HX HP].
        unfold sqrt_inv in HX.  inversion HX as [HX' Harith].
        split. assumption. 
        intros contra. apply HP. clear HP. 
        simpl. simpl in contra.
        apply random_fact_1. subst x. assumption.

    SCase "Z set to 0".
      eapply hoare_consequence_pre. apply hoare_asgn. 
      intros st HX.
      unfold assn_sub. split.
      rewrite update_neq. assumption. reflexivity.
      rewrite update_eq. reflexivity.

  Case "assignment of X".
    eapply hoare_consequence_pre. apply hoare_asgn. 
    intros st H.
    unfold assn_sub. rewrite update_eq. reflexivity. Qed.

(** **** Exercise: 3 stars, optional (sqrt_informal) *)
(** Write a decorated program corresponding to the above
    correctness proof. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Exercise: Factorial *)

Module Factorial.

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Recall the factorial Imp program: *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= (AId X);
  Y ::= ANum 1;
  fact_loop.

(** **** Exercise: 3 stars, optional (fact_informal) *)
(** Decorate the [fact_com] program to show that it satisfies the
    specification given by the pre and postconditions below.  Just as
    we have done above, you may elide the algebraic reasoning about
    arithmetic, the less-than relation, etc., that is (formally)
    required by the rule of consequence:

(* FILL IN HERE *)
[[
    {{ X = x }}
  Z ::= X;
  Y ::= 1;
  WHILE Z <> 0 DO
    Y ::= Y * Z;
    Z ::= Z - 1
  END
    {{ Y = real_fact x }}
]]
*)
(** [] *)


(** **** Exercise: 4 stars, optional (fact_formal) *)
(** Prove formally that fact_com satisfies this specification,
    using your informal proof as a guide.  You may want to state
    the loop invariant separately (as we did in the examples). *)

Theorem fact_com_correct : forall x,
  {{fun st => asnat (st X) = x}} fact_com
  {{fun st => asnat (st Y) = real_fact x}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Factorial.

(* ####################################################### *)
(** ** Reasoning About Programs with Lists *)

(** **** Exercise: 3 stars (list_sum) *)
(** Here is a direct definition of the sum of the elements of a list,
    and an Imp program that computes the sum. *)

Definition sum l := fold_right plus 0 l.

Definition sum_program :=
  Y ::= ANum 0;
  WHILE (BIsCons (AId X)) DO 
    Y ::= APlus (AId Y) (AHead (AId X)) ;
    X ::= ATail (AId X)
  END. 

(** Provide an _informal_ proof of the following specification of
    [sum_program] in the form of a decorated version of the
    program. *)

Definition sum_program_spec := forall l,
  {{ fun st => aslist (st X) = l }}
  sum_program
  {{ fun st => asnat (st Y) = sum l }}.

(* FILL IN HERE *)
(** [] **)

(** Next, let's look at a _formal_ Hoare Logic proof for a program
    that deals with lists.  We will verify the following program,
    which checks if the number [Y] occurs in the list [X], and if so sets
    [Z] to [1].
*)

Definition list_member :=
  WHILE BIsCons (AId X) DO
    IFB (BEq (AId Y) (AHead (AId X))) THEN
      Z ::= (ANum 1) 
    ELSE
      SKIP
    FI; 
    X ::= ATail (AId X)
  END.

Definition list_member_spec := forall l n,
  {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  list_member
  {{ fun st => st Z = VNat 1 <-> appears_in n l }}.

(** The proof we will use, written informally, looks as follows:
[[
    {{ X = l /\ Y = n /\ Z = 0 }} =>
    {{ Y = n /\ exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p) }}
  WHILE (BIsCons X) 
  DO
      {{ Y = n /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
               /\ (BIsCons X) }}
    IFB (Y == head X) THEN
        {{ Y = n 
           /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)) 
           /\ (BIsCons X)
           /\ Y == AHead X }} =>
        {{ Y = n /\ (exists p, p ++ tail X = l 
                    /\ (1 = 1 <-> appears_in n p)) }}
      Z ::= 1
        {{ Y = n /\ (exists p, p ++ tail X = l 
        /\ (Z = 1 <-> appears_in n p)) }}
    ELSE
        {{ Y = n 
           /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)) 
           /\ (BIsCons X)
           /\ ~ (Y == head X) }} =>
        {{ Y = n 
           /\ (exists p, p ++ tail X = l /\ (Z = 1 <-> appears_in n p)) }}
      SKIP
        {{ Y = n 
           /\ (exists p, p ++ tail X = l /\ (Z = 1 <-> appears_in n p)) }}
    FI;
    X ::= ATail X
        {{ Y = n   
           /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)) }}
  END
     {{ Y = n   
        /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)) 
        /\ ~ (BIsCons X) }} => 
     {{ Z = 1 <-> appears_in n l }}
]]

  The only interesting part of the proof is the choice of loop invariant:
[[
      exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)
]]
  This states that at each iteration of the loop, the original list
  [l] is equal to the append of the current value of [X] and some
  other list [p] which is not the value of any variable in the
  program, but keeps track of enough information from the original
  state to make the proof go through. (Such a [p] is sometimes called
  a "ghost variable").

  In order to show that such a list [p] exists, in each iteration we
  add the head of [X] to the _end_ of [p]. This needs the function
  [snoc], from Poly.v. *)

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) := 
  match l with
  | nil      =>  [ v ]
  | cons h t => h :: (snoc t v)
  end.

Lemma snoc_equation : forall (A : Type) (h:A) (x y : list A),
  snoc x h ++ y = x ++ h :: y.     
Proof.
  intros A h x y.
  induction x. 
    Case "x = []". reflexivity.
    Case "x = cons". simpl. rewrite IHx. reflexivity.
Qed.

(** The main proof uses various lemmas. *)

Lemma appears_in_snoc1 : forall a l,
  appears_in a (snoc l a).
Proof.
  induction l.
    Case "l = []". apply ai_here.
    Case "l = cons". simpl. apply ai_later. apply IHl.
Qed.

Lemma appears_in_snoc2 : forall a b l,
  appears_in a l ->
  appears_in a (snoc l b).
Proof.
  induction l; intros H; inversion H; subst; simpl.
    Case "l = []". apply ai_here.
    Case "l = cons". apply ai_later. apply IHl. assumption.
Qed.

Lemma appears_in_snoc3 : forall a b l,
   appears_in a (snoc l b) ->
   (appears_in a l \/ a = b).
Proof.
   induction l; intros H.
   Case "l = []". inversion H.
     SCase "ai_here". right. reflexivity.
     SCase "ai_later". left. assumption.
   Case "l = cons". inversion H; subst.
     SCase "ai_here". left. apply ai_here.
     SCase "ai_later". destruct (IHl H1).
       left. apply ai_later. assumption.
       right. assumption.
Qed.

Lemma append_singleton_equation : forall (x : nat) l l',
  (l ++ [x]) ++ l' = l ++ x :: l'.
Proof.
  intros x l l'.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma append_nil : forall (A : Type) (l : list A),
  l ++ [] = l.
Proof.
  induction l. 
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma beq_true__eq : forall n n',
  beq_nat n n' = true ->
  n = n'.
Proof.
  induction n; destruct n'.
  Case "n = 0, n' = 0".     reflexivity.
  Case "n = 0, n' = S _".   simpl. intros H. inversion H.
  Case "n = S, n' = 0".     simpl. intros H. inversion H.
  Case "n = S, n' = S".     simpl. intros H.
                            rewrite (IHn n' H). reflexivity.
Qed.

Lemma beq_nat_refl : forall n,
  beq_nat n n = true.
Proof.
  induction n. 
    reflexivity.
    simpl. assumption.
Qed.

Theorem list_member_correct : forall l n,
  {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  list_member
  {{ fun st => st Z = VNat 1 <-> appears_in n l }}.
Proof.
  intros l n.
  eapply hoare_consequence.
  apply hoare_while with (P := fun st =>
     st Y = VNat n 
     /\ exists p, p ++ aslist (st X) = l 
                  /\ (st Z = VNat 1 <-> appears_in n p)).
    (* The loop body preserves the invariant: *)
    eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_if.
    Case "If taken".
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      unfold assn_sub. split.
      (* (st Y) is still n *)
        rewrite update_neq; try reflexivity.  
        rewrite update_neq; try reflexivity.
        assumption.
      (* and the interesting part of the invariant is preserved: *)
        (* X has to be a cons *)
        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9. 
          rewrite <- Heqx in H9. inversion H9.
         
          exists (snoc p h).
          rewrite update_eq.
          unfold aeval. rewrite update_neq; try reflexivity. 
          rewrite <- Heqx.
          split.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try reflexivity.
            rewrite update_eq. 
            split. 
              simpl.
              unfold bassn in H10. unfold beval in H10.
              unfold aeval in H10. rewrite H1 in H10. 
              rewrite <- Heqx in H10. simpl in H10.
              rewrite (beq_true__eq _ _ H10).
              intros. apply appears_in_snoc1.
                
              intros. reflexivity.
    Case "If not taken".
      eapply hoare_consequence_pre. apply hoare_skip.
      unfold assn_sub.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      split.
      (* (st Y) is still n *)
        rewrite update_neq; try reflexivity.  
        assumption.
      (* and the interesting part of the invariant is preserved: *)
        (* X has to be a cons *)
        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9. 
          rewrite <- Heqx in H9. inversion H9.

          exists (snoc p h).
          split.
            rewrite update_eq.
            unfold aeval. rewrite <- Heqx.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try reflexivity.
            split.
              intros. apply appears_in_snoc2. apply H3. assumption.

              intros.  destruct (appears_in_snoc3 _ _ _ H).
              SCase "later".
                inversion H3 as [_ H3'].
                apply H3'. assumption.
              SCase "here (absurd)".
                subst.
                unfold bassn in H10. unfold beval in H10. unfold aeval in H10.
                rewrite <- Heqx in H10. rewrite H1 in H10.
                simpl in H10. rewrite beq_nat_refl in H10.
                apply ex_falso_quodlibet. apply H10. reflexivity.
  (* The invariant holds at the start of the loop: *)
  intros st [H1 [H2 H3]]. 
  rewrite H1. rewrite H2. rewrite H3.
  split. 
    reflexivity.
    exists []. split.
      reflexivity.
      split; intros H; inversion H.
  (* At the end of the loop the invariant implies the right thing. *)
  simpl.   intros st [[H1 [p [H2 H3]]] H5].
  (* x must be [] *)
  unfold bassn in H5. unfold beval in H5. unfold aeval in H5.
  destruct (aslist (st X)) as [|h x'].
    rewrite append_nil in H2.
    rewrite <- H2.
    assumption.

    apply ex_falso_quodlibet. apply H5. reflexivity.
Qed.

(** **** Exercise: 4 stars, optional (list_reverse) *)
(** Recall the function [rev] from Poly.v, for reversing lists. *)

Fixpoint rev {X:Type} (l:list X) : list X := 
  match l with
  | nil      => []
  | cons h t => snoc (rev t) h
  end. 

(** Write an Imp program [list_reverse_program] that reverses
    lists. Formally prove that it satisfies the following
    specification:
[[
    forall l : list nat,
      {{ X =  l /\ Y = nil }}
      list_reverse_program
      {{ Y = rev l }}.
]]
    You may find the lemmas [append_nil] and [rev_equation] useful.
*)

Lemma rev_equation : forall (A : Type) (h : A) (x y : list A),
  rev (h :: x) ++ y = rev x ++ h :: y.
Proof.
  intros. simpl. apply snoc_equation.
Qed.

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** * Formalizing Decorated Programs *)

(** The informal conventions for decorated programs amount to a way of
    displaying Hoare triples in which commands are annotated with
    enough embedded assertions that checking the validity of the
    triple is reduced to simple algebraic calculations showing that
    some assertions were stronger than others.

    In this section, we show that this informal presentation style can
    actually be made completely formal.  *)

(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of commands that includes embedded assertions.  We call the
    new commands _decorated commands_, or [dcom]s. *)

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom -> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Asgn"
  | Case_aux c "If" | Case_aux c "While"
  | Case_aux c "Pre" | Case_aux c "Post" ].

Notation "'SKIP' {{ P }}" 
      := (DCSkip P) 
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}" 
      := (DCAsgn l a P) 
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}" 
      := (DCWhile b Pbody d Ppost) 
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI'" 
      := (DCIf b P d P' d') 
      (at level 80, right associativity)  : dcom_scope.
Notation "'=>' {{ P }} d" 
      := (DCPre P d) 
      (at level 90, right associativity)  : dcom_scope.
Notation "{{ P }} d" 
      := (DCPre P d) 
      (at level 90)  : dcom_scope.
Notation "d '=>' {{ P }}" 
      := (DCPost d P) 
      (at level 91, right associativity)  : dcom_scope.
Notation " d ; d' " 
      := (DCSeq d d') 
      (at level 80, right associativity)  : dcom_scope.

Delimit Scope dcom_scope with dcom.

(** To avoid clashing with the existing [Notation] definitions
    for ordinary [com]mands, we introduce these notations in a special
    scope called [dcom_scope], and we wrap examples with the
    declaration [% dcom] to signal that we want the notations to be
    interpreted in this scope.  

    Careful readers will note that we've defined two notations for the
    [DCPre] constructor, one with and one without a [=>].  The
    "without" version is intended to be used to supply the initial
    precondition at the very top of the program. *)

Example dec_while : dcom := (
    {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0))) 
  DO
       {{ fun st => ~(asnat (st X) = 0) }}
      X ::= (AMinus (AId X) (ANum 1)) 
       {{ fun _ => True }}
  END
    {{ fun st => asnat (st X) = 0 }}
) % dcom.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _          => SKIP
  | DCSeq d1 d2       => (extract d1 ; extract d2) 
  | DCAsgn X a _      => X ::= a
  | DCIf b _ d1 _ d2  => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _   => WHILE b DO extract d END
  | DCPre _ d         => extract d
  | DCPost d _        => extract d
  end.

(** The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [SKIP;SKIP] would have to
    be annotated as
[[
        {{P}} ({{P}} SKIP {{P}}) ; ({{P}} SKIP {{P}}) {{P}},
]]
    with pre- and post-conditions on each [SKIP], plus identical pre-
    and post-conditions on the semicolon!  

    Instead, the rule we've followed is this:

       - The _post_-condition expected by each [dcom] [d] is embedded in [d]

       - The _pre_-condition is supplied by the context. *)

(** In other words, the invariant of the representation is that a
    [dcom] [d] together with a precondition [P] determines a Hoare
    triple [{{P}} (extract d) {{post d}}], where [post] is defined as
    follows: *)

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn X a Q            => Q
  | DCIf  _ _ d1 _ d2       => post d1  
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

(** We can define a similar function that extracts the "initial
    precondition" from a decorated program. *)

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => fun st => True
  | DCSeq c1 c2             => pre c1
  | DCAsgn X a Q            => fun st => True
  | DCIf  _ _ t _ e         => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c               => P
  | DCPost c Q              => pre c
  end.

(** This function is not doing anything sophisticated like calculating
    a weakest precondition; it just recursively searches for an
    explicit annotation at the very beginning of the program,
    returning default answers for programs that lack an explicit
    precondition (like a bare assignment or [SKIP]).  

    Using [pre] and [post], and assuming that we adopt the convention
    of always supplying an explicit precondition annotation at the
    very beginning of our decorated programs, we can express what it
    means for a decorated program to be correct as follows: *)

Definition dec_correct (d:dcom) := 
  {{pre d}} (extract d) {{post d}}.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified (by some process looking
    at the decorated program) to see that the decorations are
    logically consistent and thus add up to a proof of correctness. *)

(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a [dcom] [d] together
    with a precondition [P] and returns a _proposition_ that, if it
    can be proved, implies that the triple [{{P}} (extract d) {{post d}}]
    is valid.  It does this by walking over [d] and generating a big
    conjunction including all the "local checks" that we listed when
    we described the informal rules for decorated programs.
    (Strictly speaking, we need to massage the informal rules a little
    bit to add some uses of the rule of consequence, but the
    correspondence should be clear.) *)

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q          => 
      (P ~~> Q)
  | DCSeq d1 d2      => 
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q      => 
      (P ~~> assn_sub X a Q)
  | DCIf b P1 t P2 e  => 
      ((fun st => P st /\ bassn b st) ~~> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ~~> P2)
      /\ (post t = post e)
      /\ verification_conditions P1 t
      /\ verification_conditions P2 e
  | DCWhile b Pbody d Ppost      => 
      (* post d is the loop invariant and the initial precondition *)
      (P ~~> post d)  
      /\ ((fun st => post d st /\ bassn b st) <~~> Pbody)  
      /\ ((fun st => post d st /\ ~(bassn b st)) <~~> Ppost)  
      /\ verification_conditions (fun st => post d st /\ bassn b st) d
  | DCPre P' d         => 
      (P ~~> P') /\ verification_conditions P' d
  | DCPost d Q        => 
      verification_conditions P d /\ (post d ~~> Q)
  end.

(** And now, the key theorem, which captures the claim that the
    [verification_conditions] function does its job correctly.  Not
    surprisingly, we need all of the Hoare Logic rules in the
    proof. *)
(** We have used _in_ variants of several tactics before to
    apply them to values in the context rather than the goal. An
    extension of this idea is the syntax [tactic in *], which applies
    [tactic] in the goal and every hypothesis in the context.  We most
    commonly use this facility in conjunction with the [simpl] tactic,
    as below. *)

Theorem verification_correct : forall d P, 
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq". 
    inversion H as [H1 H2]. clear H. 
    eapply hoare_seq. 
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Asgn". 
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If". 
    inversion H as [HPre1 [HPre2 [HQeq [HThen HElse]]]]; clear H.
    apply hoare_if.
      eapply hoare_consequence_pre. apply IHd1. apply HThen. assumption.     
      simpl. rewrite HQeq.
      eapply hoare_consequence_pre. apply IHd2. apply HElse. assumption.
  Case "While".
    rename a into Pbody. rename a0 into Ppost.
    inversion H as [Hpre [Hbody [Hpost Hd]]]; clear H. 
    eapply hoare_consequence.
    apply hoare_while with (P := post d). 
      apply IHd. apply Hd. 
      assumption. apply Hpost.
  Case "Pre".
    inversion H as [HP Hd]; clear H. 
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

(** ** Examples *)

(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)

Eval simpl in (verification_conditions (fun st => True) dec_while).
(* ====>
    ((fun _ : state => True) ~~> (fun _ : state => True)) /\
    ((fun _ : state => True) ~~> (fun _ : state => True)) /\
    ((fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) 
     <~~> (fun st : state => asnat (st X) <> 0)) /\
    ((fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st) 
     <~~> (fun st : state => asnat (st X) = 0)) /\
    (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st) 
     ~~> assn_sub X (AMinus (AId X) (ANum 1)) (fun _ : state => True) *)

(** We can certainly work with them using just the tactics we have so
    far, but we can make things much smoother with a bit of
    automation.  We first define a custom [verify] tactic that applies
    splitting repeatedly to turn all the conjunctions into separate
    subgoals and then uses [omega] and [eauto] (a handy
    general-purpose automation tactic that we'll discuss in detail
    later) to deal with as many of them as possible. *)

Tactic Notation "verify" :=
  try apply verification_correct; 
  repeat split;
  simpl; unfold assert_implies; 
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; simpl in *;
  intros; 
  repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  try eauto; try omega.

(** What's left after [verify] does its thing is "just the interesting
    parts" of checking that the decorations are correct.  For example: *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify; destruct (asnat (st X)). 
    inversion H0.
    unfold not. intros. inversion H1.
    apply ex_falso_quodlibet. apply H. reflexivity.
    reflexivity.
    reflexivity.
    apply ex_falso_quodlibet. apply H0. reflexivity.
    unfold not. intros. inversion H0.
    inversion H.
Qed.

(** Another example (formalizing a decorated program we've seen
    before): *)

Example subtract_slowly_dec (x:nat) (z:nat) : dcom := (
    {{ fun st => asnat (st X) = x /\ asnat (st Z) = z }}
  WHILE BNot (BEq (AId X) (ANum 0))
  DO   {{ fun st => asnat (st Z) - asnat (st X) = z - x
                 /\ bassn (BNot (BEq (AId X) (ANum 0))) st }}
     Z ::= AMinus (AId Z) (ANum 1)
       {{ fun st => asnat (st Z) - (asnat (st X) - 1) = z - x }} ;
     X ::= AMinus (AId X) (ANum 1) 
       {{ fun st => asnat (st Z) - asnat (st X) = z - x }}
  END
    {{ fun st =>   asnat (st Z) 
                 - asnat (st X) 
                 = z - x 
              /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st }}
    =>
    {{ fun st => asnat (st Z) = z - x }}
) % dcom.

Theorem subtract_slowly_dec_correct : forall x z, 
  dec_correct (subtract_slowly_dec x z).
Proof.
  intros. verify.
    rewrite <- H. 
    assert (H1: update st Z (VNat (asnat (st Z) - 1)) X = st X).
      apply update_neq. reflexivity.
    rewrite -> H1. destruct (asnat (st X)) as [| X']. 
      inversion H0. simpl. rewrite <- minus_n_O. omega.
    destruct (asnat (st X)).
      omega.
      apply ex_falso_quodlibet. apply H0. reflexivity.
Qed.

(** **** Exercise: 3 stars (slow_assignment_dec) *)

(** A roundabout way of assigning a number currently stored in [X] to
   the variable [Y] is to start [Y] at [0], then decrement [X] until it
   hits [0], incrementing [Y] at each step.

   Here is an informal decorated program that implements this idea
   given a parameter [x]: *)

(**
[[
      {{ True }}
    X ::= x
      {{ X = x }} ;
    Y ::= 0
      {{ X = x /\ Y = 0 }} ;
    WHILE X <> 0 DO
        {{ X + Y = x /\ X > 0 }}
      X ::= X - 1
        {{ Y + X + 1 = x }} ;
      Y ::= Y + 1
        {{ Y + X = x }}
    END
      {{ Y = x /\ X = 0 }}
]]
*)

(** Write a corresponding function that returns a value of type [dcom]
    and prove it correct. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, optional (factorial_dec)  *)
(** Remember the factorial function we worked with before: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Following the pattern of [subtract_slowly_dec], write a decorated
    Imp program that implements the factorial function, and prove it
    correct. *)

(* FILL IN HERE *)
(** [] *)

(** Finally, for a bigger example, let's redo the proof of
    [list_member_correct] from above using our new tools.
    
    Notice that the [verify] tactic leaves subgoals for each use of
    [hoare_consequence] -- that is, for each [=>] that occurs in the
    decorated program. Each of these implications relies on a fact
    about lists, for example that [l ++ [] = l]. In other words, the
    Hoare logic infrastructure has taken care of the boilerplate
    reasoning about the execution of imperative programs, while the
    user has to prove lemmas that are specific to the problem
    domain (e.g. lists or numbers). *)

Definition list_member_dec (n : nat) (l : list nat) : dcom := (
    {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  WHILE BIsCons (AId X)
  DO {{ fun st => st Y = VNat n 
               /\ (exists p, p ++ aslist (st X) = l 
               /\ (st Z = VNat 1 <-> appears_in n p))
               /\ bassn (BIsCons (AId X)) st }}
    IFB (BEq (AId Y) (AHead (AId X))) THEN
        {{ fun st =>
          ((st Y = VNat n 
            /\ (exists p, p ++ aslist (st X) = l 
                /\ (st Z = VNat 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st => 
            st Y = VNat n 
            /\ (exists p, p ++ tail (aslist (st X)) = l 
                 /\ (VNat 1 = VNat 1 <-> appears_in n p)) }}
      Z ::= ANum 1
        {{ fun st => st Y = VNat n 
             /\ (exists p, p ++ tail (aslist (st X)) = l 
                  /\ (st Z = VNat 1 <-> appears_in n p)) }}
   ELSE
        {{ fun st =>
          ((st Y = VNat n 
            /\ (exists p, p ++ aslist (st X) = l 
                  /\ (st Z = VNat 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ ~bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st => 
          st Y = VNat n 
          /\ (exists p, p ++ tail (aslist (st X)) = l 
               /\ (st Z = VNat 1 <-> appears_in n p)) }}
      SKIP
        {{ fun st => st Y = VNat n 
            /\ (exists p, p ++ tail (aslist (st X)) = l 
                 /\ (st Z = VNat 1 <-> appears_in n p)) }}
   FI ;
   X ::= (ATail (AId X))
     {{ fun st  =>
         st Y = VNat n /\
         (exists p : list nat, p ++ aslist (st X) = l 
           /\ (st Z = VNat 1 <-> appears_in n p)) }}
  END
   {{ fun st =>
     (st Y = VNat n 
       /\ (exists p, p ++ aslist (st X) = l 
            /\ (st Z = VNat 1 <-> appears_in n p)))
     /\ ~bassn (BIsCons (AId X)) st }}
   =>
   {{ fun st => st Z = VNat 1 <-> appears_in n l }}
) %dcom.

Theorem list_member_correct' : forall n l,
  dec_correct (list_member_dec n l).
Proof.
  intros n l.
  verify.
  Case "The loop precondition holds.".
    exists []. simpl. split.
      rewrite H. reflexivity.
      rewrite H1. split; inversion 1.
  Case "IF taken".
    destruct H2 as  [p [H3 H4]].   
    (* We know X is non-nil. *)
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      simpl. split.
         rewrite snoc_equation. assumption.
         split.
           rewrite H in H0.
           simpl in H0.
           rewrite (beq_true__eq _ _ H0).
           intros. apply appears_in_snoc1.
           intros. reflexivity.
  Case "If not taken".
    destruct H2 as [p [H3 H4]].
    (* We know X is non-nil. *)
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      split.
        rewrite snoc_equation. assumption.
        split.
          intros. apply appears_in_snoc2. apply H4. assumption.
          intros Hai.  destruct (appears_in_snoc3 _ _ _ Hai).
          SCase "later". apply H4. assumption.
          SCase "here (absurd)".
            subst.
            simpl in H0. rewrite H in H0. rewrite beq_nat_refl in H0.
            apply ex_falso_quodlibet. apply H0. reflexivity.
  Case "Loop postcondition implies desired conclusion (->)".
    destruct H2 as [p [H3 H4]].
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
  Case "loop postcondition implies desired conclusion (<-)".
    destruct H2 as [p [H3 H4]]. 
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
Qed.


