(* Throughout the entirety of this midterm, you are allowed to
   use any tactic we've learned in class, including auto, eauto
   and lia.
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.



(** Question 1. 

Write an Imp.v program that will compute the minimum of two numbers.
Assume the numbers are initially in X and Y, and Z should hold
the minimum at the end.

*)
Module HoareTest.
From PLF Require Import Imp.
From PLF Require Import Hoare.

Definition minimum_command : com :=
<{ 
    if (X <= Y) 
      then (Z := X)
      else (Z := Y)
    end
}>.

(**

Question 2: Write a statement using a Hoare triple that is true if,
and only if, your minimum_command correctly computes into Z the
minimum of X and Y.

Question 3: Prove that hoare triple is held.

*)

Theorem minimum_command_correct :
  forall (x y: nat), {{ X = x /\ Y = y }}
    minimum_command
  {{ Z = min x y }}.
Proof.
intros x y.
apply hoare_if.
- eapply hoare_consequence_pre.
  + apply hoare_asgn.
  + assn_auto''.
- eapply hoare_consequence_pre.
  + apply hoare_asgn.
  + assn_auto''.
Qed.

End HoareTest.


Module TME.
From PLF Require Import Types.

Import TM.


(** Throughout class, we used types to ensure evaluation does
    not get stuck. Another way to formalize getting stuck is
    evaluation to an "error state". Let's formalize terms with
    errors: tme
*)

Inductive tme : Type :=
  | etru : tme
  | efls : tme
  | eite : tme -> tme -> tme -> tme
  | ezro : tme
  | escc : tme -> tme
  | eprd : tme -> tme
  | eiszro : tme -> tme
  | eerror : tme.

(** tme align exactly with terms. There just is an additional eerror term
*)


(** _evalues_ are [etru, efls], and numeric values... *)
Inductive ebvalue : tme -> Prop :=
  | ebv_True : ebvalue etru
  | ebv_false : ebvalue efls.

Hint Constructors ebvalue : core.

Inductive envalue : tme -> Prop :=
  | env_0 : envalue ezro
  | env_succ : forall t, envalue t -> envalue (escc t).

Hint Constructors envalue : core.

Definition evalue (t : tme) := ebvalue t \/ envalue t.

(** Note that the notation for stepping in this tme language
    is ~~> not --> (uses tilde instead of hyphen) *)

(**
    The rules align on well-typed terms, but when things go wrong
    rather than let the terms get stuck, we let them evaluate to
    an "eerror" value.

    The only new rules are:


                         numeric value v
                   -------------------------------                   (EST_ITENValue)
                      eite v t1 t2 ~~> eerror


                   -------------------------------                  (EST_ITEError)
                   if eerror then t1 else t2 ~~> eerror


                         eboolean value v
                         --------------------                          (EST_SCCBValue)
                         escc v ~~> eerror


                         --------------------                          (EST_SCCError)
                         escc eerror ~~> eerror


                         eboolean value v
                         --------------------                          (EST_PRDBValue)
                         eprd v ~~> eerror


                         --------------------                          (EST_PRDError)
                         eprd eerror ~~> eerror


                         eboolean value v
                         --------------------                          (EST_IsZeroBValue)
                         eiszro v ~~> eerror


                         --------------------                          (EST_IsZeroError)
                         eiszro eerror ~~> eerror

*)

Reserved Notation "t '~~>' t'" (at level 40).

Inductive estep : tme -> tme -> Prop :=
  | EST_IfTrue : forall t1 t2,
      eite etru t1 t2 ~~> t1
  | EST_IfFalse : forall t1 t2,
      eite efls t1 t2 ~~> t2
  | EST_If : forall c c' t2 t3,
      c ~~> c' ->
      eite c t2 t3 ~~> eite c' t2 t3
  | EST_Succ : forall t1 t1',
      t1 ~~> t1' ->
      escc t1 ~~> escc t1'
  | EST_Pred0 :
      eprd ezro ~~> ezro
  | EST_PredSucc : forall v,
      envalue v ->
      eprd (escc v) ~~> v
  | EST_Pred : forall t1 t1',
      t1 ~~> t1' ->
      eprd t1 ~~> eprd t1'
  | EST_Iszero0 :
      eiszro ezro ~~> etru
  | EST_IszeroSucc : forall v,
       envalue v ->
      eiszro (escc v) ~~> efls
  | EST_Iszero : forall t1 t1',
      t1 ~~> t1' ->
      eiszro t1 ~~> eiszro t1'
  | EST_ITENValue : forall v t1 t2,
      envalue v ->
      eite v t1 t2 ~~> eerror
  | EST_ITEError : forall t1 t2, eite eerror t1 t2 ~~> eerror
  | EST_SCCBValue : forall v,
      ebvalue v ->
      escc v ~~> eerror
  | EST_SCCError : escc eerror ~~> eerror
  | EST_PRDBValue : forall v,
      ebvalue v ->
      eprd v ~~> eerror
  | EST_PRDError : eprd eerror ~~> eerror
  | EST_IsZeroBValue : forall v,
      ebvalue v ->
      eiszro v ~~> eerror
  | EST_IsZeroError : eiszro eerror ~~> eerror

where "t '~~>' t'" := (estep t t').


Fixpoint tm_to_tme (t : tm) :=
  match t with
  | tru => etru
  | fls => efls
  | ite t1 t2 t3 => eite (tm_to_tme t1) (tm_to_tme t2) (tm_to_tme t3)
  | zro => ezro
  | scc t1 => escc (tm_to_tme t1)
  | prd t1 => eprd (tm_to_tme t1)
  | iszro t1 => eiszro (tm_to_tme t1)
  end.

(**

  One way to describe tmes that don't merely contain an error is
  at the start, but instead generate it during evaluation, is by
  the tm_to_tme function. This function converts tms into analogous
  tmes.

  Unfortunately, working with a fixpoint can be complex. Define an
  inductive proposition that characterizes the tm_to_tme function.

*)

(**

Question 4: Define the tm_tme_analogue inductive proposition

*)

Inductive tm_tme_analogue : tm -> tme -> Prop :=
  | tm_tme_tru : tm_tme_analogue tru etru
  | tm_tme_fls : tm_tme_analogue fls efls
  | tm_tme_ite : forall t1 t2 t3 tme1 tme2 tme3,
      tm_tme_analogue t1 tme1 ->
      tm_tme_analogue t2 tme2 ->
      tm_tme_analogue t3 tme3 ->
      tm_tme_analogue (ite t1 t2 t3) (eite tme1 tme2 tme3)
  | tm_tme_zro : tm_tme_analogue zro ezro
  | tm_tme_scc : forall t tme1,
      tm_tme_analogue t tme1 ->
      tm_tme_analogue (scc t) (escc tme1)
  | tm_tme_prd : forall t tme1,
      tm_tme_analogue t tme1 ->
      tm_tme_analogue (prd t) (eprd tme1)
  | tm_tme_iszro : forall t tme1,
      tm_tme_analogue t tme1 ->
      tm_tme_analogue (iszro t) (eiszro tme1)
  .

(**
Question 5: Prove tm_tme_analogue is equivalent to tm_to_tme
*)

Theorem definition_equivalence : forall t t',
        tm_to_tme t = t' <-> tm_tme_analogue t t'.
Proof.
split.
- intros H. generalize dependent t'.
  induction t; 
  intros t' H; simpl in H; try reflexivity; subst; constructor; auto.
- intros H. 
  induction H; 
  simpl; try reflexivity; try rewrite IHtm_tme_analogue; try reflexivity.
  rewrite IHtm_tme_analogue1, IHtm_tme_analogue2, IHtm_tme_analogue3; auto.
Qed.

Inductive multiestep : tme -> tme -> Prop :=
  | multi_erefl : forall t, multiestep t t
  | multi_estep : forall x y z,
                    estep x y ->
                    multiestep y z ->
                    multiestep x z.

Notation "t1 '~~>*' t2" := (multiestep t1 t2) (at level 40).

(** Now, let's actually prove that well-typed terms don't error

    Hint: using your last theorem will make this proof easier

    Hint:you can use any theorem we've built up in Types.v, including
    progress, preservation, and type safety. This proof will be easier
    if you use them.
*)

Theorem well_typed_terms_dont_error :
        forall t t' tf T,
        |- t \in T ->
        tm_to_tme t = t' ->
        t' ~~>* tf ->
        tf <> eerror.
Proof.
  intros.
  revert t H H0.
  induction H1; intros.
  - rewrite <- H0. apply definition_equivalence in H0.
    induction H0; intro Hcontra; inversion Hcontra.
  - apply IHmultiestep with (t := t); auto.
Admitted.

End TME.


Module STLCProds.
(* Typically, programming language users don't want "pairs"
they want arbitrary-width tuples. 

I've copied the definitions of the simply typed lambda calculus
below.

Question 6. Update the below definitions to include arbitrary-length
tuples. You should add in a new tuple type: Ty_Tuple that can let
users provide tuples of size zero, one, two, three, or more. You should
add in a new tuple term that can let users provide tuples of size zero, one
two, three, or more. You should add in a new tuple value to describe
what values are tuple values. You should add in a new rule for substitution
to show how to substitute variables for terms in tuples.

You don't need to do anything about pretty printing for tuples.

*)

From Coq Require Import Strings.String.


Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Tuple : list ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm
(*
  | tm_tuple : list tm -> tm
*)
.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).


Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.
(*
  | v_tuple : forall ts,
      (forall t, nth t ts -> value t) -> value <{tm_tuple ts}>. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

End STLCProds.



Module Subtyping.

(** 

The following questions involve subtyping. Recall that the subtyping relation
for the simply typed lambda calculus with records and pairs is:

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}



Question 7:
Imagine we introduced a new subtyping rule for sums.

============
A <: A + B

Which of the following properties would be held, and which would
not be held. Justify your answers.

Progress?
Progress doesn't hold.
A counter example would be String <: String + Nat.
String is sub type of String + Nat. However,
no String value exists such that it is the type of String + Nat.


Preservation?
Preservation still holds.
The new rule doesn't affect the relationship between types
when it takes a step.


Determinism of small step evaluation?
Determinism of small step evaluation still holds.
The new rule doesn't affect the number of possible
outputs.



Question 8:

    Suppose we have  [S <: T] and [U <: V].  Which of the following
    subtyping assertions is false?

    (1) [S*U <: Top]

    (2) [{i1:S,i2:T}->U <: {i1:S,i2:T,i3:V}->U]

    (3) [(S->T) -> (Top -> Top)  <:  (S->T) -> Top]

    (4) [(Top -> Top) -> V  <:  Top -> V]

    (5) [S -> {i1:U,i2:V} <: S -> {i2:V,i1:U}]


Question 9:
    Suppose we have  [S <: T] and [U <: V].  Which of the following
    subtyping assertions is false?

    (1) [ {i1:Top} <: Top]

    (2) [Top -> (Top -> Top)  <:  Top -> Top]

    (3) [{i1:T} -> {i1:T}  <:  {i1:T,i2:S} -> Top]

    (4) [{i1:T,i2:V,i3:V} <: {i1:S,i2:U} * {i3:V}]

    (5) [Top -> {i1:U,i2:V} <: {i1:S} -> {i2:V,i1:V}]

*)


End Subtyping.
