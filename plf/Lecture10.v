Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.


Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

(** Exercise 1: implement an evaluation function for
this toy language *)

(** TODO *)


Module SSSNoValues.

(** Exercise 2: implement an evaluation relation for this 
toy language *)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)
  | E_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> (n1 + n2)
  where " t '==>' n " := (eval t n).

(** Exercise 3: define a small-step semantics for this 
toy language *)

(** The rules are: 

    
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_Plus2)
                      P (C n1) t2 --> P (C n1) t2'
*)

(** Solution: *)
Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C n1 ) t2 --> P (C n1) t2'
  where " t '-->' t' " := (step t t').


(** Exercise 4: prove the following examples *)

Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.
Qed.

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      -->
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
(* TODO *)
Qed.

End SSSNoValues.

Module SSSValues.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

(**  Exercise 5: encode the following rules: *)

(** 
                     -------------------------------        (ST_PlusConstConst)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_Plus2)
                         P v1 t2 --> P v1 t2'
*)

(**  Solution: *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | (* TODO *)

  where " t '-->' t' " := (step t t').

End SSSValues.




(* Exercise 6 *)

(** We will now define a small-step semantics
for the tiny imperative language Imp. We start with
arithmetic expressions and boolean expressions *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(** Exercise 6: complete the following definition. *)

Reserved Notation " t '/' st '-->a' t' "
                  (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st -->a ANum (st i)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  | AS_Minus1 : forall st a1 a1' a2,
      (* TODO *) ->
      (AMinus a1 a2) / st -->a (* TODO *)
  | AS_Minus2 : forall st v1 a2 a2',
      (* TODO *) ->
      (* TODO *) ->
      (AMinus v1 a2) / st -->a (* TODO *)
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (* TODO *)
  | AS_Mult1 : forall st a1 a1' a2,
      (* TODO *) ->
      (AMult a1 a2) / st -->a (* TODO *)
  | AS_Mult2 : forall st v1 a2 a2',
      (* TODO *) ->
      (* TODO *) ->
      (AMult v1 a2) / st -->a (* TODO *)
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (* TODO *)

    where " t '/' st '-->a' t' " := (astep st t t').


Example st1 := empty_st.
Example st2 := (X !-> 1).

(** Exercise 7: use this newly defined semantics to evaluate the
following example: *)
Example aexp1_eval1:
  APlus (APlus (ANum 1) (ANum 2)) (ANum 3) / empty_st
  -->a 
  APlus (ANum 3) (ANum 3).
Proof.
  apply AS_Plus1. apply AS_Plus.
Qed.


(** Exercise 8: do the same for boolean expressions. *)
Reserved Notation " t '/' st '-->b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq1 : forall st a1 a1' a2,
    (* TODO *) ->
    (BEq a1 a2) / st -->b (* TODO *)
| BS_Eq2 : forall st v1 a2 a2',
    (* TODO *) ->
    (* TODO *) ->
    (BEq v1 a2) / st -->b (* TODO *)
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st -->b
    (* TODO *)
| BS_LtEq1 : forall st a1 a1' a2,
   (* TODO *) ->
    (BLe a1 a2) / st -->b (* TODO *)
| BS_LtEq2 : forall st v1 a2 a2',
    (* TODO *) ->
    (* TODO *) ->
    (BLe v1 a2) / st -->b (* TODO *)
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st -->b
             (* TODO *)
| BS_NotStep : forall st b1 b1',
    (* TODO *) ->
    (BNot b1) / st -->b (* TODO *)
| BS_NotTrue : forall st,
    (BNot BTrue) / st -->b (* TODO *)
| BS_NotFalse : forall st,
    (BNot BFalse) / st -->b (* TODO *)
| BS_AndTrueStep : forall st b2 b2',
    (* TODO *) ->
    (BAnd BTrue b2) / st -->b (* TODO *)
| BS_AndStep : forall st b1 b1' b2,
    (* TODO *) ->
    (BAnd b1 b2) / st -->b (* TODO *)
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st -->b (* TODO *)
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st -->b (* TODO *)
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st -->b (* TODO *)

where " t '/' st '-->b' t' " := (bstep st t t').


(** Exercise 9: complete the small-step semantics for
commands. *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).


Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a1 a1',
      a1 / st ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Ass : forall st i n,
      <{ i := ANum n }> / st --> <{ SKIP }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      (* TODO *) ->
      <{ c1 ; c2 }> / st --> (* TODO *)
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> (* TODO *)
  | CS_IfStep : forall st b1 b1' c1 c2,
      (* TODO *) ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      (* TODO *)
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> (* TODO *)
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> (* TODO *)
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
     (* TODO *)

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(* Exercise 10 *)

(*
<{ if X=1 then X:=2 else X:=1 end }> / (X!->1)
--> CS_IfStep: 
      X=1 / (X!->1) 
      -->b BS_Eq1:
          X / (X!->1)
          -->a AS_Id
          ANum 1 
      ANum 1 = 1 / (X!->1)
      -->b BS_Eq
      BTrue
<{ if BTrue then X:=2 else X:=1 end }> / (X!->1)
--> CS_IfTrue
<{ X:=2 }> / (X!->1)
*)

Lemma exercise_10_last_step:
  <{ if BTrue then X:=2 else X:=1 end }> / (X!->1) -->
  <{ X := 2 }> / (X!->1).
Proof.
  apply CS_IfTrue.
Qed.


(* Exercise 11 *)

(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW *)


Notation "'par' c1 'with' c2 'end'" :=
         (CPar c1 c2)
            (in custom com at level 0, c1 at level 99, c2 at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{i := a1'}> / st
  | CS_Ass : forall st i n,
      <{i := ANum n}> / st --> <{skip}> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{c1 ; c2}> / st --> <{c1' ; c2}> / st'
  | CS_SeqFinish : forall st c2,
      <{skip ; c2}> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 /st -->b b1' ->
          <{if b1  then c1 else c2 end}> / st
      --> <{if b1' then c1 else c2 end}> / st
  | CS_IfTrue : forall st c1 c2,
      <{if true then c1 else c2 end}> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{if false then c1 else c2 end}> / st --> c2 / st
  | CS_While : forall st b1 c1,
          <{while b1 do c1 end}> / st
      --> <{if b1 then (c1; (while b1 do c1 end)) else skip end}> / st
    (* New part: *)
    (* TODO *)
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).







(** Here, we define something that will allow us to write some
interesting properties. See section "Multi-step relations"
for more details. *)
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).



(* Exercise 12 *)
(** Here's the example shown in the slides: *)
Definition par_ex1 : com :=
  <{ 
  par
    X := 1
  with
    X := 42
  end }>.

Example par_ex1_0:
  exists st',
       par_ex1 / empty_st  -->* <{ skip }> / st'
    /\ st' X = 42.
Proof.(* TODO *)
Qed. 

Example par_ex1_1:
  exists st',
       par_ex1 / empty_st  -->* <{ skip }> / st'
    /\ st' X = 1.
Proof.(* TODO *)
Qed.
 

(** Among the (many) interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)


Definition par_loop : com :=
  <{
  par
    Y := 1
  with
    while (Y = 0) do
      X := X + 1
    end
  end}>.

(** In particular, it can terminate with [X] set to [0]: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_st  -->* <{skip}> / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** It can also terminate with [X] set to [2]: *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_st -->* <{skip}> / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

End CImp.




(*********************************************************)
(*                      TYPES                            *)
(*********************************************************)

Module Types.

From PLF Require Import Smallstep.


Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.


(** _Values_ are [tru], [fls], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

(* Exercise 13 *)


Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> (* TODO *)
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> (* TODO *)
  | ST_Test : forall t1 t1' t2 t3,
      (* TODO *) ->
      (test t1 t2 t3) --> (* TODO *)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (* TODO *)
  | ST_PrdZro :
      (prd zro) --> (* TODO *)
  | ST_PrdScc : forall v,
      nvalue v ->
      (prd (scc v)) --> (* TODO *)
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (* TODO *)
  | ST_IszroZro :
      (iszro zro) --> (* TODO *)
  | ST_IszroScc : forall v,
       nvalue v ->
      (iszro (scc v)) --> (* TODO *)
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (* TODO *)

where "t '-->' t'" := (step t t').


Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.


Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.


(* Exercise 14 / 15 *)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in (* TODO *)
  | T_Fls :
       |- fls \in (* TODO *)
  | T_Test : forall t1 t2 t3 T,
       |- (* TODO *)->
       |- (* TODO *) ->
       |- (* TODO *)->
       |- test t1 t2 t3 \in (* TODO *)
  | T_Zro :
       |- zro \in (* TODO *)
  | T_Scc : forall t1,
       |- (* TODO *) ->
       |- scc t1 \in (* TODO *)
  | T_Prd : forall t1,
       |- (* TODO *)->
       |- prd t1 \in (* TODO *)
  | T_Iszro : forall t1,
       |-(* TODO *) ->
       |- iszro t1 \in (* TODO *)

where "'|-' t '\in' T" := (has_type t T).


(* Exercise 16 *)
Example has_type_0:
  |- test (iszro zro) (scc zro) (prd zro) \in Nat.
Proof.
 (* TODO *)
Qed.

(* From the book *)
Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
 (* TODO *)
Qed.


Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* Progress / Preservation / Soundness *)



End Types.