(* start from Maps.v *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y:string):bool:=
  if string_dec x y then true else false.

(* for review the usage of destruct *)
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.

Check string_dec.
Check 1<>1.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs] eqn:E. Print left.
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Lemma equality_commutes:
  forall (a: bool) (b: bool), a = b -> b = a.
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite <- H in Hs. destruct Hs. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.


Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

Definition total_map (A : Type) := string -> A.
Print total_map.

Compute (total_map bool).

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Print t_empty.

Compute (t_empty false).




Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Print None.

Print t_update.

Check (t_update (t_empty false) "foo" true).

Check (t_empty false).


Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.
Print examplemap.

Definition examplemap2:=t_update examplemap "foo" false.

Compute (examplemap "foo").
Compute (examplemap "bar").
Compute (examplemap2 "foo").

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).


Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros A x v.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  rewrite <- eqb_string_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v.
  unfold t_update.
  intros H.
  rewrite <- eqb_string_false_iff in H.
  rewrite H.
  reflexivity.
 Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality_dep.
  unfold t_update.
  intros x0.
  unfold eqb_string.
  destruct (string_dec x x0).
    -reflexivity.
    -reflexivity.
Qed.

Example apply_ex1:forall P Q:Prop,
(P->Q)->P->Q.
Proof.
  intros P Q P_imply_Q P_holds.
  (*apply P_imply_Q in P_holds.*)
  apply P_imply_Q.
  apply P_holds.
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y.
  (*Check (x=y).*)
  (*Check (refle1ct (x = y) (eqb_string x y)).*)
  unfold eqb_string.
  destruct (string_dec x y).
  - apply ReflectT. apply e.
  - apply ReflectF. apply n.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros A m x.
  unfold t_update.
  apply functional_extensionality_dep.
  intros x0.
  destruct (eqb_stringP x x0).
  - rewrite e. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2.
  intros H.
  unfold t_update.
  apply functional_extensionality_dep.
  intros x.
  destruct (eqb_stringP x1 x).
  - rewrite e in H. apply <- eqb_string_false_iff in H. rewrite H. reflexivity.
  - destruct (eqb_string x2 x). reflexivity. reflexivity.
Qed.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).


Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).


Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).



Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Check @empty.

Check @update.
Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.