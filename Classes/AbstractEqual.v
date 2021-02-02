Require Import Coq.Classes.RelationClasses.
Require Import CommonKnowledge.Relations.RelationConstructors.
Require Import CommonKnowledge.Classes.RelationConstructorClasses.

Class AbstractEq (A: Type): Type :=
  abstract_eq: relation A.

Module EquivNotations.

Declare Scope ordering.

Notation "a == b" := (abstract_eq a b) (at level 70, no associativity): ordering.
Notation "a =/= b" := (not (abstract_eq a b)) (at level 70, no associativity): ordering.

End EquivNotations.

Definition RealEq (A: Type): AbstractEq A := @eq A.

Lemma RealEqEqu (A: Type): Equivalence (@abstract_eq _ (RealEq A)).
Proof. apply eq_equivalence. Qed.

Definition EqProd (A B: Type) {EqA: AbstractEq A} {EqB: AbstractEq B}: AbstractEq (prod A B) :=
  prod_relation abstract_eq abstract_eq.

Definition EqSum (A B: Type) {EqA: AbstractEq A} {EqB: AbstractEq B}: AbstractEq (sum A B) :=
  sum00_relation abstract_eq abstract_eq.

Definition EqSigT {I: Type} (A: I -> Type) {EqA: forall i, AbstractEq (A i)}: AbstractEq (sigT A) :=
  sigT_relation (fun i => @abstract_eq (A i) (EqA i)).

Definition EqSig {A: Type} (P: A -> Prop) {EqA: AbstractEq A}: AbstractEq (sig P) :=
  sig_relation P abstract_eq.

Lemma EqProdEqu (A B: Type) {EqA: AbstractEq A} {EqB: AbstractEq B}
  {EquA: Equivalence (@abstract_eq A EqA)} {EquB: Equivalence (@abstract_eq B EqB)}:
  Equivalence (@abstract_eq (A * B) (EqProd A B)).
Proof. apply prod_relation_Equivalence; auto. Qed.

Lemma EqSumEqu (A B: Type) {EqA: AbstractEq A} {EqB: AbstractEq B}
  {EquA: Equivalence (@abstract_eq A EqA)} {EquB: Equivalence (@abstract_eq B EqB)}:
  Equivalence (@abstract_eq (A + B) (EqSum A B)).
Proof. apply sum00_equivalence; auto. Qed.

Lemma EqSigTEqu {I: Type} (A: I -> Type) {EqA: forall i, AbstractEq (A i)}
  {EquA: forall i, Equivalence (@abstract_eq (A i) (EqA i))}:
  Equivalence (@abstract_eq (sigT A) (EqSigT A)).
Proof. apply sigT_relation_equivalence; auto. Qed.

Lemma EqSigEqu {A: Type} (P: A -> Prop) {EqA: AbstractEq A} {EquA: Equivalence abstract_eq}:
  Equivalence (@abstract_eq (sig P) (EqSig P)).
Proof. apply sig_relation_equivalence; auto. Qed.

Section IsRealEq.

Import EquivNotations.
Local Open Scope ordering.

Class IsRealEq (A: Type) (EqA: AbstractEq A) :=
  is_real_eq: forall a b: A, a == b <-> a = b.

Lemma RealEq_IsRealEq (A: Type): IsRealEq A (RealEq A).
Proof. firstorder. Qed.

Lemma EqSum_IsRealEq (A B: Type) (EqA: AbstractEq A) (EqB: AbstractEq B):
  IsRealEq A EqA -> IsRealEq B EqB -> IsRealEq (A + B) (EqSum A B).
Proof.
  intros.
  hnf; intros.
  split; intros.
  + inversion H1; subst.
    - f_equal.
      apply H; auto.
    - f_equal.
      apply H0; auto.
  + subst b.
    destruct a.
    - constructor.
      apply H; auto.
    - constructor.
      apply H0; auto.
Qed.

Lemma EqProd_IsRealEq (A B: Type) (EqA: AbstractEq A) (EqB: AbstractEq B):
  IsRealEq A EqA -> IsRealEq B EqB -> IsRealEq (A * B) (EqProd A B).
Proof.
  intros.
  hnf; intros.
  split; intros.
  + destruct a as [a1 a2], b as [b1 b2].
    destruct H1 as [H1 H2]; simpl in H1, H2.
    f_equal; [apply H | apply H0]; auto.
  + subst b.
    destruct a as [a1 a2].
    split; simpl; [apply H | apply H0]; auto.
Qed.

Lemma EqSigT_IsRealEq {I: Type} (A: I -> Type) {EqA: forall i, AbstractEq (A i)}:
  (forall i, IsRealEq (A i) (EqA i)) -> IsRealEq (sigT A) (EqSigT A).
Proof.
  intros.
  hnf; intros.
  split; intros.
  + inversion H0; subst.
    apply H in H1.
    subst; auto.
  + subst.
    destruct b as [i a].
    constructor.
    apply H; auto.
Qed.

End IsRealEq.

