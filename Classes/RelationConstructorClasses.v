Require Export Coq.Relations.Relations.
Require Import CommonKnowledge.Relations.RelationConstructors.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.

Instance eq_preorder (A: Type): PreOrder (@eq A) :=
  Build_PreOrder _ (eq_Reflexive) (eq_Transitive).

Instance prod_relation_Reflexive {A B: Type} (RA: relation A) (RB: relation B)
  {_: Reflexive RA} {_: Reflexive RB} : Reflexive (prod_relation RA RB).
Proof. firstorder. Qed.

Instance prod_relation_Symmetric {A B: Type} (RA: relation A) (RB: relation B)
  {_: Symmetric RA} {_: Symmetric RB}: Symmetric (prod_relation RA RB).
Proof. firstorder. Qed.

Instance prod_relation_Transitive {A B: Type} (RA: relation A) (RB: relation B)
  {_: Transitive RA} {_: Transitive RB}: Transitive (prod_relation RA RB).
Proof. firstorder. Qed.

Program Instance prod_relation_Equivalence {A B: Type} (RA: relation A) (RB: relation B)
  {_: Equivalence RA} {_: Equivalence RB}: Equivalence (prod_relation RA RB).

Program Instance prod_relation_PreOrder {A B: Type} (RA: relation A) (RB: relation B)
  {_: PreOrder RA} {_: PreOrder RB}: PreOrder (prod_relation RA RB).

Program Instance pointwise_preorder A {B : Type} (RB : relation B) {_: PreOrder RB}:
  PreOrder (pointwise_relation A RB).

Instance option00_reflexive {A: Type} (R: relation A) {_: Reflexive R}: Reflexive (option00_relation R).
Proof.
  hnf; intros.
  destruct x.
  + constructor; reflexivity.
  + constructor.
Qed.

Instance option01_reflexive {A: Type} (R: relation A) {_: Reflexive R}: Reflexive (option01_relation R).
Proof.
  hnf; intros.
  destruct x.
  + constructor; reflexivity.
  + constructor.
Qed.

Instance option00_symmetric {A: Type} (R: relation A) {_: Symmetric R}: Symmetric (option00_relation R).
Proof.
  hnf; intros.
  inversion H0; subst.
  + constructor.
  + constructor.
    symmetry; auto.
Qed.

Instance option00_transitive {A: Type} (R: relation A) {_: Transitive R}: Transitive (option00_relation R).
Proof.
  hnf; intros.
  hnf; intros.
  inversion H0; inversion H1; subst; try first [congruence | constructor].
  inversion H6; subst.
  etransitivity; eauto.
Qed.

Instance option01_transitive {A: Type} (R: relation A) {_: Transitive R}: Transitive (option01_relation R).
Proof.
  hnf; intros.
  hnf; intros.
  inversion H0; inversion H1; subst; try first [congruence | constructor].
  inversion H6; subst.
  etransitivity; eauto.
Qed.

Instance option00_preorder {A: Type} (R: relation A) {_: PreOrder R}: PreOrder (option00_relation R)
  := Build_PreOrder _ (option00_reflexive R) (option00_transitive R).

Instance option01_preorder {A: Type} (R: relation A) {_: PreOrder R}: PreOrder (option01_relation R)
  := Build_PreOrder _ (option01_reflexive R) (option01_transitive R).

Instance option00_equiv {A: Type} (R: relation A) {_: Equivalence R}: Equivalence (option00_relation R)
  := Build_Equivalence _ (option00_reflexive R) (option00_symmetric R) (option00_transitive R).

Instance sum00_reflexive {A B: Type} (RA: relation A) (RB: relation B) {_: Reflexive RA} {_: Reflexive RB}: Reflexive (sum00_relation RA RB).
Proof.
  hnf; intros.
  destruct x; constructor; auto.
Qed.

Instance sum01_reflexive {A B: Type} (RA: relation A) (RB: relation B) {_: Reflexive RA} {_: Reflexive RB}: Reflexive (sum01_relation RA RB).
Proof.
  hnf; intros.
  destruct x; constructor; auto.
Qed.

Instance sum00_symmetric {A B: Type} (RA: relation A) (RB: relation B) {_: Symmetric RA} {_: Symmetric RB}: Symmetric (sum00_relation RA RB).
Proof.
  hnf; intros.
  inversion H1; subst; constructor; auto.
Qed.

Instance sum00_transitive {A B: Type} (RA: relation A) (RB: relation B) {_: Transitive RA} {_: Transitive RB}: Transitive (sum00_relation RA RB).
Proof.
  hnf; intros.
  inversion H1; subst; inversion H2; subst;
  constructor;
  etransitivity; eauto.
Qed.

Instance sum01_transitive {A B: Type} (RA: relation A) (RB: relation B) {_: Transitive RA} {_: Transitive RB}: Transitive (sum01_relation RA RB).
Proof.
  hnf; intros.
  inversion H1; subst; inversion H2; subst;
  constructor;
  etransitivity; eauto.
Qed.

Program Instance sum00_preorder {A B: Type} (RA: relation A) (RB: relation B)
  {_: PreOrder RA} {_: PreOrder RB}: PreOrder (sum00_relation RA RB).

Program Instance sum00_equivalence {A B: Type} (RA: relation A) (RB: relation B)
  {_: Equivalence RA} {_: Equivalence RB}: Equivalence (sum00_relation RA RB).

Program Instance sum01_preorder {A B: Type} (RA: relation A) (RB: relation B)
  {_: PreOrder RA} {_: PreOrder RB}: PreOrder (sum01_relation RA RB).

Instance full_reflexive (A: Type): Reflexive (full_relation A).
Proof. firstorder. Qed.

Instance full_symmetric (A: Type): Symmetric (full_relation A).
Proof. firstorder. Qed.

Instance full_transitive (A: Type): Transitive (full_relation A).
Proof. firstorder. Qed.

Program Instance full_preorder (A: Type): PreOrder (full_relation A).

Program Instance full_equivalence (A: Type): PreOrder (full_relation A).

Instance sigT_relation_reflexive {I: Type} {A: I -> Type} (RA: forall i, relation (A i))
  {_: forall i, Reflexive (RA i)}: Reflexive (sigT_relation RA).
Proof.
  hnf; intros.
  destruct x.
  econstructor.
  apply H.
Qed.

Instance sigT_relation_symmetric {I: Type} {A: I -> Type} (RA: forall i, relation (A i))
  {_: forall i, Symmetric (RA i)}: Symmetric (sigT_relation RA).
Proof.
  hnf; intros.
  inversion H0; subst.
  econstructor.
  apply H; auto.
Qed.

Lemma path_sigT {I: Type} {A: I -> Type} (x y : sigT A) (H : x = y) :
  { p : projT1 x = projT1 y & eq_rect _ A (projT2 x) _ p = projT2 y }.
Proof.
  exists (f_equal _ H).
  destruct H; reflexivity.
Qed.

Lemma path_sigT_relation {I: Type} {A: I -> Type} (RA: forall i, relation (A i))
  (x y : sigT A) (H: sigT_relation RA x y):
  { p : projT1 x = projT1 y & RA _ (eq_rect _ A (projT2 x) _ p) (projT2 y) }.
Proof.
  inversion H.
  simpl in *.
  exists eq_refl.
  simpl.
  auto.
Qed.

Instance sigT_relation_transitive {I: Type} {A: I -> Type} (RA: forall i, relation (A i))
  {_: forall i, Transitive (RA i)}: Transitive (sigT_relation RA).
Proof.
  intros; hnf; intros.
  inversion H0; inversion H1; subst.
  apply path_sigT in H6.
  destruct H6.
  simpl in *.
  subst.
  econstructor.
  eapply H; eassumption.
Qed.

Program Instance sigT_relation_equivalence {I} {A: I -> Type} (RA: forall i, relation (A i)) 
  {_: forall i, Equivalence (RA i)}: Equivalence (sigT_relation RA).

Instance sig_relation_reflexive {A: Type} {P: A -> Prop} (RA:relation A)
  {_: Reflexive RA}: Reflexive (sig_relation P RA).
Proof.
  hnf; intros.
  destruct x.
  constructor.
  apply H.
Qed.

Instance sig_relation_symmetric {A: Type} {P: A -> Prop} (RA:relation A)
  {_: Symmetric RA}: Symmetric (sig_relation P RA).
Proof.
  hnf; intros.
  destruct x, y.
  constructor.
  inversion H0; subst.
  apply H; auto.
Qed.

Instance sig_relation_transitive {A: Type} {P: A -> Prop} (RA:relation A)
  {_: Transitive RA}: Transitive (sig_relation P RA).
Proof.
  hnf; intros.
  destruct x, y, z.
  constructor.
  inversion H0; inversion H1; subst.
  eapply H; eauto.
Qed.

Program Instance sig_relation_equivalence {A: Type} {P: A -> Prop} (RA:relation A)
  {_: Equivalence RA}: Equivalence (sig_relation P RA).
