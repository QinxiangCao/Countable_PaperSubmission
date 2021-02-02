Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Arith.Even.
Require Import Coq.Arith.Div2.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import CommonKnowledge.Classes.RelationConstructorClasses.
Require Import CommonKnowledge.Classes.AbstractEqual.
Require Import CommonKnowledge.Relations.Mappings.

Section Def1.

Import EquivNotations.
Local Open Scope ordering.

Context {A B: Type}.
Context {eqA: AbstractEq A}.
Context {eqB: AbstractEq B}.

Definition image_defined (R: A -> B -> Prop): Prop :=
  forall a, exists b, R a b.

Definition partial_functional (R: A -> B -> Prop): Prop :=
  forall a b1 b2, R a b1 -> R a b2 -> b1 == b2.

Definition injective (R: A -> B -> Prop): Prop :=
  forall a1 a2 b, R a1 b -> R a2 b -> a1 == a2.

Definition surjective (R: A -> B -> Prop): Prop :=
  forall b, exists a, R a b.

Definition function_injective (f: A -> B): Prop :=
  forall a1 a2, f a1 == f a2 -> a1 == a2.

Definition function_surjective (f: A -> B): Prop :=
  forall b, exists a, f a == b.

End Def1.

Section Def2.

Context (A B: Type).
Context {eqA: AbstractEq A}.
Context {eqB: AbstractEq B}.

Record injection: Type := {
  inj_R:> A -> B -> Prop;
  wd_inj: Proper (abstract_eq ==> abstract_eq ==> iff) inj_R;
  im_inj: image_defined inj_R;
  pf_inj: partial_functional inj_R;
  in_inj: injective inj_R
}.

Record surjection: Type := {
  surj_R:> A -> B -> Prop;
  wd_surj: Proper (abstract_eq ==> abstract_eq ==> iff) surj_R;
  im_surj: image_defined surj_R;
  pf_surj: partial_functional surj_R;
  su_surj: surjective surj_R
}.

Record bijection: Type := {
  bij_R:> A -> B -> Prop;
  wd_bij: Proper (abstract_eq ==> abstract_eq ==> iff) bij_R;
  im_bij: image_defined bij_R;
  pf_bij: partial_functional bij_R;
  in_bij: injective bij_R;
  su_bij: surjective bij_R
}.

End Def2.

Existing Instances wd_inj wd_surj wd_bij.

Section Construction.

Import EquivNotations.
Local Open Scope ordering.

Context {A B: Type}.
Context {eqA: AbstractEq A}.
Context {eqB: AbstractEq B}.
Context {equA: @Equivalence A abstract_eq}.
Context {equB: @Equivalence B abstract_eq}.

Program Definition FBuild_injection
        (f: A -> B)
        (H: function_injective f)
        (H0: Proper (abstract_eq ==> abstract_eq) f): injection A B :=
  Build_injection _ _ (fun a b => f a == b) _ _ _ _.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Program Definition FBuild_surjection
        (f: A -> B)
        (H: function_surjective f)
        (H0: Proper (abstract_eq ==> abstract_eq) f): surjection A B :=
  Build_surjection _ _ (fun a b => f a == b) _ _ _ _.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Program Definition FBuild_bijection
           (f: A -> B)
           (H: function_injective f)
           (H0: function_surjective f)
           (H1: Proper (abstract_eq ==> abstract_eq) f): bijection A B :=
  Build_bijection _ _ (fun a b => f a == b) _ _ _ _ _.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Program Definition bijection_refl: bijection A A :=
  Build_bijection _ _ abstract_eq _ _ _ _ _.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Program Definition bijection_sym (R: bijection A B): bijection B A :=
  Build_bijection _ _ (fun a b => R b a) _ _ _ _ _.
Next Obligation.
  split.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
Qed.
Next Obligation.
  hnf. apply (su_bij _ _ R).
Qed.
Next Obligation.
  hnf. intros. apply (in_bij _ _ R b1 b2 a H H0).
Qed.
Next Obligation.
  hnf. intros. apply (pf_bij _ _ R b a1 a2 H H0).
Qed.
Next Obligation.
  hnf. intros. apply (im_bij _ _ R).
Qed.

Definition bijection_injection (R: bijection A B): injection A B :=
  Build_injection _ _ R (wd_bij _ _ R) (im_bij _ _ R) (pf_bij _ _ R) (in_bij _ _ R).

Section trans.

Context {C: Type}.
Context {eqC: AbstractEq C}.
Context {equC: Equivalence eqC}.

Lemma injective_compose (R1: A -> B -> Prop) (R2: B -> C -> Prop) (PrR1: Proper (abstract_eq ==> abstract_eq ==> iff) R1):
  injective R1 ->
  injective R2 ->
  injective (fun a c => exists b, R1 a b /\ R2 b c).
Proof.
  unfold injective.
  intros.
  destruct H1 as [b1 [? ?]], H2 as [b2 [? ?]].
  specialize (H0 _ _ _ H3 H4).
  rewrite H0 in *.
  specialize (H _ _ _ H1 H2).
  auto.
Qed.

Lemma injective_compose_rev (R1: A -> B -> Prop) (R2: B -> C -> Prop):
  image_defined R2 ->
  injective (fun a c => exists b, R1 a b /\ R2 b c) ->
  injective R1.
Proof.
  unfold injective, image_defined.
  intros.
  pose proof H b as [c ?].
  apply H0 with c; exists b; auto.
Qed.

Program Definition injection_trans (R1: injection A B) (R2: injection B C): injection A C :=
  Build_injection _ _ (fun a c => exists b, R1 a b /\ R2 b c) _ _ _ _.
Next Obligation.
  split.
  - intros. destruct H1 as [b H1]. exists b. destruct H1. split.
    + rewrite <- H. auto.
    + rewrite <- H0. auto.
  -
    intros. destruct H1 as [b H1]. exists b. destruct H1. split.
    + rewrite H. auto.
    + rewrite H0. auto.
Qed.
Next Obligation.
  hnf. intros.
  destruct (im_inj _ _ R1 a) as [b ?].
  destruct (im_inj _ _ R2 b) as [c ?].
  exists c. eauto.
Qed.
Next Obligation.
  hnf.
  intros a c1 c2 [b1 [? ?]] [b2 [? ?]].
  pose proof pf_inj _ _ R1 a b1 b2 H H1.
  pose proof pf_inj _ _ R2 b1 c1 c2.
  apply H4; auto.
  rewrite H3.
  auto.
Qed.
Next Obligation.
  hnf; intros a1 a2 c [b1 [? ?]] [b2 [? ?]].
  pose proof in_inj _ _ R2 b1 b2 c H0 H2.
  pose proof in_inj _ _ R1 a1 a2 b2.
  apply H4; auto.
  rewrite <- H3; auto.
Qed.

End trans.

Section alg.

Context {A0 B0: Type}.
Context {eqA0: AbstractEq A0}.
Context {eqB0: AbstractEq B0}.
Context {equA0: @Equivalence A0 abstract_eq}.
Context {equB0: @Equivalence B0 abstract_eq}.
Local Existing Instances EqSum EqSumEqu EqProd EqProdEqu EqSigT EqSigTEqu.

Definition sum_injection (R: injection A B) (R0: injection A0 B0): injection (sum A A0) (sum B B0).
Proof.
  intros.
  apply (Build_injection _ _ (fun a b =>
          match a, b with
          | inl a, inl b => R a b
          | inr a, inr b => R0 a b
          | _, _ => False
          end)).
  + hnf; intros a1 a2 ?H.
    hnf; intros b1 b2 ?H.
    inversion H; subst;
    inversion H0; subst.
    - rewrite H1, H2.
      reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite H1, H2.
      reflexivity.
  + hnf; intros.
    destruct a as [a | a].
    - destruct (im_inj _ _ R a) as [b ?].
      exists (inl b); auto.
    - destruct (im_inj _ _ R0 a) as [b ?].
      exists (inr b); auto.
  + hnf; intros.
    destruct a as [a | a], b1 as [b1 | b1], b2 as [b2 | b2]; try solve [inversion H | inversion H0].
    - constructor; apply (pf_inj _ _ R a); auto.
    - constructor; apply (pf_inj _ _ R0 a); auto.
  + hnf; intros.
    destruct a1 as [a1 | a1], a2 as [a2 | a2], b as [b | b]; try solve [inversion H | inversion H0].
    - constructor; apply (in_inj _ _ R _ _ b); auto.
    - constructor; apply (in_inj _ _ R0 _ _ b); auto.
Defined.

Definition prod_injection (R: injection A B) (R0: injection A0 B0): injection (prod A A0) (prod B B0).
Proof.
  intros.
  apply (Build_injection _ _ (fun a b => R (fst a) (fst b) /\ R0 (snd a) (snd b))).
  + hnf; intros [a11 a12] [a21 a22] [?H ?H].
    hnf; intros [b11 b12] [b21 b22] [?H ?H].
    simpl in *.
    rewrite H, H0, H1, H2.
    tauto.
  + hnf; intros.
    destruct (im_inj _ _ R (fst a)) as [b1 ?].
    destruct (im_inj _ _ R0 (snd a)) as [b2 ?].
    exists (b1, b2); auto.
  + hnf; intros.
    destruct b1, b2, H, H0.
    pose proof pf_inj _ _ R (fst a) _ _ H H0.
    pose proof pf_inj _ _ R0 (snd a) _ _ H1 H2.
    simpl in *; split; subst; auto.
  + hnf; intros.
    destruct a1, a2, H, H0.
    pose proof in_inj _ _ R _ _ _ H H0.
    pose proof in_inj _ _ R0 _ _ _ H1 H2.
    simpl in *; split; subst; auto.
Defined.

Definition sigT_injection {I: Type} {A1: I -> Type} {eqA1: forall i, AbstractEq (A1 i)}
  {equA1: forall i, Equivalence (@abstract_eq (A1 i) (eqA1 i))}
  (R: forall i: I, injection (A1 i) B): @injection (sigT A1) (I * B) _ (@EqProd _ _ (RealEq _) _).
  apply (Build_injection _ _ (fun a b => projT1 a = fst b /\ (R (projT1 a)) (projT2 a) (snd b))).
  + hnf; intros a1 a2 ?H.
    hnf; intros [b11 b12] [b21 b22] [?H ?H].
    simpl in *.
    hnf in H0.
    apply path_sigT_relation in H.
    destruct H as [?H ?H].
    change (@abstract_eq _ (eqA1 (projT1 a2)) (eq_rect (projT1 a1) A1 (projT2 a1) (projT1 a2) H) (projT2 a2)) in H2.
    split; intros [? ?]; subst.
    - split; auto.
      destruct a1, a2; simpl in *.
      destruct H.
      rewrite <- H2, <- H1.
      simpl.
      auto.
    - split; auto.
      destruct a1, a2; simpl in *.
      destruct H.
      rewrite H2, H1.
      simpl.
      auto.
  + hnf; intros.
    destruct a as [i a0].
    destruct (im_inj _ _ (R i) a0) as [b0 ?].
    exists (i, b0).
    auto.
  + hnf; intros.
    destruct b1 as [i1 b1]; simpl in H.
    destruct b2 as [i2 b2]; simpl in H0.
    destruct H, H0; subst.
    pose proof pf_inj _ _ (R (projT1 a)) _ _ _ H1 H2.
    split; simpl; [reflexivity | exact H].
  + hnf; intros.
    destruct b, H, H0; simpl in *; subst.
    destruct a1, a2; simpl in *; subst.
    pose proof in_inj _ _ (R x) _ _ _ H1 H2.
    constructor; auto.
Qed.

End alg.

Section EqSetoid.

Program Definition bijection_setoid_biject_s (f: Mappings.bijection A B) (_: IsRealEq A eqA) (_: IsRealEq B eqB): bijection A B :=
  Build_bijection _ _ f _ _ _ _ _.
Next Obligation.
  hnf. intros.
  hnf. intros.
  apply H in H1; apply H0 in H2.
  subst y y0.
  tauto.
Qed.
Next Obligation.
  hnf. intros. apply (Mappings.im_bij _ _ f).
Qed.
Next Obligation.
  hnf. intros.
  apply H0.
  apply (Mappings.pf_bij _ _ f a b1 b2 H1 H2).
Qed.
Next Obligation.
  hnf. intros.
  apply H.
  apply (Mappings.in_bij _ _ f a1 a2 b H1 H2).
Qed.
Next Obligation.
  hnf. intros. apply (Mappings.su_bij _ _ f).
Qed.

Local Existing Instances RealEq RealEqEqu.

Program Definition injection_setoid_inject {A B} (f: Mappings.injection A B): injection A B :=
  Build_injection _ _ f _ _ _ _.
Next Obligation.
  hnf. intros. apply (Mappings.im_inj _ _ f).
Qed.
Next Obligation.
  hnf. intros.
  apply (Mappings.pf_inj _ _ f a b1 b2 H H0).
Qed.
Next Obligation.
  hnf. intros.
  apply (Mappings.in_inj _ _ f a1 a2 b H H0).
Qed.

Program Definition surjection_setoid_surject {A B} (f: Mappings.surjection A B): surjection A B :=
  Build_surjection _ _ f _ _ _ _.
Next Obligation.
  hnf. intros. apply (Mappings.im_surj _ _ f).
Qed.
Next Obligation.
  hnf. intros.
  apply (Mappings.pf_surj _ _ f a b1 b2 H H0).
Qed.
Next Obligation.
  hnf. intros. apply (Mappings.su_surj _ _ f).
Qed.

Program Definition bijection_setoid_biject_w {A B} (f: Mappings.bijection A B): bijection A B :=
  Build_bijection _ _ f _ _ _ _ _.
Next Obligation.
  hnf. intros. apply (Mappings.im_bij _ _ f).
Qed.
Next Obligation.
  hnf. intros.
  apply (Mappings.pf_bij _ _ f a b1 b2 H H0).
Qed.
Next Obligation.
  hnf. intros.
  apply (Mappings.in_bij _ _ f a1 a2 b H H0).
Qed.
Next Obligation.
  hnf. intros. apply (Mappings.su_bij _ _ f).
Qed.

End EqSetoid.

End Construction.

Lemma inject_extra_attr: forall A B (f: A -> B) (P: A -> B -> Prop),
  (forall a, P a (f a)) ->
  @injection A (@sigT B (fun b: B => sig (fun a => P a b))) 
    (RealEq A)
    (@EqSigT B
       (fun b => @sig A (fun a => P a b))
       (fun b => @EqSig A (fun a => P a b) (RealEq A))).
Proof.
  intros.
  apply
    (SetoidMappings.FBuild_injection
       (fun a => existT _ (f a) (exist _ a (H a)))).
  + hnf. intros.
    inversion H0; subst.
    destruct H2.
    destruct H1.
    inversion H3.
    inversion H5.
    congruence.
  + hnf; intros.
    destruct H0.
    reflexivity.
Qed.

