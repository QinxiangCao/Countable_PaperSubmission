Require Import Coq.Classes.RelationClasses.
Require Import CommonKnowledge.Classes.AbstractEqual.
Require Import CommonKnowledge.Relations.Mappings.
Require Import CommonKnowledge.Relations.SetoidMappings.
Require Import CommonKnowledge.Relations.Countable.

Definition Countable (A: Type) {eqA: AbstractEq A}: Type := @injection A nat _ (RealEq nat).

Section Countable.

Context {A B: Type}.
Context {eqA: AbstractEq A} {eqB: AbstractEq B}.
Context {equA: Equivalence (@abstract_eq _ eqA)} {equB: Equivalence (@abstract_eq _ eqB)}.

Definition injection_Countable 
           (R: injection A B) (CB: Countable B): Countable A := injection_trans R CB.

Definition bijection_Countable (R: bijection A B) (CB: Countable B): Countable A := injection_Countable (bijection_injection R) CB.

Local Existing Instance RealEq_IsRealEq.
Local Existing Instance EqSum_IsRealEq.
Local Existing Instance EqProd_IsRealEq.

Definition sum_Countable (CA: Countable A) (CB: Countable B): Countable (sum A B) :=
  injection_trans (sum_injection CA CB)
    (bijection_injection (bijection_setoid_biject_s nat2_nat_bijection _ _)).

Definition prod_Countable (CA: Countable A) (CB: Countable B): Countable (prod A B) :=
  injection_trans (prod_injection CA CB)
    (bijection_injection (bijection_setoid_biject_s natnat_nat_bijection _ _)).

Definition nCountable_Countable {A: nat -> Type} (eqA1 : forall n , AbstractEq (A n))
  (equA1 : forall n , Equivalence (@abstract_eq _ (eqA1 n)))
   (CA: forall n, @Countable (A n) (eqA1 n)) : @Countable (sigT A) (EqSigT A):=
  injection_trans (@sigT_injection nat _ _ nat A eqA1 equA1 CA) 
    (bijection_injection (bijection_setoid_biject_s natnat_nat_bijection _ _)).
    
Definition unit_Countable: @Countable unit (RealEq unit).
  apply (FBuild_injection (fun _ => 0)).
  + hnf; intros.
    destruct a1, a2.
    reflexivity.
  + hnf; intros; hnf; intros.
    auto.
Qed.

Definition void_Countable: (A -> False) -> Countable A.
  intros.
  apply (FBuild_injection (fun _ => 0)).
  + hnf; intros.
    exfalso.
    apply H, a1.
  + hnf; intros.
    reflexivity.
Qed.

End Countable.

Lemma Countable_SetoidCountable {A: Type}:
  Countable.Countable A -> @Countable A (RealEq _).
Proof.
  intros.
  apply injection_setoid_inject.
  auto.
Qed.

Lemma SetoidCountable_Countable {A: Type}:
  @Countable A (RealEq _) -> Countable.Countable A. 
Proof.
  intros. exists X ; apply X.
Qed.

Ltac solve_Countable :=
  match goal with
  | |- Countable (sum _ _) => apply sum_Countable; solve_Countable
  | |- Countable (prod _ _) => apply prod_Countable; solve_Countable
  | |- Countable (sigT _) => try (apply nCountable_Countable;
                                  [ intros; try solve [typeclasses eauto]
                                  | intro; solve_Countable ])
  | |- Countable unit => apply unit_Countable
  | |- @Countable _ (RealEq _) => apply Countable_SetoidCountable; Countable.solve_Countable
  | _ => try assumption
  end.
