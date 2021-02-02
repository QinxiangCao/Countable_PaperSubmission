Require Import Omega.
Require Import CommonKnowledge.Classes.AbstractEqual.
Require Import CommonKnowledge.Relations.SetoidMappings.
Require Import CommonKnowledge.Relations.Mappings.
Require Import CommonKnowledge.Relations.SetoidCountable.
Require Import CommonKnowledge.Relations.Countable.
Require Import CommonKnowledge.Relations.RelationConstructors.
Require Import CommonKnowledge.IndType.Syntax.
Require Import CommonKnowledge.Relations.IndCountable.
Require Import List.

Axiom Countable_nat : Countable nat.
(** We can prove the axiom but it is not meaningful *)

Theorem Countable_Countable_T0 : forall T , Countable T -> option_Countable (Some T).
Proof. auto. Qed.

Ltac Countable_simpl_solver := solve_Countable ; try (apply Countable_nat) ; try assumption.

Ltac Countable_solver := 
     Countable_simpl_solver ; 
     match goal with 
      | |- Countable ?T =>  set (rect_T := ltac:(gen_rect T)) ;
                            set (constrs_T := ltac:(gen_constrs T rect_T)) ;
                            assert (T_rect_correct : forall P para , Sol2.para_rect_correct T P para constrs_T (rect_T (P constrs_T))) by para_rect_correctness_gen;
                            apply (Countable_T T constrs_T rect_T T_rect_correct); 
                            subst constrs_T; clear rect_T T_rect_correct; 
                            repeat constructor ; Countable_solver
      | |- option_Countable _ => apply Countable_Countable_T0 ; Countable_solver
      | _ => try assumption 
     end.

Inductive Nat :=
| SNat : bool -> Nat -> Nat
| ONat : Nat.

Inductive naT :=
| O : naT
| S : naT -> naT.

Inductive Tree :=
| TT3 : nat -> Tree -> Tree -> Tree -> Tree
| TT2 : Tree -> bool -> Tree -> Tree
| TT1 : Tree -> Tree
| TT0 : Tree.

Theorem Countable_bool : Countable bool.
Proof.
  Countable_solver.
Qed.

Theorem Countable_naT : Countable naT.
Proof.
  Countable_solver.
Qed.

Theorem Countable_Nat : Countable Nat.
Proof.
  Countable_solver.
Qed.

Theorem Countable_Tree : Countable Tree.
Proof.
  Countable_solver.
Qed.

Class PropositionalVariables: Type := {
  Var: Type
}.

Inductive expr1 {Sigma: PropositionalVariables}: Type :=
  | andp1 : expr1 -> expr1 -> expr1
  | orp1 : expr1 -> expr1 -> expr1
  | impp1 : expr1 -> expr1 -> expr1
  | falsep1 : expr1
  | varp1 : Var -> expr1.

Arguments expr1 Sigma: clear implicits.

Theorem Countable_expr1 : forall Sigma , Countable Var -> Countable (expr1 Sigma).
Proof.
  intros.
  Time Countable_solver.
Qed.


Theorem Coutable_list : forall A : Type , Countable A -> Countable (list A).
Proof.
  intros.
  Countable_solver. 
Qed.

Class ProgramVariables: Type :={
  BaseP: Type
}.

Inductive program {Sigma: PropositionalVariables}{ProV: ProgramVariables}: Type :=
  | choice: program -> program -> program
  | composition: program -> program -> program
  | iteration: program -> program
  | test: expr -> program
  | basep: BaseP -> program
with
 expr {Sigma: PropositionalVariables} {ProV: ProgramVariables}: Type :=
  | impp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | andp: expr -> expr -> expr
  | falsep : expr
  | boxp: program -> expr -> expr
  | varp : Var -> expr.

Arguments expr Sigma ProV : clear implicits.
Arguments program Sigma ProV : clear implicits.

Theorem Countable_program : forall Sigma ProV, Countable Var -> Countable BaseP -> Countable (expr Sigma ProV).
Proof.
  intros.
Abort.

Inductive simplprogram {Sigma: PropositionalVariables}{ProV: ProgramVariables}: Type :=
  | schoice: simplprogram -> simplprogram -> simplprogram
  | scomposition: simplprogram -> simplprogram -> simplprogram
  | siteration: simplprogram -> simplprogram
  | stest: expr1 Sigma -> simplprogram
  | sbasep: BaseP -> simplprogram.

Arguments simplprogram Sigma ProV : clear implicits.

Theorem Countable_simplprogram : forall Sigma ProV, Countable Var -> Countable BaseP -> Countable (simplprogram Sigma ProV).
Proof.
  intros.
  Time Countable_solver.
Qed.

