Require Export Coq.Relations.Relation_Definitions.

(* The following was RelCompFun in Coq.Classes.RelationPairs and
   respectful_relation in RamifyCoq.lib.Relation_ext. *)

Definition func_dom_relation {A} {B : Type} (R:relation B) (f:A->B) : relation A :=
  fun a a' => R (f a) (f a').

(* The following was RelProd in Coq.Classes.RelationPairs. *)

Definition prod_relation {A : Type} {B : Type} (RA:relation A)(RB:relation B) : relation (A*B) :=
  fun x x' => RA (fst x) (fst x') /\ RB (snd x) (snd x').

Inductive option00_relation {A: Type} (R: relation A): relation (option A):=
| None_None_option00: option00_relation R None None
| Some_Some_option00: forall a b, R a b -> option00_relation R (Some a) (Some b).

Inductive option01_relation {A: Type} (R: relation A): relation (option A):=
| None_None_option01: option01_relation R None None
| None_Some_option01: forall a, option01_relation R None (Some a)
| Some_Some_option01: forall a b, R a b -> option01_relation R (Some a) (Some b).

Inductive option10_relation {A: Type} (R: relation A): relation (option A):=
| None_None_option10: option10_relation R None None
| Some_None_option10: forall a, option10_relation R (Some a) None
| Some_Some_option10: forall a b, R a b -> option10_relation R (Some a) (Some b).

Inductive sum00_relation {A B: Type} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum00_ll a1 a2: RA a1 a2 -> sum00_relation RA RB (inl a1) (inl a2)
  | sum00_rr b1 b2: RB b1 b2 -> sum00_relation RA RB (inr b1) (inr b2).

Inductive sum01_relation {A B: Type} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum01_ll a1 a2: RA a1 a2 -> sum01_relation RA RB (inl a1) (inl a2)
  | sum01_lr a b: sum01_relation RA RB (inl a) (inr b)
  | sum01_rr b1 b2: RB b1 b2 -> sum01_relation RA RB (inr b1) (inr b2).

Inductive sum10_relation {A B: Type} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum10_ll a1 a2: RA a1 a2 -> sum10_relation RA RB (inl a1) (inl a2)
  | sum10_rl a b: sum10_relation RA RB (inr a) (inl b)
  | sum10_rr b1 b2: RB b1 b2 -> sum10_relation RA RB (inr b1) (inr b2).

Definition full_relation (A: Type): relation A := fun _ _ => True.

Definition empty_relation (A: Type): relation A := fun _ _ => False.

Inductive sigT_relation {I: Type} {A: I -> Type} (RA: forall i, relation (A i)): relation (sigT A) :=
  | sigT_relation_intro i a b: RA i a b -> sigT_relation RA (existT _ i a) (existT _ i b).

Inductive sig_relation {A: Type} (P: A -> Prop) (RA: relation A): relation (sig P) :=
  | sig_relation_intro a b Ha Hb: RA a b -> sig_relation P RA (exist _ a Ha) (exist _ b Hb).
