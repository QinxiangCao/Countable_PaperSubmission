Require Import Coq.micromega.Psatz.
Require Import CommonKnowledge.Classes.AbstractEqual.
Require Import CommonKnowledge.Relations.SetoidMappings.
Require Import CommonKnowledge.Relations.Mappings.
Require Import CommonKnowledge.Relations.SetoidCountable.
Require Import CommonKnowledge.Relations.Countable.
Require Import CommonKnowledge.Relations.RelationConstructors.
Require Import CommonKnowledge.IndType.Syntax.
Require Import CommonKnowledge.Relations.IndCountable_AuxDefs.
Require Import List.

Inductive Nat :=
| SNat : bool -> Nat -> Nat
| ONat : Nat.

Inductive Tree :=
| TT3 : nat -> Tree -> Tree -> Tree -> Tree
| TT2 : Tree -> bool -> Tree -> Tree
| TT1 : Tree -> Tree
| TT0 : Tree.

Example ex1: Nat_rect = (Nat_rect: forall P,
                                    rect_type Nat
                                      ((existT _ (Some (bool:Type) :: None :: nil) SNat) ::
                                       (existT _ nil ONat) :: nil) P).
Proof.
  reflexivity.
Qed.

Example ex2: Tree_rect =
            (Tree_rect: forall P,
                          rect_type Tree
                            ((existT _ (Some (nat:Type) :: None :: None :: None :: nil) TT3) ::
                             (existT _ (None :: Some (bool:Type) :: None :: nil) TT2) ::
                             (existT _ (None :: nil) TT1) ::
                             (existT _ nil TT0) :: nil) P).
Proof.
  reflexivity.
Qed.

Definition normtype_clause_equiv (arg: list (option Type)) (ty: Type) (eqty : AbstractEq ty): AbstractEq (normtype_clause arg ty) :=
  (fix normtype_clause_equiv arg: AbstractEq (normtype_clause arg ty) :=
     match arg with
     | nil => (RealEq _)
     | Some T0 :: arg0 => @EqProd (normtype_clause arg0 ty) T0 (normtype_clause_equiv arg0) (RealEq T0) 
     | None :: arg0 => @EqProd (normtype_clause arg0 ty) ty (normtype_clause_equiv arg0) eqty
     end) arg.

Definition normtype_equiv {T} (constrs : ConstrsType T) (ty : Type) (eqty : AbstractEq ty) : 
    AbstractEq (normtype T constrs ty) :=
  (fix normtype_equiv constrs : AbstractEq (normtype T constrs ty) :=
     match constrs with
     | nil => (RealEq _)
     | existT _ arg constr :: constrs0 => @EqSum (normtype_clause arg ty) (normtype T constrs0 ty) (normtype_clause_equiv arg ty eqty) (normtype_equiv constrs0) 
    end) constrs.

Theorem normtype_clause_equiv_Equ : forall arg ty eqty , Equivalence eqty -> @Equivalence (normtype_clause arg ty) (normtype_clause_equiv arg ty eqty).
Proof.
  intros.
  induction arg.
  + simpl. apply RealEqEqu.
  + simpl. destruct a ; simpl ; apply EqProdEqu ; auto.
    apply RealEqEqu. 
Qed.

Theorem normtype_equiv_Equ : forall T constrs ty eqty , Equivalence eqty -> @Equivalence (normtype T constrs ty) (normtype_equiv constrs ty eqty).
Proof.
  intros.
  induction constrs as [ | [arg constr] constrs0] ; simpl in * ; auto.
  - apply RealEqEqu.
  - apply EqSumEqu ; auto.
    apply normtype_clause_equiv_Equ ; auto.
Qed.

Theorem normtype_clause_equiv_IsRealEq : forall arg ty eqty , IsRealEq ty eqty -> IsRealEq (normtype_clause arg ty) (normtype_clause_equiv arg ty eqty).
Proof.
  intros.
  induction arg.
  + simpl. apply RealEq_IsRealEq.
  + simpl. destruct a ; simpl ; apply EqProd_IsRealEq ; auto.
    apply RealEq_IsRealEq. 
Qed.

Theorem normtype_equiv_IsRealEq : forall T constrs ty eqty , IsRealEq ty eqty -> IsRealEq (normtype T constrs ty) (normtype_equiv constrs ty eqty).
Proof.
  intros. 
  induction constrs as [ | [arg constr] constrs0] ; simpl in * ; auto.
  - apply RealEq_IsRealEq.
  - apply EqSum_IsRealEq ; auto.
    apply normtype_clause_equiv_IsRealEq ; auto.
Qed.

Section Pattern_match.

Variables (T: Type).

(*Definition PM_inj := forall constrs rect a b,
  Pattern_match constrs rect a = Pattern_match constrs rect b -> a = b.
*)
Definition PM_inj_1 constrs rect a := forall b,
  pattern_match T constrs rect a = pattern_match T constrs rect b -> a = b.

Lemma nested_inr_eq : forall constrs1_r arg2 constr2 constrs4 x y,
  nested_inr T constrs1_r (_[ arg2, constr2]_ :: constrs4) T x =
  nested_inr T constrs1_r (_[ arg2, constr2]_ :: constrs4) T y ->
  x = y.
Proof.
  intros constrs1_r.
  induction constrs1_r as [| [arg1_r constr1_r] constrs1_r]; intros.
  - simpl in H. inversion H; auto.
  - simpl in *. 
    specialize (IHconstrs1_r arg1_r constr1_r (_[ arg2, constr2 ]_ :: constrs4) (inr x) (inr y) H).
    inversion IHconstrs1_r ; auto.
Qed.

Lemma nested_inr_not_eq : forall constrs1_r arg2 constr2 constrs4 x y,
  nested_inr T constrs1_r (_[ arg2, constr2]_ :: constrs4) T (inl x) =
  nested_inr T constrs1_r (_[ arg2, constr2]_ :: constrs4) T (inr y) ->
  False.
Proof.
  intros.
  apply nested_inr_eq in H.  
  inversion H.
Qed.

(**
  "PM_inj_1_clause _ _ arg constr" says:
    for any a1 a2 ... an, PM_inj_1 (constr a1 a2 ... an).
  In other words,
    for any a1 a2 ... an,
      forall b, PM (constr a1 a2 ... an) = PM b -> constr a1 a2 ... an = b
*)

Definition PM_inj_1_clause
           (constrs : ConstrsType T)
           Trect:
  forall (arg : list (option Type))
         (constr : constr_type arg T)
         (F : normtype_clause arg T -> normtype T constrs T), Prop :=
  fix PM_inj_1_clause (arg : list (option Type)) :
    forall (constr : constr_type arg T)
           (F : normtype_clause arg T -> normtype T constrs T), Prop :=
  match arg as arg0 return 
    forall (constr : constr_type arg0 T)
           (F : normtype_clause arg0 T -> normtype T constrs T), Prop 
  with
  | nil => fun constr F => forall a2:T , F tt = pattern_match T constrs Trect a2 -> constr = a2
  | Some T0 :: arg0 => fun constr F => forall x , PM_inj_1_clause arg0 (constr x) (fun nt => F (nt , x))
  | None :: arg0 => fun constr F => forall x , PM_inj_1_clause arg0 (constr x) (fun nt => F (nt , x))
  end.

(**
  PM_inj_1_clause' extract the inner most "forall a2" of PM_inj_1_clause
  to the outmost position.
*)

Definition PM_inj_1_clause'
           (a2: T)
           (constrs: list (sigT (fun arg => constr_type arg T) ))
           Trect :
  forall (arg : list (option Type))
         (constr: constr_type arg T)
         (F: normtype_clause arg T -> normtype T constrs T), Prop :=
  fix PM_inj_1_clause' (arg : list (option Type)):
    forall (constr: constr_type arg T)
           (F: normtype_clause arg T -> normtype T constrs T), Prop :=
  match arg as arg0 return
    forall (constr: constr_type arg0 T)
      (F: normtype_clause arg0 T -> normtype T constrs T), Prop
  with
  | nil => fun constr F => F tt = pattern_match T constrs Trect a2 -> constr = a2
  | cons (Some T0) arg0 => fun constr F => forall x, PM_inj_1_clause' arg0 (constr x) (fun nt => F (nt, x))
  | cons None arg0 => fun constr F => forall x, PM_inj_1_clause' arg0 (constr x) (fun nt => F (nt, x))
  end.

Lemma PM_inj_1_clause_PM_inj_1_clause': forall constrs Trect arg constr F,
  (forall a2, PM_inj_1_clause' a2  constrs Trect arg constr F) ->
  PM_inj_1_clause constrs Trect arg constr F.
Proof.
  intros.
  induction arg as [ | [ | ]] ; simpl in * ;  auto.
Qed.

(**
  PM_inj_2_clause and PM_inj_2_clause_c describes the situation that x y: T fall into the same branch.
*)

Definition PM_inj_2_clause_nil 
           (constrs: list (sigT (fun arg => constr_type arg T) ))
           (constr1 : T)
           (F1: normtype_clause nil T -> normtype T constrs T) :
  forall (arg : list (option Type))
         (constr : constr_type arg T)
         (F: normtype_clause arg T -> normtype T constrs T), Prop :=
  fix PM_inj_2_clause_nil (arg : list (option Type)):
    forall (constr: constr_type arg T)
           (F: normtype_clause arg T -> normtype T constrs T), Prop :=
  match arg as arg0 return
    forall (constr: constr_type arg0 T)
      (F: normtype_clause arg0 T -> normtype T constrs T), Prop
  with
  | nil => fun constr F => F1 tt = F tt -> constr = constr1
  | cons (Some T0) arg0 => fun constr F => forall x, PM_inj_2_clause_nil arg0 (constr x) (fun nt => F (nt, x))
  | cons None arg0 => fun constr F => forall x, PM_inj_2_clause_nil arg0 (constr x) (fun nt => F (nt, x))
  end.

Definition PM_inj_2_clause
           (constrs: list (sigT (fun arg => constr_type arg T) ))
           (arg1 : list (option Type))
           (constr1 : constr_type arg1 T)
           (F1: normtype_clause arg1 T -> normtype T constrs T) :
  forall (arg : list (option Type))
         (constr: constr_type arg T)
         (F: normtype_clause arg T -> normtype T constrs T), Prop :=
  fix PM_inj_2_clause (arg : list (option Type)):
    forall (constr: constr_type arg T)
           (F: normtype_clause arg T -> normtype T constrs T), Prop :=
  match arg as arg0 return
    forall (constr: constr_type arg0 T)
      (F: normtype_clause arg0 T -> normtype T constrs T), Prop
  with
  | nil => fun constr F => PM_inj_2_clause_nil constrs constr F arg1 constr1 F1 
  | cons (Some T0) arg0 => fun constr F => forall x, PM_inj_2_clause arg0 (constr x) (fun nt => F (nt, x))
  | cons None arg0 => fun constr F => forall x, PM_inj_2_clause arg0 (constr x) (fun nt => F (nt, x))
  end.

Definition PM_inj_2_clause_nil_c 
           (argc : list (option Type))
           (constr1 : constr_type nil T)
           (F1: normtype_clause nil T -> normtype_clause argc T) :
  forall (arg : list (option Type))
         (constr : constr_type arg T)
         (F: normtype_clause arg T -> normtype_clause argc T), Prop :=
  fix PM_inj_2_clause_nil_c (arg : list (option Type)):
    forall (constr: constr_type arg T)
           (F: normtype_clause arg T -> normtype_clause argc T), Prop :=
  match arg as arg0 return
    forall (constr: constr_type arg0 T)
      (F: normtype_clause arg0 T -> normtype_clause argc T) , Prop
  with
  | nil => fun constr F => F1 tt = F tt -> constr = constr1
  | cons (Some T0) arg0 => fun constr F => forall x, PM_inj_2_clause_nil_c arg0 (constr x) (fun nt => F (nt, x))
  | cons None arg0 => fun constr F => forall x, PM_inj_2_clause_nil_c arg0 (constr x) (fun nt => F (nt, x))
  end.

Definition PM_inj_2_clause_c
           (argc arg1 : list (option Type))
           (constr1 : constr_type arg1 T)
           (F1: normtype_clause arg1 T -> normtype_clause argc T) :
  forall (arg : list (option Type))
         (constr: constr_type arg T)
         (F: normtype_clause arg T -> normtype_clause argc T), Prop :=
  fix PM_inj_2_clause_c (arg : list (option Type)):
    forall (constr: constr_type arg T)
           (F: normtype_clause arg T -> normtype_clause argc T), Prop :=
  match arg as arg0 return
    forall (constr: constr_type arg0 T)
      (F: normtype_clause arg0 T -> normtype_clause argc T), Prop
  with
  | nil => fun constr F => PM_inj_2_clause_nil_c argc constr F arg1 constr1 F1 
  | cons (Some T0) arg0 => fun constr F => forall x, PM_inj_2_clause_c arg0 (constr x) (fun nt => F (nt, x))
  | cons None arg0 => fun constr F => forall x, PM_inj_2_clause_c arg0 (constr x) (fun nt => F (nt, x))
  end.


Lemma PM_inj_2_clause_arg_to_constrs : forall constrs argc arg constr F arg1 constr1 F1 F2 ,  
  (forall x y , F2 x = F2 y -> x = y) ->
  PM_inj_2_clause_c argc arg1 constr1 F1 arg constr F ->
  PM_inj_2_clause constrs arg1 constr1 (fun x => F2 (F1 x)) arg constr
  (fun x => F2 (F x)).
Proof.
  intros.
  induction arg as [ | [ | ]] ; simpl in * ; intros;  auto.
  induction arg1 as [ | [ | ]] ; simpl in * ; intros ; auto.
Qed.

(** This lemma "PM_help" unfolds the PM function on the LHS of PM_inj_1 property. *)

Theorem PM_help : forall constrs rect arg constr F , 
  CG_pattern_match_correct T constrs arg constr rect F ->
  PM_inj_1_clause constrs rect arg constr F ->
  rect_clause_type arg T (fun a0 : T => PM_inj_1 constrs rect a0) constr.
Proof.
  unfold CG_pattern_match_correct.
  intros.
  unfold PM_inj_1.
  induction arg as [ | [ | ]] ; simpl in * ; intros.
  - apply H0. rewrite <- H1. auto. 
  - apply IHarg with (F := (fun res => F (res, x0))) ; auto.
  - apply IHarg with (F := (fun res => F (res, x))) ; auto.
Qed.

(** Then we prove the PM_inj_2_clause_c property, which is immediately followed by
    PM_inj_2_clause.

    BEGINNING OF THE PROOF.
*)

Lemma PM_inj_2_clause_correct_c1' : forall arg1 arg2 argc T0 constr1 constr2 F1 F2,
  PM_inj_2_clause_c argc arg1 constr1 F1 arg2 constr2 F2
  -> forall x1 x2, PM_inj_2_clause_c (Some T0 :: argc) arg1 constr1 (fun res => (F1 res , x1)) arg2 constr2 (fun res => (F2 res , x2)).
Proof.
  intros.
  induction arg2 as [ | [ | ]]; simpl in * ; intros ; auto.
  induction arg1 as [ | [ | ]] ; simpl in * ; intros ; auto. 
  inversion H0. auto.
Qed.

Lemma PM_inj_2_clause_correct_c1 : forall arg1 arg2 argc T0 constr1 constr2 F1 F2, 
  (forall x1 y1 x2 y2 , F2 (y1 , x1) = F1 (y2 , x2) -> x1 = x2) ->
  (forall x , PM_inj_2_clause_c argc arg1 (constr1 x) (fun res => F1 (res , x)) arg2 (constr2 x) (fun res => F2 (res , x)))
  -> PM_inj_2_clause_c argc (Some T0 :: arg1) constr1 F1 (Some T0 :: arg2) constr2 F2.
Proof.
  intros.
  induction arg2 as [ | [ | ]] ; simpl in *; intros ; auto.
  - induction arg1 as [ | [ | ]] ; simpl in *; intros; auto.
    + inversion H1.  apply H in H1. subst. auto.
    + apply (IHarg1 (fun x0 => constr1 x0 x1) (fun nt => F1 (fst nt , x1 , snd nt))) ; intros ; eauto ; apply H0.
    + apply (IHarg1 (fun x0 => constr1 x0 x1) (fun nt => F1 (fst nt , x1 , snd nt))) ; intros ; eauto ; apply H0.
  - apply (IHarg2 (fun x => (constr2 x x0)) (fun nt => F2 (fst nt , x0 , snd nt))); intros ; eauto ; apply H0.
  - apply (IHarg2 (fun x => (constr2 x x0)) (fun nt => F2 (fst nt , x0 , snd nt))); intros ; eauto ; apply H0.
Qed.

Lemma PM_inj_2_clause_correct_c2' : forall arg1 arg2 argc constr1 constr2 F1 F2,
  PM_inj_2_clause_c argc arg1 constr1 F1 arg2 constr2 F2
  -> forall x1 x2, PM_inj_2_clause_c (None :: argc) arg1 constr1 (fun res => (F1 res , x1)) arg2 constr2 (fun res => (F2 res , x2)).
Proof.
  intros.
  induction arg2 as [ | [ | ]]; simpl in * ; intros ; auto.
  induction arg1 as [ | [ | ]] ; simpl in * ; intros ; auto. 
  inversion H0. auto.
Qed.

Lemma PM_inj_2_clause_correct_c2 : forall arg1 arg2 argc constr1 constr2 F1 F2, 
  (forall x1 y1 x2 y2 , F2 (y1 , x1) = F1 (y2 , x2) -> x1 = x2) ->
  (forall x, PM_inj_2_clause_c argc arg1 (constr1 x) (fun res => F1 (res , x)) arg2 (constr2 x) (fun res => F2 (res , x)))
  -> PM_inj_2_clause_c argc (None :: arg1) constr1 F1 (None :: arg2) constr2 F2.
Proof.
  intros.
  induction arg2 as [ | [ | ]] ; simpl in *; intros ; auto.
  - induction arg1 as [ | [ | ]] ; simpl in *; intros; auto.
    + inversion H1.  apply H in H1. subst. auto.
    + apply (IHarg1 (fun x0 => constr1 x0 x1) (fun nt => F1 (fst nt , x1 , snd nt))) ; intros ; eauto ; apply H0.
    + apply (IHarg1 (fun x0 => constr1 x0 x1) (fun nt => F1 (fst nt , x1 , snd nt))) ; intros ; eauto ; apply H0.
  - apply (IHarg2 (fun x => (constr2 x x0)) (fun nt => F2 (fst nt , x0 , snd nt))); intros ; eauto ; apply H0.
  - apply (IHarg2 (fun x => (constr2 x x0)) (fun nt => F2 (fst nt , x0 , snd nt))); intros ; eauto ; apply H0.
Qed.

Lemma PM_inj_2_clause_correct2 : forall constrs arg constr F ,
  (forall x y , F x = F y -> x = y) ->
 PM_inj_2_clause constrs arg constr F arg constr F.
Proof.
  intros.
  apply PM_inj_2_clause_arg_to_constrs with (argc := arg) ; auto.
  clear F constrs H.
  induction arg as [ | [ | ]].
  - simpl. auto.
  - apply PM_inj_2_clause_correct_c1 ; intros.
    + inversion H. auto.
    + apply PM_inj_2_clause_correct_c1' ; auto. 
  - apply PM_inj_2_clause_correct_c2 ; intros.
    + inversion H. auto.
    + apply PM_inj_2_clause_correct_c2' ; auto.
Qed.

(** END OF THE PROOF. *)

(* From PM_inj_2_clause to rect_clause_type PM_inj_1_clause' is just unfolding the RHS *)

Lemma PM_inj_1_clause'_rect_clause : forall constrs arg constr F arg1 constr1 F1 rect,
  CG_pattern_match_correct T constrs arg1 constr1 rect F1 ->
  PM_inj_2_clause constrs arg constr F arg1 constr1 F1 -> 
  rect_clause_type arg1 T (fun a0 : T => PM_inj_1_clause' a0 constrs rect arg constr F) constr1.
Proof.
  unfold CG_pattern_match_correct.
  intros.
  induction arg1 as [ | [ | ]] ; simpl in * ; intros ;  auto.
  - simpl in *. induction arg as [ | [ | ]] ; simpl in * ; intros ; auto.
    apply H0. rewrite H1. symmetry; apply H.
  - apply IHarg1 with (F1 := (fun res => F1 (res,x0))) ; auto.
  - apply IHarg1 with (F1 := (fun res => F1 (res,x))) ; auto. 
Qed.

(* when b appears on a righter branch *)

Lemma PM_inj_1_clause'_correct_rec1 : forall a constrs1 constrs3a constrs3b arg constr rect rect1
  (G : normtype T (rev_append (constrs3a ++ _[ arg, constr ]_ :: constrs1) constrs3b) T -> 
       normtype T (rev_append (_[ arg, constr ]_ :: constrs1) (rev_append constrs3a constrs3b)) T)
  (rect_correctness : Sol1.rect_correct T (rev_append (_[ arg, constr ]_ :: constrs1) (rev_append constrs3a constrs3b)) rect)
  (rect_correctness1 : Sol1.rect_correct T (rev_append (constrs3a ++ _[ arg, constr ]_ :: constrs1) constrs3b) rect1)
  (Prop_rect : forall x, pattern_match T (rev_append (_[ arg, constr ]_ :: constrs1) (rev_append constrs3a constrs3b)) (rect _) x = 
    G (pattern_match T (rev_append (constrs3a ++ _[ arg, constr ]_ :: constrs1) constrs3b) (rect1 _) x))
  (G_prop : forall x x1, nested_inr_oo_inl T constrs1 arg constr (rev_append constrs3a constrs3b) x = G (nested_inr T (constrs3a ++ _[ arg, constr ]_ :: constrs1) constrs3b T x1) -> False)
  (Trect : rect_type T constrs3b (fun a => PM_inj_1_clause' a (rev_append (_[ arg, constr ]_ :: constrs1) (rev_append constrs3a constrs3b)) (rect _) arg constr (nested_inr_oo_inl T constrs1 arg constr (rev_append constrs3a constrs3b)))),
  PM_inj_1_clause' a (rev_append (_[ arg, constr ]_ :: constrs1) (rev_append constrs3a constrs3b)) (rect _) arg constr (nested_inr_oo_inl T constrs1 arg constr (rev_append constrs3a constrs3b)).
Proof.
  intros.
  revert dependent constrs3a.
  induction constrs3b as [ | [ arg3 constr3] constrs3] ; simpl in * ; intros;  auto.
  apply (IHconstrs3 (_[ arg3, constr3 ]_ :: constrs3a) rect rect1 G);  auto ; try (intros ; apply (G_prop x (inr x1)) ; auto).
  apply Trect.
  clear IHconstrs3. clear Trect.
  pose proof (pattern_match_correctness _ _ _ _ _ _ rect_correctness).
  pose proof (pattern_match_correctness _ _ _ _ _ _ rect_correctness1).
  clear rect_correctness rect_correctness1.
  rewrite <- pattern_match_correct_equiv in H, H0.
  unfold CG_pattern_match_correct in H, H0.
  assert (forall x x1 , nested_inr_oo_inl T constrs1 arg constr
                        (rev_append constrs3a (_[ arg3, constr3 ]_ :: constrs3)) x = G (nested_inr_oo_inl T (constrs3a ++ _[ arg, constr ]_ :: constrs1) arg3 constr3 constrs3 x1) -> False).
  { intros. apply (G_prop x (inl x1)). auto. }
  set (F := nested_inr_oo_inl T constrs1 arg constr
                        (rev_append constrs3a (_[ arg3, constr3 ]_ :: constrs3))) in *.
  clearbody F.
  set (F1 := nested_inr_oo_inl T (constrs3a ++ _[ arg, constr ]_ :: constrs1) arg3 constr3 constrs3) in *.
  clearbody F1.
  clear G_prop.
  set (constrs := (rev_append constrs1
              (_[ arg, constr ]_
               :: rev_append constrs3a
                    (_[ arg3, constr3 ]_ :: constrs3)))) in *.
  set (constrs' := (rev_append
             (constrs3a ++ _[ arg, constr ]_ :: constrs1)
             (_[ arg3, constr3 ]_ :: constrs3))) in *.
  clearbody constrs constrs'.
  clear constrs1 constrs3 constrs3a.
  induction arg3 as [ | [ | ]] ; simpl in * ; intros ; auto.
  - induction arg as [ | [ | ]] ; simpl in * ; intros ; auto.
    + exfalso.
      apply (H1 tt tt).
      rewrite H2. rewrite Prop_rect.
      rewrite H0. auto.
    + apply (IHarg (constr x) (fun res => F (res , x))) ; auto.
      intros. apply H1 in H2 ; auto.
    + apply (IHarg (constr x) (fun res => F (res , x))) ; auto.
      intros. apply H1 in H2 ; auto.
  - apply (IHarg3 (constr3 x0) (fun res => F1 (res , x0))) ; auto.
    intros. apply H1 in H2 ; auto.
  - apply (IHarg3 (constr3 x) (fun res => F1 (res , x))) ; auto.
    intros. apply H1 in H2 ; auto.
Qed.

Definition is_id constrs1 constrs2 constrs3 arg constr
    (G : normtype T (rev_append constrs1 (constrs2 ++ _[arg,constr]_ :: constrs3)) T -> 
       normtype T (rev_append (rev_append constrs2 constrs1) (_[ arg, constr]_ :: constrs3)) T) : Prop.
  revert dependent constrs1.
  induction constrs2 as [ | [arg1 constr1] constrs2] ; intros.
  + apply (forall x , G x = x).
  + apply (IHconstrs2 (_[ arg1 , constr1]_ :: constrs1) G) .
Defined. 

(* case analysis for when b appears on a lefter branch, and use the conclusion about b appears on a righter branch above *)

Theorem PM_inj_1_clause'_correct_rec : forall a constrs1 constrs2 constrs3 arg constr rect rect1
  (G : normtype T (rev_append constrs1 (constrs2 ++ _[arg,constr]_ :: constrs3)) T -> 
       normtype T (rev_append (rev_append constrs2 constrs1) (_[ arg, constr]_ :: constrs3)) T)
  (rect_correctness : Sol1.rect_correct T (rev_append (rev_append constrs2 constrs1) (_[ arg, constr]_ :: constrs3)) rect)
  (rect_correctness1 : Sol1.rect_correct T (rev_append constrs1 (constrs2 ++ _[arg,constr]_ :: constrs3)) rect1) 
  (Prop_rect : forall x, pattern_match T (rev_append (rev_append constrs2 constrs1) (_[ arg, constr]_ :: constrs3)) (rect _) x = G (pattern_match T (rev_append constrs1 (constrs2 ++ _[arg,constr]_ :: constrs3)) (rect1 _) x))
  (G_prop1 : is_id constrs1 constrs2 constrs3 arg constr G)
  (G_prop2 : forall x y , G x = G y -> x = y)
  (Trect_rev : rect_type_rev T constrs1 constrs2 (_[ arg, constr]_ :: constrs3) (fun a => PM_inj_1_clause' a (rev_append (rev_append constrs2 constrs1) (_[ arg, constr]_ :: constrs3)) (rect _) arg constr (nested_inr_oo_inl T (rev_append constrs2 constrs1) arg constr constrs3))), 
  PM_inj_1_clause' a (rev_append (rev_append constrs2 constrs1) (_[ arg, constr]_ :: constrs3)) (rect _) arg constr (nested_inr_oo_inl T (rev_append constrs2 constrs1) arg constr constrs3).
Proof.
  intros.
  revert a.
  revert dependent constrs2. 
  induction constrs1 as [| [arg1 constr1] constrs1] ; intros ; simpl in * ; auto.
  - apply (PM_inj_1_clause'_correct_rec1 a (rev_append constrs2 nil) nil constrs3 arg constr rect rect (fun res => res)) ; auto .
    * intros. simpl in *.
      unfold nested_inr_oo_inl in H. 
      apply nested_inr_not_eq in H. auto.
    * apply Trect_rev. clear Trect_rev.
      apply PM_inj_1_clause'_rect_clause with (F1 := nested_inr_oo_inl T (rev_append constrs2 nil) arg constr constrs3).
      + rewrite pattern_match_correct_equiv.
        apply pattern_match_correctness; auto.
      + apply PM_inj_2_clause_correct2.
        intros.
        unfold nested_inr_oo_inl in H. apply nested_inr_eq in H . inversion H ; auto. 
  - apply (IHconstrs1 (_[ arg1, constr1]_ :: constrs2) rect rect1 G);  auto. 
    apply Trect_rev.
    clear Trect_rev IHconstrs1.
    pose proof (pattern_match_correctness _ _ _ _ _ _ rect_correctness).
    pose proof (pattern_match_correctness _ _ _ _ _ _ rect_correctness1).
    clear rect_correctness rect_correctness1.
    assert (forall x x1, nested_inr_oo_inl T (rev_append constrs2 (_[ arg1, constr1 ]_ :: constrs1)) arg constr constrs3 x = G (nested_inr_oo_inl T constrs1 arg1 constr1 (constrs2 ++ _[ arg, constr]_ :: constrs3 ) x1) -> False).
    {  intros. 
       unfold nested_inr_oo_inl in H1.
       clear - G_prop1 G_prop2 H1.
       assert (exists y , nested_inr T (rev_append constrs2 (_[ arg1, constr1 ]_ :: constrs1))
       (_[ arg, constr ]_ :: constrs3) T (inl x) = G
       (nested_inr T constrs1 (_[ arg1, constr1 ]_ :: constrs2 ++ _[ arg, constr ]_ :: constrs3)
          T (inr y))).
       { 
          clear H1 x1. revert dependent constrs1. revert dependent arg1.
          induction constrs2 as [ | [ arg2' constr2' ] constrs2'] ; simpl in * ; intros ; auto.
          + exists (inl x). auto.
          + specialize (IHconstrs2' arg2' constr2' (_[arg1,constr1]_::constrs1) G G_prop1 G_prop2).
            destruct IHconstrs2'.
            exists (inr x0).
            auto.
       }
       destruct H. rewrite H in H1. apply G_prop2 in H1. apply nested_inr_eq in H1. inversion H1.
    }
    rewrite <- pattern_match_correct_equiv in H, H0.
    set (F1 := nested_inr_oo_inl T constrs1 arg1 constr1 (constrs2 ++ _[ arg, constr]_ :: constrs3 )) in *.
    set (F := nested_inr_oo_inl T (rev_append constrs2 (_[ arg1, constr1 ]_ :: constrs1)) arg constr constrs3) in *.
    clearbody F F1.
    clear G_prop1 G_prop2.
    set (constrs := rev_append
            (rev_append constrs2
               (_[ arg1, constr1 ]_ :: constrs1))
            (_[ arg, constr ]_ :: constrs3)) in *.
    set (constrs' := rev_append constrs1
             (_[ arg1, constr1 ]_
              :: constrs2 ++ _[ arg, constr ]_ :: constrs3)) in *.
    clearbody constrs constrs'.
    unfold CG_pattern_match_correct in *.
    clear constrs1 constrs3 constrs2.
    induction arg1 as [ | [ | ]] ; simpl in * ; intros ; auto.
    * induction arg as [ | [ | ]] ; simpl in * ; intros ; auto.
      + exfalso.
        apply (H1 tt tt).
        rewrite H2. rewrite Prop_rect.
        rewrite H0. auto.
      + apply (IHarg (constr x) (fun res => F (res , x))) ; auto.
        intros. apply H1 in H2 ; auto.
      + apply (IHarg (constr x) (fun res => F (res , x))) ; auto.
        intros. apply H1 in H2 ; auto.
    * apply (IHarg1 (constr1 x0) (fun res => F1 (res , x0))) ; auto.
      intros. apply H1 in H2 ; auto.
    * apply (IHarg1 (constr1 x) (fun res => F1 (res , x))) ; auto.
      intros. apply H1 in H2 ; auto.
Qed.

(* Merging conclusions from all branches together. While filling arguments of Trect,
   need to proof rect_clause_type PM_inj_1, proved by PM_inj_1_clause, which is proved above. *)
Theorem PM_inj_correct_rec: forall a constrs1 constrs234 rect  
  (rect_correctness : Sol1.rect_correct T (rev_append constrs1 constrs234) rect)
  (Trect_axiom : forall P , rect_type T (rev_append constrs1 constrs234) P)
  (Trect: rect_type T constrs234 (fun a => PM_inj_1 (rev_append constrs1 constrs234) (rect _) a)),
  PM_inj_1 (rev_append constrs1 constrs234) (rect _) a. 
Proof.
  intros.
  revert a.
  revert dependent constrs1.
  induction constrs234 as [| [arg2 constr2] constrs34] ; intros.
  - simpl in *. auto.
  - apply (IHconstrs34  (_[ arg2 , constr2 ]_ :: constrs1) rect rect_correctness); auto. 
    simpl in Trect. apply Trect.
    clear IHconstrs34 Trect.
    apply PM_help with (F := (fun res => nested_inr T constrs1 (_[ arg2, constr2 ]_ :: constrs34) T (inl res))).
    + rewrite pattern_match_correct_equiv.
      apply pattern_match_correctness; auto.
    + apply PM_inj_1_clause_PM_inj_1_clause' ; intros ; auto.
      apply (PM_inj_1_clause'_correct_rec a2 constrs1 nil constrs34 arg2 constr2 rect rect (fun res => res)) ; auto.
      * hnf. auto. 
      * apply rect_arrow_rect_rev. auto.
Qed.

Theorem PM_inj_correct: forall a constrs rect
  (rect_correctness : Sol1.rect_correct T constrs rect) ,
  PM_inj_1 constrs (rect _) a.
Proof.
  intros.
  apply (PM_inj_correct_rec a nil constrs rect rect_correctness) ; auto.
Qed.

End Pattern_match.

Program Definition injection_T T (constrs : ConstrsType T) rect
  (rect_correctness : Sol1.rect_correct T constrs rect) : 
                                    @SetoidMappings.injection T (normtype T constrs T) 
                                  (RealEq T) (normtype_equiv constrs T (RealEq T)) :=
  SetoidMappings.Build_injection _ _ (fun a b => (normtype_equiv constrs T (RealEq T)) b (pattern_match T constrs (rect _) a)) _ _ _ _ .
Next Obligation.
  hnf. intros. hnf. intros.
  rewrite H. 
  pose proof (normtype_equiv_Equ T constrs T (RealEq T) (RealEqEqu T)).
  destruct H1.
  split ; intros.
  - apply Equivalence_Transitive with x0 ; auto.
  - apply Equivalence_Transitive with y0 ; auto.
Qed.
Next Obligation.
  hnf. intros. 
  exists (pattern_match T constrs (rect _) a).
  pose proof (normtype_equiv_Equ T constrs T (RealEq T) (RealEqEqu T)).
  apply H.
Qed.
Next Obligation.
  hnf. intros.
  pose proof (normtype_equiv_Equ T constrs T (RealEq T) (RealEqEqu T)).
  destruct H1.  
  apply Equivalence_Transitive with (pattern_match T constrs (rect _) a) ; auto.
Qed.
Next Obligation.
  hnf. intros. 
  apply normtype_equiv_IsRealEq in H ; try (apply RealEq_IsRealEq).
  apply normtype_equiv_IsRealEq in H0 ; try (apply RealEq_IsRealEq).
  subst b.
  pose proof PM_inj_correct T a1 constrs rect rect_correctness ; auto.
Qed.

Inductive Forall_type (A : Type) (P : A -> Type) : list A -> Type :=
  | Forall_type_nil : @Forall_type A P (@nil A)
  | Forall_type_cons : forall (x : A) (l : list A),
                  P x -> @Forall_type A P l -> @Forall_type A P (x :: l).

Section countable.

Local Existing Instances RealEqEqu EqSigEqu.

Variable (T: Type).
Variable (constrs: ConstrsType T).
Variable (Trect: forall P, rect_type T constrs P). 
Variable (rect_correctness : Sol2.rect_correct T constrs Trect).

Definition option_Countable (X: option Type) :=
  match X with
  | Some T0 => Countable T0
  | _ => unit
  end.
   
Lemma Countable_arg : forall arg T , @Forall_type (option Type) option_Countable arg -> Countable T -> Countable (normtype_clause arg T).
Proof.
  intros.
  induction arg ; simpl ; solve_Countable.
  destruct a ; simpl ; solve_Countable ; auto ; try (apply IHl); 
  inversion X ; subst ; auto.
Qed.  

Lemma Countable_constr : forall T1 constrs0 T, ((@Forall_type (sigT (fun arg => constr_type arg T1)) 
   (fun s =>(@Forall_type (option Type) option_Countable) (projT1 s ))) constrs0) -> Countable T -> Countable 
(normtype T1 constrs0 T).
Proof.
  intros.
  induction constrs0 as [ | [arg constr] constrs0]; simpl in *; solve_Countable.
  - apply void_Countable. auto.
  - apply Countable_arg ; auto.
    inversion X ; auto.
  - apply IHconstrs0. inversion X ; auto.
Qed.

Lemma SetoidCountable_arg : forall arg T eqty (equty : Equivalence eqty), @Forall_type (option Type) option_Countable arg -> 
                            @SetoidCountable.Countable T eqty -> 
                            @SetoidCountable.Countable (normtype_clause arg T) (normtype_clause_equiv arg T eqty).
Proof.
  intros.
  induction arg ; simpl ; SetoidCountable.solve_Countable.
  destruct a ; simpl ; apply (@SetoidCountable.prod_Countable _ _ _ _ (@normtype_clause_equiv_Equ _ _ _ _ ) _);
  try (apply IHarg; inversion X ; auto) ; auto.
  apply Countable_SetoidCountable.
  inversion X. auto.
Qed.  

Lemma SetoidCountable_constr : forall T1 T constrs0 eqty (equty : Equivalence eqty), 
    ((@Forall_type (sigT (fun arg => constr_type arg T1)) 
   (fun s =>(@Forall_type (option Type) option_Countable) (projT1 s ))) constrs0) -> 
    @SetoidCountable.Countable T eqty -> 
    @SetoidCountable.Countable (normtype T1 constrs0 T) (normtype_equiv constrs0 T eqty).
Proof.
  intros.
  induction constrs0 as [ | [arg constr] constrs0] ; simpl in *; SetoidCountable.solve_Countable.
  - apply void_Countable. auto.
  - apply (@SetoidCountable.sum_Countable _ _ _ _ (@normtype_clause_equiv_Equ _ _ _ _) (@normtype_equiv_Equ _ _ _ _ _)) ; auto.
    * apply SetoidCountable_arg ; auto.
      inversion X ; auto.
    * apply IHconstrs0. inversion X ; auto.
Qed.

Definition small_T (n: nat): Type := {x: T | rank T constrs (Trect (fun _ => nat)) x < n}.

Lemma smallEqu : forall n , @Equivalence (small_T n) (fun x1 y1 : small_T n => RealEq T
     (@proj1_sig T (fun x2 : T => rank T constrs (Trect (fun _ : T => nat)) x2 < n) x1)
     (@proj1_sig T (fun x2 : T => rank T constrs (Trect (fun _ : T => nat)) x2 < n) y1)).
Proof.
  intros.
  split ; hnf ; intros.
  - apply RealEqEqu.
  - rewrite H. reflexivity.
  - rewrite H. auto.
Qed.

Lemma EqSig_lemma : forall (n : nat) (x y : small_T n), (@EqSig _ _ (RealEq _)) x y <-> proj1_sig x = proj1_sig y.
Proof.
  intros.
  split ; intros.
  - inversion H. auto.
  - destruct x , y. 
    hnf. simpl. split. auto.
Qed.

Definition inj_n (n : nat) (X : small_T (S n)) : normtype T constrs (small_T n)
 := let (t, H) := X in pattern_match_DT n T constrs Trect rect_correctness t H.

Theorem normtype_equiv_map_H_clause : forall (H : T -> Prop) arg x y , normtype_clause_equiv arg ({x : T | H x }) (@EqSig _ _ (RealEq _)) x y <-> normtype_clause_map arg _ _ (@proj1_sig _ _) x = normtype_clause_map arg _ _ (@proj1_sig _ _) y.
Proof.
  intros.
  clear constrs Trect rect_correctness.
  induction arg as [ | [ | ]] ; split ; destruct x , y ; intros ; simpl in * ; auto ; inversion H0 ; simpl in * ; subst.
  - destruct H2. rewrite (IHarg n n0) in H1.  rewrite H1. auto.
  - rewrite <- IHarg in H2. split ; simpl ; auto. reflexivity.
  - destruct H2. destruct H2. simpl. rewrite (IHarg n n0) in H1. rewrite H1. auto.
  - rewrite <- IHarg in H2. split ; simpl in *; destruct s , s0 ; simpl in * ; auto.
    split. auto. 
Qed.

Theorem normtype_equiv_map_H : forall (H : T -> Prop) x y , normtype_equiv constrs ({x : T | H x }) (@EqSig _ _ (RealEq _)) x y <-> normtype_map T constrs _ _ (@proj1_sig _ _) x = normtype_map T constrs _ _ (@proj1_sig _ _) y.
Proof.
  intros. clear Trect rect_correctness.
  induction constrs as [ | [ arg constr] constrs0] ; destruct x , y ; split ; intros ; simpl in * ; inversion H0 ; subst ; auto.
  - rewrite (normtype_equiv_map_H_clause H arg n n0) in H3. rewrite H3. auto.
  - rewrite <- (normtype_equiv_map_H_clause H arg n n0) in H2. left. auto.
  - rewrite (IHconstrs0 n n0) in H3. rewrite H3. auto.
  - rewrite <- IHconstrs0 in H2. right. auto.
Qed. 

Theorem normtype_equiv_map_small (n : nat) : forall x y , normtype_equiv constrs (small_T n) (@EqSig _ _ (RealEq _)) x y <-> normtype_map T constrs _ _ (@proj1_sig _ _) x = normtype_map T constrs _ _ (@proj1_sig _ _) y.
Proof.
  intros. apply normtype_equiv_map_H.
Qed.

Program Definition injection_n (n : nat):
  @SetoidMappings.injection
    (small_T (S n))
    (normtype T constrs (small_T n)) 
    (@EqSig _ _ (RealEq _ ))
    (normtype_equiv constrs (small_T n) (@EqSig _ _ (RealEq _))) :=
  SetoidMappings.Build_injection
    _ _
    (fun a b =>
       normtype_equiv constrs (small_T n) (@EqSig _ _ (RealEq _)) (inj_n n a) b)
    _ _ _ _ .
Next Obligation.
  hnf. intros. hnf. intros.
  split ; intros.
  - apply normtype_equiv_Equ with x0 ; try (apply EqSigEqu ;  apply RealEqEqu) ; auto.
    apply normtype_equiv_Equ with (inj_n n x); try (apply EqSigEqu ;  apply RealEqEqu) ; auto.
    apply normtype_equiv_map_small. unfold inj_n in *. destruct x , y ; subst ; simpl in *.
    repeat rewrite <- DT_pattern_match_correct.
    inversion H. subst. hnf in H4. subst. reflexivity.
  - apply normtype_equiv_Equ with y0 ; try (apply EqSigEqu ;  apply RealEqEqu) ; auto.
    apply normtype_equiv_Equ with (inj_n n y); try (apply EqSigEqu ;  apply RealEqEqu) ; auto.
    +  apply normtype_equiv_map_small. unfold inj_n in *. destruct x , y ; subst ; simpl in *.
    repeat rewrite <- DT_pattern_match_correct.
    inversion H. subst. hnf in H4. subst. reflexivity.
    + apply normtype_equiv_Equ ; try (apply EqSigEqu ;  apply RealEqEqu) ; auto.
Qed.
Next Obligation.
  hnf. intros. exists (inj_n n a). 
  apply normtype_equiv_Equ. apply EqSigEqu. apply RealEqEqu.
Qed.
Next Obligation.
  hnf. intros.
  apply normtype_equiv_Equ with (inj_n n a) ; try (apply EqSigEqu ;  apply RealEqEqu) ; auto.
  apply normtype_equiv_Equ ; try (apply EqSigEqu ;  apply RealEqEqu) ; auto.
Qed.
Next Obligation.
  hnf. intros. destruct a1, a2. simpl in *. split.
  apply normtype_equiv_map_small in H.
  apply normtype_equiv_map_small in H0.
  rewrite <- H in H0. clear H.
  repeat rewrite <- DT_pattern_match_correct in H0.
  apply PM_inj_correct in H0 ; hnf ; auto.
  apply rect_correctness_equiv ; auto.
Qed.

Hypothesis (axiom_forall : (@Forall_type (sigT (fun arg => constr_type arg T)) 
   (fun s =>(@Forall_type (option Type) option_Countable) (projT1 s ))) constrs).

Theorem Countable_T: Countable T.
Proof.
  assert (smallEqu: forall n,
            @Equivalence
              (small_T n)
              (@EqSig T (fun x => rank T constrs (Trect _) x < n) (RealEq T))).
  { intros. apply EqSigEqu. apply RealEqEqu. }
  assert (forall n,
            @SetoidCountable.Countable (small_T n) (@EqSig _ _ (RealEq _))).
  { 
    intros. induction n.
    - apply SetoidCountable.void_Countable.
      intros [? ?].
      lia.
    - refine (@SetoidCountable.injection_Countable _
               (normtype T constrs (small_T n)) (@EqSig _ _ (RealEq _)) 
               (normtype_equiv constrs (small_T n) (@EqSig _ _ (RealEq _)))
               _ _ _ _).
      + apply normtype_equiv_Equ. apply smallEqu.
      + apply injection_n.
      + apply (SetoidCountable_constr T (small_T n) constrs); auto.
  }
  apply SetoidCountable_Countable.
  apply (@SetoidCountable.injection_Countable
           _
           (sigT (fun n => small_T n))
           _
           (@EqSigT _ _ (fun _ => (@EqSig _ _ (RealEq _))))
           _
           _).
  - apply (inject_extra_attr _ _
             (fun a => S (rank T constrs (Trect (fun _ => nat)) a))
             (fun a b => rank T constrs (Trect (fun _ => nat)) a < b)).
    intros; lia.
  - SetoidCountable.solve_Countable; auto.
Qed.

End countable.


