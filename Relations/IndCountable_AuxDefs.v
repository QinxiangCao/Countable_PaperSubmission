Require Import Coq.micromega.Psatz.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import CommonKnowledge.IndType.Syntax.

Fixpoint rank_para_rec T arg s: forall constr, rect_clause_type arg T (fun _ => nat) constr :=
  match arg with
  | nil => fun _ => S s
  | Some A :: arg0 => fun constr a => rank_para_rec T arg0 s (constr a)
  | None :: arg0 => fun constr x rank_x => rank_para_rec T arg0 (s + rank_x) (constr x)
  end.

Definition rank_para T arg constr: rect_clause_type arg T (fun _ => nat) constr :=
  rank_para_rec T arg O constr.

Definition rank T constrs rect: T -> nat :=
  apply_rect T (fun _ _ => nat) constrs (fun constrs1 arg2 constr2 constrs3 => rank_para T arg2 constr2) rect.

Definition normtype_clause (arg: list (option Type)) (ty: Type): Type :=
  (fix normtype_clause arg: Type :=
     match arg with
     | nil => unit
     | Some T0 :: arg0 => (normtype_clause arg0 * T0)%type
     | None :: arg0 => (normtype_clause arg0 * ty)%type
     end) arg.

Definition normtype T (constrs: ConstrsType T) ty: Type :=
  (fix normtype constrs: Type :=
     match constrs with
     | nil => False
     | existT _ arg constr :: constrs0 =>
         (normtype_clause arg ty + normtype constrs0)%type
     end) constrs.

Fixpoint nested_inr T (constrs1 constrs23: ConstrsType T) ty:
  normtype T constrs23 ty -> normtype T (rev_append constrs1 constrs23) ty :=
  match constrs1 with
  | nil => fun x => x
  | existT _ arg1b constr1b :: constrs1a =>
      fun x => nested_inr T constrs1a (_[arg1b, constr1b]_ :: constrs23) ty (inr x)
  end.

Definition nested_inr_oo_inl T constrs1 arg2 constr2 constrs3:
  normtype_clause arg2 T ->
  normtype T (rev_append constrs1 (_[ arg2 , constr2]_ :: constrs3)) T :=
  fun x => nested_inr T constrs1 (_[ arg2, constr2]_ :: constrs3) T (inl x).

Section pattern_match_para_rec.

Variable T: Type.
Variable constrs: ConstrsType T.

Fixpoint pattern_match_para_rec arg:
  forall constr: constr_type arg T,
    (normtype_clause arg T -> normtype T constrs T) ->
    rect_clause_type arg T (fun _ => normtype T constrs T) constr :=
  match arg with
  | nil =>
      fun constr F => F tt
  | Some A :: arg0 =>
      fun constr F a =>
        pattern_match_para_rec arg0 (constr a) (fun x => F (x, a))
  | None :: arg0 =>
      fun constr F a _ =>
        pattern_match_para_rec arg0 (constr a) (fun x => F (x, a))
  end.

End pattern_match_para_rec.

Definition pattern_match_para
           T
           (constrs1: ConstrsType T)
           arg2 constr2
           (constrs3: ConstrsType T):
           rect_clause_type arg2 T (fun _ => normtype T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) T) constr2
:=
  pattern_match_para_rec
    T
    (rev_append constrs1 (_[arg2, constr2]_ :: constrs3))
    arg2
    constr2
    (nested_inr_oo_inl T constrs1 arg2 constr2 constrs3).

Definition pattern_match T constrs rect: T -> normtype T constrs T :=
  apply_rect T (fun constrs _ => normtype T constrs T) constrs (pattern_match_para T) rect.

Definition rank_correct T constrs rect arg constr: Prop :=
  rect_correct_clause T (fun _ => nat) (rank T constrs rect) arg constr (rank_para T arg constr).

Lemma rank_correctness: forall T constrs rect arg constr,
  List.In (_[arg, constr]_) constrs ->
  Sol1.rect_correct T constrs rect ->
  rank_correct T constrs (rect (fun _ => nat)) arg constr.
Proof.
  intros.
  unfold Sol1.rect_correct in H0.
  specialize (H0 (fun _ _ => nat) (fun _ arg constr _ => rank_para T arg constr)).
  unfold Sol1.apply_rect_correct in H0.
  change (apply_rect T (fun _ _ => nat) constrs (fun _ arg constr _ => rank_para T arg constr) (rect (fun _ => nat))) with (rank T constrs (rect (fun _ => nat))) in H0.
  unfold rank_correct.
  set (RANK := rank T constrs (rect (fun _ : T => nat))) in H0 |- *.
  clearbody RANK.
  set (constrs1 := @nil (sigT (fun arg => constr_type arg T))) in H0.
  set (constrs2 := constrs) in H, H0.
  clearbody constrs1 constrs2.
  clear constrs rect.
  revert dependent constrs1.
  induction constrs2; intros; [simpl in H; inversion H |].
  simpl in H; destruct H.
  + subst a.
    clear IHconstrs2.
    destruct H0 as [? _].
    auto.
  + destruct a as [arg' constr'].
    apply (IHconstrs2 H (_[arg', constr']_ :: constrs1)); clear IHconstrs2.
    destruct H0 as [_ ?].
    auto.
Qed.

Definition CG_pattern_match_correct T constrs arg constr rect F : Prop :=
  rect_correct_clause
    T
    (fun _ => normtype T constrs T)
    (pattern_match T constrs rect)
    arg
    constr
    (pattern_match_para_rec T constrs arg constr F).

Definition pattern_match_correct T constrs1 arg2 constr2 constrs3 rect: Prop :=
  rect_correct_clause
    T
    (fun _ => normtype T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) T)
    (pattern_match T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) rect)
    arg2
    constr2
    (pattern_match_para T constrs1 arg2 constr2 constrs3).

Lemma pattern_match_correct_equiv: forall T constrs1 arg2 constr2 constrs3 rect,
  CG_pattern_match_correct
    T
    (rev_append constrs1 (_[arg2, constr2]_ :: constrs3))
    arg2 constr2 rect
    (nested_inr_oo_inl T constrs1 arg2 constr2 constrs3) =
  pattern_match_correct T constrs1 arg2 constr2 constrs3 rect.
Proof.
  intros.
  reflexivity.
Qed.

Lemma pattern_match_correctness : forall T constrs1 arg2 constr2 constrs3 rect,
  Sol1.rect_correct T (rev_append constrs1 (_[arg2,constr2]_ :: constrs3)) rect ->
  pattern_match_correct T constrs1 arg2 constr2 constrs3 (rect _).
Proof.
  intros. 
  pose proof (Sol1_rect_correct_lemma _ _ _ _ _ _ H).
  specialize (H0 (fun constrs _ => normtype T constrs T) (pattern_match_para T)).
  destruct H0 as [ ? _ ].
  exact H0.
Qed.

Fixpoint partial_rank_equiv T (RANK: T -> nat) arg: constr_type arg T -> nat -> Prop :=
  match arg with
  | nil => fun constr s => S s = RANK constr
  | Some A :: arg0 => fun constr s => forall a: A, partial_rank_equiv T RANK arg0 (constr a) s
  | None :: arg0 => fun constr s => forall a: T, partial_rank_equiv T RANK arg0 (constr a) (s + RANK a)
  end.

Fixpoint normtype_clause_rank T (RANK: T -> nat) arg s n: normtype_clause arg {t : T | RANK t < n} -> Prop :=
  match arg with
  | nil => fun _ => S s < S n
  | Some A :: arg0 => fun xa => match xa with (x, a) => normtype_clause_rank T RANK arg0 s n x end
  | None :: arg0 => fun xt => match xt with (x, exist _ t _) => normtype_clause_rank T RANK arg0 (s + RANK t) n x end
  end.

Lemma normtype_claus_rank_lemma: forall T RANK arg s n x, normtype_clause_rank T RANK arg s n x -> s < n.
Proof.
  intros.
  revert dependent s; induction arg as [| [|] ?]; intros; simpl in *.
  + lia.
  + destruct x as [x a].
    apply (IHarg x); auto.
  + destruct x as [x [t ?H]].
    specialize (IHarg x (s + RANK t) H).
    lia.
Qed.

Lemma rank_correct_partial_rank : forall T constrs arg2 constr2 (x: rect_type T constrs (fun _ => nat)), rank_correct T constrs x arg2 constr2 -> partial_rank_equiv T (rank T constrs x) arg2 constr2 0.
Proof.
  intros.
  set (RANK := rank T constrs x) in *.
  unfold rank_correct in H.
  change (rank T constrs x) with RANK in H.
  unfold rank_para in H.
  set (s := 0) in H |- *.
  clearbody RANK s.
  revert dependent s; induction arg2 as [| [|] ? IH]; intros.
  - simpl in *.
    symmetry; auto.
  - simpl in *.
    intros a.
    specialize (H a).
    apply (IH (constr2 a)).
    auto.
  - simpl in *.
    intros.
    specialize (H a).
    apply (IH (constr2 a)).
    auto.
Qed.

Definition DT_pattern_match_para_clause n T constrs1 arg2a arg2b constr2 constr2b constrs3 s x
            (H : partial_rank_equiv T (rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x) arg2b constr2b s)
            (F : forall x0 : normtype_clause arg2b {t : T | rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t < n},
    normtype_clause_rank T (rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x) arg2b s n x0 ->
    normtype T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3))
      {t : T | rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t < n}) : 
  rect_clause_type arg2b T (fun t : T => rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t < S n -> normtype T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) {t0 : T | rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t0 < n}) constr2b.
  set (RANK := rank T (rev_append constrs1 (_[rev_append arg2a arg2b, constr2]_ :: constrs3)) x) in *.
  revert dependent arg2a.
  revert dependent s.
  induction arg2b as [| [A |] arg2b IH]; intros.
  - simpl in F, H |- *. symmetry in H. 
    exact (fun H0 => F tt (eq_rect (RANK constr2b) (fun n0 : nat => n0 < S n) H0 (S s) H)).
  - simpl; intros a.
    exact (IH (constr2b a) s (Some A :: arg2a) constr2 x (H a) (fun x H0 => F (x, a) H0)).
  - simpl; intros a _.
    refine (IH (constr2b a) (s + RANK a) (None :: arg2a) constr2 x (H a) (fun x H0 => _)).
    pose proof normtype_claus_rank_lemma T RANK _ _ _ _ H0.
    assert (RANK a < n).
    { apply Plus.plus_lt_reg_l with (p := s).
      apply Lt.lt_le_trans with n ; auto.
      apply Plus.le_plus_r.
    }
    refine (F (x, exist _ a H2) H0).
Defined.

Definition DT_pattern_match_para
           n
           T
           (constrs1: ConstrsType T)
           arg2 constr2
           (constrs3: ConstrsType T)
           (x: rect_type T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) (fun _ => nat)):
           rank_correct T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x arg2 constr2 ->
           rect_clause_type arg2 T (fun t => rank T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x t < S n -> normtype T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) (sig (fun t: T => rank T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x t < n))) constr2.
  intros T_rank_correctness.
  apply rank_correct_partial_rank in T_rank_correctness as H. clear T_rank_correctness.
  set (RANK := rank T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x) in *.
  pose proof fun x
                 (H0: normtype_clause_rank T RANK arg2 0 n x) =>
               nested_inr T constrs1 (_[ arg2, constr2 ]_ :: constrs3) (sig (fun t => RANK t < n)) (inl x) as F.
    apply (DT_pattern_match_para_clause n T constrs1 nil arg2 constr2 constr2 constrs3 0 x H F).
Defined.

Definition pattern_match_DT_para_clause n T constrs1 arg2a arg2b constr2 constr2b constrs3 
           (X : forall x : rect_type T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) ((fun (_ : ConstrsType T) (_ : T) => nat) (rev_append nil (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)))),
    (forall arg constr,In (_[ arg, constr ]_) (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) -> rank_correct T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x arg constr) ->
    rect_clause_type arg2b T (fun t : T => rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t < S n -> normtype T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) {t0 : T | rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t0 < n}) constr2b) :
          rect_clause_type arg2b T (fun t : T => forall x : rect_type T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) (fun _ : T => nat),
   (forall arg constr,In (_[ arg, constr ]_) (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) -> rank_correct T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x arg constr) ->
   rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t < S n -> normtype T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) {t0 : T | rank T (rev_append constrs1 (_[ rev_append arg2a arg2b, constr2 ]_ :: constrs3)) x t0 < n}) constr2b.
  revert arg2a constr2 constr2b X.
  induction arg2b as [| [|] arg2b]; intros.
  + simpl in X |- *.
    apply X.
  + intros ?. 
    apply (IHarg2b (Some T0 :: arg2a) constr2 (constr2b x0) (fun x H => X x H x0)).
  + intros ? ?.
    apply (IHarg2b (None :: arg2a) constr2 (constr2b x) (fun x0 H => X x0 H x (IH x0 H))).
Defined.

Definition pattern_match_para_DT
           n
           T
           (constrs1: ConstrsType T)
           arg2 constr2
           (constrs3: ConstrsType T):
           rect_clause_type arg2 T
             (fun t =>
                forall x: rect_type T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) (fun _ => nat),
                  (forall arg constr,
                      List.In (_[arg, constr]_) (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) ->
            rank_correct T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x arg constr) ->
                rank T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x t < S n ->
                normtype T
                  (rev_append constrs1 (_[arg2, constr2]_ :: constrs3))
                  (sig (fun t: T => rank T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x t < n))) constr2 :=
    pattern_match_DT_para_clause n T constrs1 nil arg2 constr2 constr2 constrs3 
    (fun x (H: forall arg constr,
                List.In (_[arg, constr]_) (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) ->
                rank_correct T (rev_append constrs1 (_[arg2, constr2]_ :: constrs3)) x arg constr)
    => DT_pattern_match_para n T constrs1 arg2 constr2 constrs3 x (H arg2 constr2 ltac:(rewrite rev_append_rev, in_app_iff; simpl; tauto))).


Definition pattern_match_DT
           n
           T
           (constrs: ConstrsType T)
           (rect: forall P, rect_type T constrs P)
           (rect_correctness: Sol2.rect_correct T constrs rect):
  forall t:T,
    rank T constrs (rect (fun _ => nat)) t < S n ->
    normtype T constrs (sig (fun t: T => rank T constrs (rect (fun _ => nat)) t < n)).
  refine (fun t =>
  apply_rect_rec
    T
    (fun constrs t =>
       forall x: rect_type T constrs (fun _ => nat),
         (forall arg constr,
            List.In (_[arg, constr]_) constrs ->
            rank_correct T constrs x arg constr) ->
         rank T constrs x t < S n -> normtype T constrs (sig (fun t => rank T constrs x t < n)))
    nil
    constrs
    (pattern_match_para_DT n T) (rect _) t _ _).
  intros.
  apply rank_correctness; auto.
  apply rect_correctness_equiv; auto.
Defined.

Definition pattern_match_DT_correct n T constrs1 arg constr constrs3 rect: Prop :=
  rect_correct_clause T (fun t0 : T =>
   forall  x : rect_type T (rev_append constrs1 (_[ arg, constr ]_ :: constrs3)) (fun _ : T => nat),
   (forall arg0 constr0 , In (_[ arg0, constr0 ]_) (rev_append constrs1 (_[ arg, constr ]_ :: constrs3)) ->
    rank_correct T (rev_append constrs1 (_[ arg, constr ]_ :: constrs3)) x arg0 constr0) ->
   rank T (rev_append constrs1 (_[ arg, constr ]_ :: constrs3)) x t0 < S n ->
   normtype T (rev_append constrs1 (_[ arg, constr ]_ :: constrs3))
     {t1 : T | rank T (rev_append constrs1 (_[ arg, constr ]_ :: constrs3)) x t1 < n})
  (apply_rect_rec T
     (fun (constrs0 : list {arg0 : list (option Type) & constr_type arg0 T})
        (t0 : T) =>
      forall x : rect_type T constrs0 (fun _ : T => nat),
      (forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
       In (_[ arg0, constr0 ]_) constrs0 ->
       rank_correct T constrs0 x arg0 constr0) ->
      rank T constrs0 x t0 < S n ->
      normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n})
      nil (rev_append constrs1 (_[ arg, constr ]_ ::constrs3)) (pattern_match_para_DT n T)
     rect) arg constr
  (pattern_match_para_DT n T constrs1 arg constr constrs3).

Lemma pattern_match_DT_correctness : forall n T constrs1 arg2 constr2 constrs3 rect ,
    Sol1.rect_correct T (rev_append constrs1 (_[arg2,constr2]_ :: constrs3)) rect ->
  pattern_match_DT_correct n T constrs1 arg2 constr2 constrs3 (rect _).
Proof.
  intros. unfold Sol1.rect_correct in H.
  unfold Sol1.apply_rect_correct in H.
  assert(forall (P : ConstrsType T -> T -> Type)
      (para: ParaType T P),
    citer_and T
      (fun constrs : ConstrsType T =>
       forall t : T, P constrs t)
      (fun (constrs1 : ConstrsType T)
         (arg2 : list (option Type)) (constr2 : constr_type arg2 T)
         (constrs3 : ConstrsType T)
         (f : forall t : T, P (rev_append constrs1 (_[ arg2, constr2 ]_ :: constrs3)) t) =>
       rect_correct_clause T (P (rev_append constrs1 (_[ arg2, constr2 ]_ :: constrs3))) f arg2
         constr2 (para constrs1 arg2 constr2 constrs3)) constrs1
       (_[ arg2, constr2 ]_ :: constrs3)
      (apply_rect T P (rev_append constrs1 (_[ arg2, constr2 ]_ :: constrs3)) para
         (rect (P (rev_append constrs1 (_[ arg2, constr2 ]_ :: constrs3))))) ).
  { 
    revert arg2 constr2 constrs3 rect H.
    induction constrs1 as [ | [arg1 constr1] constrs1]; simpl in * ; intros ; auto.
    apply (IHconstrs1 arg1 constr1 (_[arg2 , constr2]_ :: constrs3)) ; auto.
  }
  specialize (H0 (fun (constrs0 : list {arg0 : list (option Type) & constr_type arg0 T})
        (t0 : T) =>
      forall x : rect_type T constrs0 (fun _ : T => nat),
      (forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
       In (_[ arg0, constr0 ]_) constrs0 ->
       rank_correct T constrs0 x arg0 constr0) ->
      rank T constrs0 x t0 < S n ->
      normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n}) (pattern_match_para_DT n T)).
  destruct H0 as [ ? _ ].
  exact H0.
Qed.

Fixpoint normtype_clause_map arg ty1 ty2 (f: ty1 -> ty2): normtype_clause arg ty1 -> normtype_clause arg ty2 :=
  match arg with
  | nil => fun _ => tt
  | Some A :: arg0 => fun xa => match xa with (x, a) => (normtype_clause_map arg0 ty1 ty2 f x, a) end
  | None :: arg0 => fun xt => match xt with (x, t) => (normtype_clause_map arg0 ty1 ty2 f x, f t) end
  end.

Fixpoint normtype_map T (constrs: ConstrsType T) ty1 ty2 (f: ty1 -> ty2): normtype T constrs ty1 -> normtype T constrs ty2 :=
  match constrs with
  | nil => fun H => H
  | existT _ arg constr :: constrs0 => fun x =>
      match x with
      | inl x => inl (normtype_clause_map arg ty1 ty2 f x)
      | inr x => inr (normtype_map T constrs0 ty1 ty2 f x)
      end
  end.

Definition Match_result T constrs1 arga argb constr constrb constrs3 n 
      (F1 : normtype_clause argb T -> normtype_clause (rev_append arga argb) T)
      (X : forall
         x : rect_type T
               (rev_append constrs1
                  (_[ rev_append arga argb, constr ]_ :: constrs3))
               ((fun (_ : ConstrsType T) (_ : T) => nat)
                  (rev_append nil
                     (rev_append constrs1
                        (_[ rev_append arga argb, constr ]_ :: constrs3)))),
       (forall (arg : list (option Type)) (constr0 : constr_type arg T),
        In (_[ arg, constr0 ]_)
          (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) ->
        rank_correct T
          (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3))
          x arg constr0) ->
       rect_clause_type argb T
         (fun t : T =>
          rank T
            (rev_append constrs1
               (_[ rev_append arga argb, constr ]_ :: constrs3)) x t < 
          S n ->
          normtype T
            (rev_append constrs1
               (_[ rev_append arga argb, constr ]_ :: constrs3))
            {t0 : T |
            rank T
              (rev_append constrs1
                 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t0 < n})
         constrb) : Prop .
  intros. revert dependent arga.
  induction argb as [ | [ | ]] ; intros ; simpl in *.
  -  apply (forall x H1 H2,  nested_inr T constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3) T (inl (F1 tt)) = 
  normtype_map T (rev_append constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3)) {t1 : T | rank T (rev_append constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3)) x t1 < n} T
     (proj1_sig (P:=fun t1 : T => rank T (rev_append constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3)) x t1 < n)) (X x H1 H2)).
  - apply (forall x0 , IHargb (constrb x0) (Some T0 :: arga) constr (fun res => F1 (res , x0)) (fun x H1 => X x H1 x0)).
  - apply (forall x0 (H2 : forall x H0, rank T
       (rev_append constrs1
          (_[ rev_append arga (None :: argb), constr ]_ :: constrs3)) x x0 <
     S n ->
     normtype T
       (rev_append constrs1
          (_[ rev_append arga (None :: argb), constr ]_ :: constrs3))
       {t0 : T |
       rank T
         (rev_append constrs1
            (_[ rev_append arga (None :: argb), constr ]_ :: constrs3)) x t0 <
       n}), IHargb (constrb x0) (None :: arga) constr (fun res => F1 (res , x0)) (fun x H1 => X x H1 x0 (H2 x H1))).
Defined.

Definition Match_result_less T constrs1 arga argb constr constrb constrs3 n 
      (F1 : normtype_clause argb T -> normtype_clause (rev_append arga argb) T)
      (x : rect_type T
               (rev_append constrs1
                  (_[ rev_append arga argb, constr ]_ :: constrs3))
               ((fun (_ : ConstrsType T) (_ : T) => nat)
                  (rev_append nil
                     (rev_append constrs1
                        (_[ rev_append arga argb, constr ]_ :: constrs3)))))
      (H1 : forall (arg : list (option Type)) (constr0 : constr_type arg T),
        In (_[ arg, constr0 ]_)
          (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) ->
        rank_correct T
          (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3))
          x arg constr0)
      (X : rect_clause_type argb T
         (fun t : T =>
          rank T
            (rev_append constrs1
               (_[ rev_append arga argb, constr ]_ :: constrs3)) x t < 
          S n ->
          normtype T
            (rev_append constrs1
               (_[ rev_append arga argb, constr ]_ :: constrs3))
            {t0 : T |
            rank T
              (rev_append constrs1
                 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t0 < n})
         constrb) : Prop.
  intros. revert dependent arga.
  induction argb as [ | [ | ]] ; intros ; simpl in *.
  - apply (forall H2,  nested_inr T constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3) T (inl (F1 tt)) = 
  normtype_map T (rev_append constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3)) {t1 : T | rank T (rev_append constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3)) x t1 < n} T
     (proj1_sig (P:=fun t1 : T => rank T (rev_append constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3)) x t1 < n)) (X H2)).
  - apply (forall x0 , IHargb (constrb x0) (Some T0 :: arga) constr (fun res => F1 (res , x0)) x H1 (X x0)).
  - apply (forall x0 (H2 : rank T
       (rev_append constrs1
          (_[ rev_append arga (None :: argb), constr ]_ :: constrs3)) x x0 <
     S n ->
     normtype T
       (rev_append constrs1
          (_[ rev_append arga (None :: argb), constr ]_ :: constrs3))
       {t0 : T |
       rank T
         (rev_append constrs1
            (_[ rev_append arga (None :: argb), constr ]_ :: constrs3)) x t0 <
       n}), IHargb (constrb x0) (None :: arga) constr (fun res => F1 (res , x0)) x H1 (X x0 H2)).
Defined.

Theorem Match_result_less_arrow_Match : forall T constrs1 arga argb constr constrb constrs3 n F1 X , 
    (forall x H1 , Match_result_less T constrs1 arga argb constr constrb constrs3 n F1 x H1 (X x H1)) ->
    Match_result T constrs1 arga argb constr constrb constrs3 n F1 X.
Proof.
  intros.
  revert dependent arga.
  induction argb as [ | [ | ]]; intros ; auto.
  - intro. intros.
    apply (IHargb (constrb x0) (Some T0 :: arga) constr (fun res => F1 (res , x0))).
    intros. apply (H x H1).
  - intro. intros.
    apply (IHargb (constrb x0) (None :: arga) constr (fun res => F1 (res , x0))).
    intros. apply (H x H1).
Qed.

Lemma DT_pattern_match_para_equiv_clause_lemma : forall T constrs1 arga argb constr constrb constrs3 n
  F1 X, Match_result T constrs1 arga argb constr constrb constrs3 n F1 X ->
  apply_rect_clause_rel_rec T
  (fun (constrs0 : ConstrsType T) (_ : T) =>
   normtype T constrs0 T)
  (fun (constrs0 : ConstrsType T) (t0 : T) =>
   forall x : rect_type T constrs0 (fun _ : T => nat),
   (forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
    In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0) ->
   rank T constrs0 x t0 < S n -> normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n})
  (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) argb constrb
  (fun (constrs0 : ConstrsType T) 
     (t0 : T) (x1 : normtype T constrs0 T)
     (x2 : forall x : rect_type T constrs0 (fun _ : T => nat),
           (forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
            In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0) ->
           rank T constrs0 x t0 < S n ->
           normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n}) =>
   forall (x : rect_type T constrs0 (fun _ : T => nat))
     (H0 : forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
           In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0)
     (H2 : rank T constrs0 x t0 < S n),
   x1 =
   normtype_map T constrs0 {t1 : T | rank T constrs0 x t1 < n} T
     (proj1_sig (P:=fun t1 : T => rank T constrs0 x t1 < n)) (x2 x H0 H2))
  (pattern_match_para_rec T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) argb constrb
     (fun x : normtype_clause argb T => nested_inr T constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3) T (inl (F1 x))))
  (pattern_match_DT_para_clause n T constrs1 arga argb constr constrb constrs3 X).
Proof.
  intros.
  revert dependent arga.
  induction argb as [ | [| ]] ; intros ; auto.
  - simpl. intros.
    apply (IHargb (constrb x0) (Some T0 :: arga) constr (fun res => F1 (res , x0)) (fun x H1 => X x H1 x0)).
    apply H.
  - simpl. intros. 
    apply (IHargb (constrb x) (None :: arga) constr (fun res => F1 (res , x)) (fun x0 H0 => X x0 H0 x (y2 x0 H0))). 
    apply H. 
Qed.

Lemma DT_pattern_match_para_equiv_clause : forall T constrs1 arga argb constr constrb constrs3 n F1 F2 H1,
  (forall x x0 x1 h, x0 = normtype_clause_map argb {t1 : T | rank T (rev_append constrs1 (_[ rev_append arga argb , constr ]_ :: constrs3)) x t1 < n} T (proj1_sig (P:=fun t1 : T => rank T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t1 < n)) x1 -> F1 x0 = normtype_clause_map (rev_append arga argb) {t1 : T | rank T (rev_append constrs1 (_[ rev_append arga argb , constr ]_ :: constrs3)) x t1 < n} T (proj1_sig (P:=fun t1 : T => rank T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t1 < n)) (F2 x x1 h))-> 
    (forall x x0 x1 h,  F1 x0 = normtype_clause_map (rev_append arga argb) {t1 : T | rank T (rev_append constrs1 (_[ rev_append arga argb , constr ]_ :: constrs3)) x t1 < n} T (proj1_sig (P:=fun t1 : T => rank T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t1 < n)) (F2 x x1 h) ->
  nested_inr T constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3) T (inl (F1 x0)) = normtype_map T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) {t1 : T | rank T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t1 < n} T (proj1_sig (P:=fun t1 : T => rank T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t1 < n)) (nested_inr T constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3) {t : T | rank T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t < n} (inl (F2 x x1 h)))) ->
  apply_rect_clause_rel_rec T
  (fun (constrs0 : ConstrsType T) (_ : T) => normtype T constrs0 T)
  (fun (constrs0 : ConstrsType T) (t0 : T) =>
   forall x : rect_type T constrs0 (fun _ : T => nat),
   (forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
    In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0) ->
   rank T constrs0 x t0 < S n -> normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n})
  (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) argb constrb
  (fun (constrs0 : ConstrsType T) 
     (t0 : T) (x1 : normtype T constrs0 T)
     (x2 : forall x : rect_type T constrs0 (fun _ : T => nat),
           (forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
            In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0) ->
           rank T constrs0 x t0 < S n ->
           normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n}) =>
   forall (x : rect_type T constrs0 (fun _ : T => nat))
     (H0 : forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
           In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0)
     (H2 : rank T constrs0 x t0 < S n),
   x1 =
   normtype_map T constrs0 {t1 : T | rank T constrs0 x t1 < n} T
     (proj1_sig (P:=fun t1 : T => rank T constrs0 x t1 < n)) (x2 x H0 H2))
  (pattern_match_para_rec T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) argb constrb
     (fun x : normtype_clause argb T => nested_inr T constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3) T (inl (F1 x))))
  (pattern_match_DT_para_clause n T constrs1 arga argb constr constrb constrs3
     (fun
        (x : rect_type T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3))
               (fun _ : T => nat))
        (H : forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
             In (_[ arg0, constr0 ]_)
               (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) ->
             rank_correct T
               (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x arg0
               constr0) =>
      DT_pattern_match_para_clause n T constrs1 arga argb constr constrb constrs3 0 x (H1 x H)
        (fun
           (x0 : normtype_clause argb
                   {t : T |
                   rank T
                     (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t <
                   n})
           (h : normtype_clause_rank T
                  (rank T
                     (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x)
                  argb 0 n x0) => nested_inr T constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)
           {t : T | rank T (rev_append constrs1 (_[ rev_append arga argb, constr ]_ :: constrs3)) x t < n}
           (inl (F2 x x0 h))))).
Proof.
  intros. apply DT_pattern_match_para_equiv_clause_lemma.
  apply Match_result_less_arrow_Match. 
  intros. specialize (H x). specialize (H0 x).
  set (F3 := F2 x) in *. set (H1' := H1 x H2) in *.
  clearbody F3 H1'. clear F2 H1. 
  rename F3 into F2. rename H1' into H1. 
  set (s := 0) in *.
  clearbody s.
  set (RANK := rank T (rev_append constrs1 (_[rev_append arga argb, constr]_ :: constrs3)) x) in *.
  revert dependent arga.
  revert dependent s.
  induction argb as [| [|] argb] ; intros.
  - simpl in * ; intros. simpl. 
    change (rank T (rev_append constrs1 (_[ rev_append arga nil, constr ]_ :: constrs3)) x) with RANK in H3 |- *.
    rewrite (H0 tt tt (eq_rect (RANK constrb) (fun n0 : nat => n0 < S n) H3 (S s) (eq_sym H1))) ; auto.
  - intro. intros. 
    apply (IHargb (constrb x0) s (Some T0 :: arga) constr (fun res => F1 (res , x0)) x (fun res => F2 (res , x0))) ; auto. clear IHargb. 
    intros. apply H. simpl. rewrite H3. auto. 
  - intro. intros. 
    apply (IHargb (constrb x0) (s + RANK x0) (None :: arga) constr (fun res => F1 (res , x0)) x (fun res Hp =>
          let H2 : s + RANK x0 < n :=
            normtype_claus_rank_lemma T RANK argb (s + RANK x0) n res Hp in
          let H3 : RANK x0 < n :=
            Plus.plus_lt_reg_l (RANK x0) n s
              (Lt.lt_le_trans (s + RANK x0) n (s + n) H2 (Plus.le_plus_r s n)) in
          F2 (res, exist _ x0 H3) Hp)) ; auto. clear IHargb.
    intros. apply H. simpl. rewrite H4. auto.
Qed.

Lemma F_Prop_normtype_map : forall n T constrs1 constrs23 x x0 x1, 
    x0 = normtype_map T constrs23 {t1 : T | rank T (rev_append constrs1 constrs23) x t1 < n} T (@proj1_sig _ _) x1 ->
    nested_inr T constrs1 constrs23 T x0 = normtype_map T (rev_append constrs1 constrs23) {t1 : T | rank T (rev_append constrs1 constrs23) x t1 < n} T (@proj1_sig _ _) (nested_inr T constrs1 constrs23
     {t : T | rank T (rev_append constrs1 constrs23) x t < n} x1).
Proof.
  intros.
  revert dependent constrs23.
  induction constrs1 as [ | [arg constr] constrs1]; simpl in * ; intros ; auto.
  apply (IHconstrs1 (_[arg,constr]_::constrs23)) ; auto.
  rewrite H. auto.
Qed.

Lemma DT_pattern_match_para_equiv : forall T constrs1 arg constr constrs3 n , 
  apply_rect_clause_rel T
  (fun constrs0 _ => normtype T constrs0 T)
  (fun constrs0 t0 => forall x : rect_type T constrs0 (fun _ : T => nat),
   (forall arg0 constr0 , In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0) ->
   rank T constrs0 x t0 < S n ->
   normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n}) constrs1 arg constr
  constrs3
  (fun constrs0 t0 (x1 : normtype T constrs0 T)
     (x2 : forall x : rect_type T constrs0 (fun _ : T => nat),
           (forall arg0 constr0, In (_[ arg0, constr0 ]_) constrs0 -> rank_correct T constrs0 x arg0 constr0) -> rank T constrs0 x t0 < S n ->  normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n}) =>
   forall (x : rect_type T constrs0 (fun _ : T => nat))
     (H0 : forall (arg0 : list (option Type)) (constr0 : constr_type arg0 T),
           In (_[ arg0, constr0 ]_) constrs0 ->
           rank_correct T constrs0 x arg0 constr0)
     (H1 : rank T constrs0 x t0 < S n),
   x1 = normtype_map T constrs0 {t1 : T | rank T constrs0 x t1 < n} T
     (@proj1_sig _ _) (x2 x H0 H1)) (pattern_match_para T constrs1 arg constr constrs3)
  (pattern_match_para_DT n T constrs1 arg constr constrs3).
Proof.
  intros.
  apply (DT_pattern_match_para_equiv_clause T constrs1 nil arg constr constr constrs3 n (fun res => res) (fun x res H => res) (fun x H => (rank_correct_partial_rank T (rev_append constrs1 (_[ arg, constr ]_ :: constrs3)) arg
           constr x
           (H arg constr
              (eq_ind_r
                 (fun l : ConstrsType T =>
                  In (_[ arg, constr ]_) l)
                 (Morphisms.iff_flip_impl_subrelation
                    (In (_[ arg, constr ]_) (rev constrs1 ++ _[ arg, constr ]_ :: constrs3))
                    (In (_[ arg, constr ]_) (rev constrs1) \/
                     In (_[ arg, constr ]_) (_[ arg, constr ]_ :: constrs3))
                    (in_app_iff (rev constrs1) (_[ arg, constr ]_ :: constrs3)
                       (_[ arg, constr ]_)) (or_intror (or_introl eq_refl)))
                 (rev_append_rev constrs1 (_[ arg, constr ]_ :: constrs3))))))) ; auto.
   intros.
   simpl in *.
   apply F_Prop_normtype_map.
   rewrite H. auto.
Qed.
 
Theorem DT_pattern_match_correct: forall T constrs (rect: forall P, rect_type T constrs P) rect_correctness n t
  (H: rank T constrs (rect (fun _ => nat)) t < S n),
  pattern_match T constrs (rect _) t = normtype_map T constrs _ _ (@proj1_sig _ _) (pattern_match_DT n T constrs rect rect_correctness t H).
Proof.
  intros.
  refine (apply_rect_clause_rel_Prop T (fun constrs _ => normtype T constrs T) (fun constrs0 t0 =>
      forall x : rect_type T constrs0 (fun _ : T => nat),
      (forall arg constr,  In (_[ arg, constr ]_) constrs0 -> rank_correct T constrs0 x arg constr) ->
      rank T constrs0 x t0 < S n ->
      normtype T constrs0 {t1 : T | rank T constrs0 x t1 < n}) constrs (pattern_match_para T) (pattern_match_para_DT n T) rect _ (fun constrs t x1 x2 => forall x H (H0 : rank T constrs x t < S n) , x1 = normtype_map T constrs {t : T | rank T constrs x t < n} T (@proj1_sig _ _) (x2 x H H0)) _ _ _ _ _ _) ; intros ; simpl in * ; auto.
  - apply rect_correctness_equiv, rect_correctness.
  - apply DT_pattern_match_para_equiv.
Qed.
