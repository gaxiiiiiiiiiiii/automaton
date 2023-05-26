Require Export Ensembles Classical_sets.
Require Export ssreflect.
From mathcomp Require Export finset eqtype ssrbool seq.
Require Export NonEmptyFintype.
Open Scope list_scope.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ================== Notation of finset ================== *)

Global Notation "x ∈ X" := (x \in X)(at level 60).
Global Notation "A ∩ B" := (setI A B)(at level 40).
Global Notation "A ∪ B" := (setU A B)(at level 40).
Global Notation "A ⊂ B" := (A \subset B)(at level 30).
Global Notation "A // B" := (setD A B)(at level 40).
Global Notation "¬ A" := (setC A)(at level 40).
Global Notation "pow[ A ]" := (powerset A).
Global Notation "∅" := set0.

Arguments Union {U}.
Arguments Intersection {U}.
Arguments Complement {U}.
Arguments Singleton {U}.
Arguments In {U}.

(* ================== Nondeterministic Finite Autolmata(NFA) ================== *)

Record NFA  (alphabet : nonEmptyFintype) := {
  state : nonEmptyFintype;
  init : {SET state};
  trans : state -> alphabet -> {set state};
  accepts : {set state}
}.

Arguments state {alphabet}.
Arguments init {alphabet}.
Arguments trans {alphabet}.
Arguments accepts {alphabet}.

Inductive path {Σ : nonEmptyFintype} (N : NFA Σ) :  list Σ -> (state N) -> Prop :=
  | path_nil s : s ∈ init N -> path N nil s
  | path_step s s' a w : s' ∈ trans N s a -> path N w s -> path N  (a :: w) s'.

Definition langOf {Σ : nonEmptyFintype}(N : NFA Σ) : Ensemble (list Σ) :=
  fun input => exists s, path N input s /\ s ∈ accepts N.

(* ================== Deterministic Finite Autolmata(DFA)  ================== *)

Record DFA (alphabet : nonEmptyFintype) := {
  baseD :> NFA alphabet;
  initD : [set (default (state baseD))] = init baseD;
  transD :forall s a,  exists s0, trans baseD s a = [set s0];
}.

Arguments baseD {alphabet}.
Arguments initD {alphabet}.
Arguments transD {alphabet}.

Lemma DFA_path {Σ : nonEmptyFintype} (N : DFA Σ) (w : list Σ) :
  exists s, path N w s.
Proof.
  induction w.
  - exists (default (state N)).
    constructor.
    rewrite <- initD.
    apply /set1P; auto.
  - move : IHw => [s H].
    move : (transD N s a) => [s' H'].
    exists s'.
    econstructor; eauto.
    rewrite H'.
    apply /set1P; auto.
Qed.

Lemma DFA_path_inj {Σ : nonEmptyFintype} (N : DFA Σ) (w : list Σ) s s' :
  path N w s -> path N w s' -> s = s'.
Proof.
  move : s s'.
  induction w => s s' H1 H2; inversion H1; inversion H2; clear H1 H2; subst.
  - rewrite <- (initD N) in H, H0.
    move /set1P : H ->.
    move /set1P : H0 ->.
    auto.
  - move : (IHw s0 s1 H5 H10) => ss; subst s1.
    case : (transD N s0 a) => [s1 Hs1] .
    rewrite Hs1 in H3, H8.
    move /set1P : H3 ->.
    move /set1P : H8 ->.
    auto.
Qed.

(* ================== Union  ================== *)

Definition union_init_  {Σ : nonEmptyFintype} (N1 N2 : NFA Σ) :=
  [set ss : sum_finType (state N1) (state N2)
              | match ss with
              | inl s1 => s1 ∈ init N1
              | inr s2 => s2 ∈ init N2
              end
  ].

Definition union_init {Σ : nonEmptyFintype} (N1 N2 : NFA Σ) :
  {SET nonEmptyFinType_of (inl (default (state N1)) : sum_finType (state N1) (state N2))}.
Proof.
  eapply nonEmptyFinset.Pack with (carrier := union_init_ N1 N2).
  simpl.
  unfold union_init_.
  rewrite in_set.
  apply hasDefault.
Defined.

Definition union_trans {Σ} (N1 N2 : NFA Σ) ss a :=

   [set ss' |
        match ss with
        | inl s1 => [exists s, (s ∈ trans N1 s1 a) && (ss' == inl s)]
        | inr s2 => [exists s, (s ∈ trans N2 s2 a) && (ss' == inr s)]
        end
   ].

Definition union {Σ : nonEmptyFintype} (N1 N2 : NFA Σ) : NFA Σ :=
  {|
    state := nonEmptyFinType_of (inl (default (state N1)) : sum_finType (state N1) (state N2));
    init := union_init N1 N2;
    accepts := [set ss : sum_finType (state N1) (state N2)
                | match ss with
                | inl s1 => s1 ∈ accepts N1
                | inr s2 => s2 ∈ accepts N2
                end
              ];
    trans := union_trans N1 N2;
  |}.

Theorem union_spec  {Σ}  (N1 N2 : NFA Σ) :
  Union (langOf N1) (langOf N2) = langOf (union N1 N2).
Proof.
  apply Extensionality_Ensembles; split => w H.
  {
    destruct H; move : H => [s [Hp Ha]];
      [exists (inl s) | exists (inr s)].
    - split.
      + clear Ha; induction Hp.
        * constructor; simpl.
          rewrite in_set => //.
        * apply (path_step (union N1 N2) (inl s)); eauto.
          rewrite in_set.
          apply /existsP.
          exists s'.
          apply /andP; auto.
      + simpl.
        rewrite in_set => //=.
    - split.
      + clear Ha; induction Hp.
        * constructor; simpl.
          rewrite in_set => //.
        * apply (path_step (union N1 N2) (inr s)); eauto.
          rewrite in_set.
          apply /existsP.
          exists s'.
          apply /andP; auto.
      + simpl.
        rewrite in_set => //.
  }
  {
    destruct H as [s [Hp Ha]].
    destruct s; rewrite in_set in Ha;
    [left|right]; exists s; split; auto; clear Ha.
    - move : s Hp.
      induction w => s Hp.
      * inversion Hp; subst; clear Hp.
        rewrite in_set in H.
        constructor; auto.
      * inversion Hp; subst.
        rewrite in_set in H1.
        destruct s0; move /existsP : H1 => [s' /andP [Hs' /eqP Hss]];
        inversion Hss; subst s'.
        econstructor; eauto.
    - move : s Hp.
      induction w => s Hp.
      * inversion Hp; subst; clear Hp.
        rewrite in_set in H.
        constructor; auto.
      * inversion Hp; subst.
        rewrite in_set in H1.
        destruct s0; move /existsP : H1 => [s' /andP [Hs' /eqP Hss]];
        inversion Hss; subst s'.
        econstructor; eauto.
  }
Qed.

(* ================== Intersection  ================== *)

Definition inter_init {Σ : nonEmptyFintype} (N1 N2 : NFA Σ) :
  {SET nonEmptyFinType_of (default (state N1), default (state N2))}.
Proof.
  eapply nonEmptyFinset.Pack with (carrier := setX (init N1) (init N2)).
  simpl.
  apply /setXP.
  split; apply hasDefault.
Defined.

Definition inter_trans {Σ} (N1 N2 : NFA Σ) ss a :=
  [set ss' |
        (fst ss' ∈ trans N1 (fst ss) a) && (snd ss' ∈ trans N2 (snd ss) a)
  ].


Definition inter {Σ : nonEmptyFintype} (N1 N2 : NFA Σ) : NFA Σ :=
  {|
    state := nonEmptyFinType_of (default (state N1), default (state N2));
    init := inter_init N1 N2;
    accepts := setX (accepts N1) (accepts N2);
    trans := inter_trans N1 N2;
  |}.

Theorem inter_spec  {Σ}  (N1 N2 : NFA Σ) :
  Intersection (langOf N1) (langOf N2) = langOf (inter N1 N2).
Proof.
  apply Extensionality_Ensembles; split => w H.
  {
    destruct H as [s [s1 [Hp1 Ha1]] [s2 [Hp2 Ha2]]].
    exists (s1, s2); split; try split.
    * clear Ha1 Ha2.
      move : s2 Hp2.
      induction Hp1 => s2 Hp2.
      - inversion Hp2; subst.
        constructor => //=.
        apply /setXP; auto.
      - inversion Hp2; subst.
        econstructor; first last.
        apply IHHp1. apply H4.
        simpl. rewrite in_set => //=.
        apply /andP; split; auto.
    * rewrite in_set.
      apply /andP; split; auto.
  }
  {
    destruct H as [[s1 s2] [H1 H2]].
    rewrite in_set in H2.
    move /andP : H2 => /= [H H0].
    split; [exists s1 | exists s2]; split; auto; clear H H0.
    - move : s1 s2 H1.
      induction w => s1 s2 H.
      * inversion H; subst; clear H.
        rewrite in_set in H0.
        move : H0 => /= /andP [H1 H2].
        constructor; auto.
      * inversion H; subst.
        destruct s as [s1' s2'].
        rewrite in_set in H2.
        move : H2 => /= /andP [H1 H2].
        econstructor; eauto.
    - move : s1 s2 H1.
      induction w => s1 s2 H.
      * inversion H; subst; clear H.
        rewrite in_set in H0.
        move : H0 => /= /andP [H1 H2].
        constructor; auto.
      * inversion H; subst.
        destruct s as [s1' s2'].
        rewrite in_set in H2.
        move : H2 => /= /andP [H1 H2].
        econstructor; eauto.
  }
Qed.

(* ================== Complements  ================== *)

Definition compl {Σ} (N : NFA Σ) :=
  {|
    state := state N;
    init := init N;
    trans := trans N;
    accepts := ¬ (accepts N);
  |}.

Lemma path_compl_inj {Σ} (N : DFA Σ) w s s' :
  path N w s -> path (compl N) w s'  -> s = s'.
Proof.
  move : s s'.
  induction w => s s' H H'.
  - inversion H; inversion H'; subst; simpl in *.
    move : (initD N) H0 H1 <-.
    move /set1P ->.
    move /set1P ->.
    auto.
  - inversion H; inversion H'; subst; clear H H'.
    simpl in *.
    move : (IHw _ _ H4 H9) => ss; subst.
    move : (transD N s1 a) => [s0 H]; rewrite H in H2 H7.
    * move /set1P : H2 ->.
      move /set1P : H7 ->.
      auto.
Qed.

Lemma path_compl_iff {Σ} (N : DFA Σ) w s :
  path N w s <-> path (compl N) w s.
Proof.
  move : s.
  induction w => s; split => H; inversion H; clear H; subst;
  try econstructor => //=; eauto; try apply IHw; auto.
Qed.

Theorem compl_spec {Σ} (N : DFA Σ) :
  langOf (compl N) = Complement  (langOf N).
Proof.
  apply Extensionality_Ensembles; split => w H.
  {
    destruct H as [s [Hp Ha]]; simpl in *.
    move => F; destruct F as [s0 [Hp0 Ha0]].
    move : (path_compl_inj N w s0 s Hp0 Hp) => ss; subst.
    move /setCP : Ha0; auto.
  }
  {
    apply: NNPP => F.
    unfold In, langOf in *.
    unfold Complement, In in H.
    assert (forall s, ~ path N w s \/ ~ s ∈ accepts N).
    {
      move => s0.
      apply not_and_or => F0; apply H; exists s0; auto .
    }
    assert (forall s, ~ path (compl N) w s \/ ~ s ∈ setC (accepts N)).
    {
      move => s0.
      apply not_and_or => F0; apply F; exists s0; auto .
    }
    clear H F.
    move : (DFA_path N w) => [s Hp].
    move : (H0 s); move /or_to_imply /(_ Hp); clear H0 => H0.
    apply path_compl_iff in Hp.
    move : (H1 s); move /or_to_imply /(_ Hp); clear H1 => H1.
    apply H1; apply /setCP; auto.
  }
Qed.

(* ================== Determization  ================== *)

Definition determize_init_ {Σ} (N : NFA Σ) :
  { SET nonEmptyFinType_of (nonEmptyFinset.carrier (init N))}.
Proof.
  eapply nonEmptyFinset.Pack with
    (carrier := [set nonEmptyFinset.carrier (init N)]).
  simpl.
  apply /set1P; auto.
Defined.



Definition determize_ {Σ} (N : NFA Σ) : NFA Σ :=
  {|
    state := nonEmptyFinType_of (nonEmptyFinset.carrier (init N));
    init := determize_init_ N;
    trans := fun T a =>
      [set [set t | [exists s, (s \in T) && (t \in trans N s a)]]];
    accepts :=
      [set T | T ∩ (accepts N) != ∅ ];
  |}.

Lemma determize_initD {Σ} (N : NFA Σ) :
  [set (default (state (determize_ N)))] = init (determize_ N).
Proof.
  simpl. auto.
Qed.

Lemma determize_transD  : forall {Σ} (N : NFA Σ),
  forall (s : state (determize_ N)) (a : Σ),
  (exists s0 : state (determize_ N), trans (determize_ N) s a = [set s0]).
Proof.
  move => Σ N s a.
  simpl in *.
  exists ([set t | [exists s1, (s1 ∈ s) && (t ∈ trans N s1 a)]]); auto.
Qed.


Definition determize {Σ} (N : NFA Σ) : DFA Σ :=
  {|
    baseD := determize_ N;
    initD := determize_initD N;
    transD := determize_transD N;
  |}.



Lemma determize_preserves_path {Σ} (N : NFA Σ) w S :
  path (determize N) w S -> forall s, s ∈ S -> path N w s.
Proof.
  induction 1; rename s into S => s Hs.
  - simpl in *.
    move /set1P : H => E; subst.
    constructor; auto.
  - simpl in *.
    move /set1P : H => E; subst.
    rewrite in_set in Hs.
    move /existsP : Hs => [s0 /andP [Hs0 Hs1]].
     econstructor 2 with s0; auto.
Qed.

Lemma path_extends_determize {Σ} (N : NFA Σ) w s :
  path N w s -> exists S : {set (state N)}, s ∈ S /\ path (determize N) w S.
Proof.
  induction 1.
  - exists (init N); split; auto.
    constructor. apply hasDefault.
  - destruct IHpath as [S [HS Hp]].
    exists ([set t | [exists s0, (s0 ∈ S) && (t ∈ trans N s0 a)]]); split.
    * rewrite in_set.
      apply /existsP; exists s; apply /andP; split; auto.
    * econstructor 2 with S; auto.
      apply /set1P; auto.
Qed.


Theorem determize_spec {Σ} (N : NFA Σ) :
  langOf (determize N) = langOf N.
Proof.
  apply Extensionality_Ensembles; split => w H.
  {
    destruct H as [S [Hp Ha]]; simpl in *.
    rewrite in_set in Ha.
    move /set0Pn : Ha => [s /setIP [Hs Ha]].
    unfold langOf, In.
    exists s; split; auto.
    apply determize_preserves_path with S; auto.
  }
  {
    unfold In, langOf in *.
    move : H => [s [Hp Hs]].
    simpl.
    apply path_extends_determize in Hp.
    destruct Hp as [S [HS Hp]].
    exists S; split; auto.
    rewrite in_set.
    apply /set0Pn.
    exists s; apply /setIP; split; auto.
  }
Qed.

Lemma determizes_compl_spec {Σ} (N : NFA Σ) :
  langOf (compl (determize N)) = Complement (langOf N).
Proof.
  rewrite compl_spec.
  rewrite determize_spec.
  auto.
Qed.