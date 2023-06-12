Require Export buchi.
From mathcomp Require Export choice.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Implicit Arguments.

Record rabin (Σ : nonEmptyFintype) := {
  stateR : nonEmptyFintype;
  initR : {SET stateR};
  transR : stateR -> Σ -> {set stateR};
  acceptsR : {set {set stateR} * {set stateR}}
  (* acceptsInf : {set stateR}; *)
  (* acceptsFin : {set stateR}; *)
}.

Arguments stateR {_}.
Arguments initR {_}.
Arguments transR {_}.
Arguments acceptsR {_}.
(* Arguments acceptsFin {_}. *)

CoInductive prerun {Σ} (N : rabin Σ) : Stream Σ ->  Stream (stateR N) -> Prop :=
  | step w r :
     hd (tl r) ∈ transR N (hd r) (hd w) -> prerun (tl w) (tl r) -> prerun w r.

Inductive run {Σ} (N : rabin Σ) : Stream Σ -> Stream (stateR N) -> Prop :=
  | run_intro w r : hd r ∈ initR N -> prerun w r -> run  w r.

Definition langOf {Σ} (N : rabin Σ) (w : Stream Σ) : Prop :=
  exists r,(run w r /\ 
    exists p, (p ∈ acceptsR N /\ 
      (infinitely_often (fun s => hd s ∈ fst p) r) /\
      (~ infinitely_often (fun s => hd s ∈ snd p) r)
    )   
  ).




(* Record id_prod (T : finType) := {
  baseIP :>  prod_finType T T;
  axiomIP : fst baseIP == snd baseIP;
}.



Canonical id_prod_sub T := Eval hnf in [subType for baseIP T].
Definition id_prod_eqm T := Eval hnf in [eqMixin of id_prod T by <: ].
Canonical id_prod_eq T := Eval hnf in EqType (id_prod T) (id_prod_eqm T).
Definition id_prod_chm T := [choiceMixin of id_prod T by <: ].
Canonical id_prod_ch T := Eval hnf in ChoiceType (id_prod T) (id_prod_chm T).
Definition id_prod_cntm T := [countMixin of id_prod T by <: ].
Canonical id_prod_cnt T := Eval hnf in CountType (id_prod T) (id_prod_cntm T).
Canonical id_prod_scnt T := Eval hnf in [subCountType of id_prod T].
Definition id_prod_finm T := [finMixin of id_prod T by <: ].
Canonical id_prod_fin T := Eval hnf in FinType (id_prod T) (id_prod_finm T).
Canonical id_prod_sfin T := Eval hnf in [subFinType of id_prod T].

Arguments baseIP {_}.
Arguments axiomIP {_}.

*)

(* Definition mk_id_prod {T : nonEmptyFintype} (t : T) : id_prod T.
Proof.
  eapply Build_id_prod with (baseIP := (t, t)).
  auto.
Defined.  *)

Definition nonEmpty_prod (T : nonEmptyFintype) : nonEmptyFintype.
Proof.
  eapply nonEmptyFintype.Pack with (sort := prod_finType T T); split.  
  - destruct (prod_finType T T) => //=.
  - split.
    exact (default T, default T).
Defined. 

(* Canonical nonEmpty_prod. *)

Definition SET_nonEmpty_prod {T : nonEmptyFintype} (l r : {SET T}) : {SET nonEmpty_prod T}.
Proof.
  destruct l as [l Hl].
  destruct r as [r Hr].
  eapply nonEmptyFinset.Pack with (carrier := setX l r) => /=.
  apply /setXP; split => //.  
Defined.

(* Definition nonEmpty_id_prod (T : nonEmptyFintype) : nonEmptyFintype.
Proof.  
  eapply nonEmptyFintype.Pack with (sort := id_prod_fin T); split.  
  - destruct (id_prod_fin T) => //=.
  - split.
    apply (mk_id_prod (default T)).
Defined.

Definition mk_SET_nonEmpty_id_prod {T : nonEmptyFintype} (s : {SET T}) : {SET nonEmpty_id_prod T}.
Proof.
  eapply nonEmptyFinset.Pack with (carrier := [set :id_prod_fin T]).
  simpl.
  apply in_setT.
Qed. *)

(* Canonical nonEmpty_id_prod. *)






Definition rabin2buchi {Σ} (N : rabin Σ) : buchi Σ := {|
    state := nonEmpty_prod (stateR N);
    init := SET_nonEmpty_prod (initR N) (initR N);
    trans := fun p a => 
      [set q | (fst q \in (transR N (fst p ) a)) && (fst q == snd q)];
    accepts :=  setX (acceptsInf N) (acceptsFin N);
|}.
(*


Record rabin Σ := {
  baseR :> buchi Σ;
  stateR : nonEmptyFintype;
  axiomR : state baseR = nonEmpty_id_prod stateR;
}.

Arguments baseR {_}.
Arguments stateR {_}.
Arguments axiomR {_}.


Definition acceptsR {Σ} (N : rabin Σ) : {set nonEmpty_id_prod (stateR N)}.
Proof.
   move : (accepts N) => s.
  rewrite axiomR in s; auto.
Defined.

Definition acceptsFst {Σ} (N : rabin Σ) : {set stateR N} :=
  [set l | [exists p, (p ∈ (acceptsR N)) && (fst p  == l)]].

Definition acceptsSnd {Σ} (N : rabin Σ) : {set stateR N} :=
  [set r | [exists p, (p ∈ (acceptsR N)) && (snd p  == r)]].

Definition initR {Σ} (N : rabin Σ) : {SET nonEmpty_id_prod (stateR N)}.
Proof.
  move : (init N) => s.
  rewrite axiomR in s; auto.
Defined.

Definition transR {Σ} (N : rabin Σ) : nonEmpty_id_prod (stateR N) -> Σ -> {set nonEmpty_id_prod (stateR N)}.
Proof.
  move : (trans N).
  rewrite axiomR; auto.
Defined.  

(* 
取り敢えず buchi automaton の受理条件を書いたけど、いい感じにrabinのものに書き換えたい。
rabinの公理を使わないと状態が直積である事は主張できないから、最終状態の左右で分ける書き方がよくわからない。
*)

Search finset prod.
Print imset.
Print Imset.imset.
Export Imset.
Check imset.

Variable Σ : nonEmptyFintype.
Variable N : rabin Σ.
Variable s : state N.
Definition F := acceptsR N.
Variable p : nonEmpty_id_prod (stateR N).
Check (fst p).
Check (stateR N).


Definition langOf {Σ} (N : rabin Σ) (w : Stream Σ) : Prop :=
  exists r, run w r /\ infinitely_often (fun s => hd s ∈ accepts N) r.

Print langOf.
