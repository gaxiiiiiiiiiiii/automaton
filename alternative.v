Require Import Streams.

From mathcomp Require Import ssreflect ssrbool.




Notation "¬ P" := (fun s => ~ P s)(at level 10).


(*
substreamもuntilも自身を含まない（真部分集合の様な）実装となっている。
何故なら、自身を含むとalternativeにおいてPとQをの両方を満たすストリームに対して、
その子の要素がalternativeを満たす事を表現できないからである。つまり、
until P r r -> alternative Q P r ->  alternative P Q r
until P r r -> alternative P Q r ->  alternative Q P r
が繰り返されて、これは意図する挙動ではない。
*)

Inductive substream {T : Type} : Stream T -> Stream T -> Prop :=
  | next r : substream r (tl r)
  | further r r' : substream (tl r) r' -> substream r r'.

Inductive until {T : Type} (P : Stream T -> Prop) : Stream T -> Stream T -> Prop :=
  | here r : P r -> until P r (tl r)
  | later r r' : ~ P r -> until P (tl r) r' -> until P r r'.


CoInductive alternative  {T : Type} (P Q : Stream T -> Prop) : Stream T -> Prop :=
  | alt r r' : until P r r' -> alternative Q P r' ->  alternative P Q r.

Definition infinitely_often {T : Type} (P : Stream T -> Prop) s : Prop :=
  ForAll (fun s' => Exists (fun s'' => P s'') s') s.


Lemma substream_trans {T : Type} (r r' r'' : Stream T) :
  substream r r' -> substream r' r'' -> substream r r''.
Proof.
  move => H; move : r''.
  induction H => r'' H'.
  -  constructor; auto.
  - constructor; eauto.
Qed.  

Lemma until_substream {T} (t t' : Stream T) P :
  until P t t' -> substream t t'.
Proof.
  induction 1; try constructor => //.  
Qed.  

Lemma substream_infinitely_often {T} (l l' : Stream T) P :
  substream l l' -> infinitely_often P l' -> infinitely_often P l.
Proof.  
  induction 1.
  2: move /IHsubstream.
  all:
    move => H0;
    constructor; auto;
    inversion H0;
    constructor 2; auto.
Qed.


Lemma infinitely_switch {T} (P Q : Stream T -> Prop) (r : Stream T) :
  alternative P Q r -> infinitely_often P r.
Proof.  
  move : P Q r.
  cofix f => P Q r.
  assert (
    forall (P Q : Stream T -> Prop) (r : Stream T), alternative P Q r -> infinitely_often Q r
  ). 
  {
    move => P' Q' r' H.
    inversion_clear H.
    eapply substream_infinitely_often with r'0.
    - eapply until_substream; eauto.
    - eapply f. eauto.
  }
  inversion_clear 1.
  eapply substream_infinitely_often with r'.
  - eapply until_substream; eauto.
  - eapply H; eauto.
    (* Fail Guarded. *)
Abort.


Lemma infinitely_switch1 {T}
  (H : forall (P Q : Stream T -> Prop) (r : Stream T), alternative P Q r -> infinitely_often Q r) 
  (P Q : Stream T -> Prop) (r : Stream T) :
  alternative P Q r -> infinitely_often P r.
Proof.
  inversion_clear 1.
  eapply substream_infinitely_often with r'.
  - eapply until_substream; eauto.
  - eapply H; eauto.
Restart.
  inversion_clear 1.
  induction H1.
  - constructor.
    * constructor; auto.
    * eapply H; eauto.
  - apply IHuntil in H2.
    inversion H2.
    constructor; auto.
    constructor 2; auto.
Qed.
Print infinitely_switch1.     

Lemma infinitely_switch2 {T} 
  (H : forall (P Q : Stream T -> Prop) (r : Stream T), alternative P Q r -> infinitely_often P r) 
  (P Q : Stream T -> Prop) (r : Stream T) :
  alternative P Q r -> infinitely_often Q r.
Proof.
  inversion_clear 1.
  eapply substream_infinitely_often with r'.
  - eapply until_substream; eauto.
  - eapply H; eauto.
Qed.


(* it violates guaardness condition *)
Fail CoFixpoint infinitely_switch {T} (P Q : Stream T -> Prop) (r : Stream T) (H : alternative P Q r) : infinitely_often P r := 
  infinitely_switch1 (infinitely_switch2 infinitely_switch) P Q r H.




(* CoFixpoint infinitely_switch1 {T} (P Q : Stream T -> Prop) (r : Stream T) 
  (H : alternative P Q r) : infinitely_often P r :=
  let alt _ r' (Hr : until P r r') (Hr' : alternative Q P r') := H in 
  HereAndFurther (_ : Expsts P r) (
    HereAndFurther (_ : Exists P (tl r)) (
      ...
      HereAndFurther (_ : Exists P r') (infinitely_switch2 Q P r' (Hr') : infinitely_often P r')
    )
  )
  

with infinitely_switch2 {T} (P Q : Stream T -> Prop) (r : Stream T) 
  (H : alternative P Q r) : infinitely_often Q r :=
  let alt _ r' (Hr : until P r r') (Hr' : alternative Q P r') := H in
  HereAndFurther (_ : Exists Q r) (
    HereAndFurther (_ : Exists Q (tl r)) (
      ...
      HereAndFurther (_ : Exists Q r') (infinitely_switch1 (Hr') : infinitely_often Q r')
    )
  ). *)

(* Axiom P_dec : forall (P : Prop), {P} + {~ P}.
Axiom decE : forall P, reflect P (P_dec P). *)

CoInductive inf_until  {T : Type} (P : Stream T -> Prop) : Stream T -> Prop :=
  | inf r r' : until P r r' -> inf_until P r' ->  inf_until P r.

Inductive eventually {T : Type} (P : Stream T -> Prop) : Stream T -> Prop :=
  | e_here s r : P (Cons s r)  -> eventually P (Cons s r)
  | e_later s r : ~ P (Cons s r)  -> eventually P r -> eventually P (Cons s r).

Definition eventually_inv {T : Type} (P : Stream T -> Prop) (r : Stream T) :
  eventually P r  ->  ~ P r -> eventually P (tl r).
Proof.
  move => Hr F.
  inversion Hr; subst; auto.
  contradiction F.
Defined.

Lemma inf_often {T} (P : Stream T -> Prop) r (H : inf_until P r ) : infinitely_often P r.
Proof.
  move : r H.
  cofix inf_often => r H.
  inversion_clear H.
  constructor.
  - clear inf_often H1.
    induction H0.
    * constructor; auto.
    * constructor 2; auto.
  - eapply inf_often.
Restart.
  move : r H.
  cofix inf_often => r H.
  inversion_clear H.
  induction H0.
  - constructor.
    * constructor; auto.
    * eapply inf_often; eauto.
  - constructor.
    * clear inf_often IHuntil H1 H. 
      constructor 2.
      destruct r as [s r]; simpl in *; clear s.
      induction H0.
      + constructor; auto.
      + constructor 2; auto.
    * eapply IHuntil; auto.
Abort.    
  
  
 