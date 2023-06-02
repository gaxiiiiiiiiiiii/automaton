Require Import Streams.

From mathcomp Require Import ssreflect.



Notation "¬ P" := (fun s => ~ P s)(at level 10).

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
    Fail Guarded.
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
Qed.

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

Print infinitely_switch1.
Print substream_infinitely_often.


Fail CoFixpoint infinitely_switch {T} 
  (P Q : Stream T -> Prop) (r : Stream T) (H : alternative P Q r) :infinitely_often P r :=
  infinitely_switch1 (infinitely_switch2 infinitely_switch) P Q r H.


Lemma infinitely_switch {T} (P Q : Stream T -> Prop) (r : Stream T) :
  alternative P Q r -> infinitely_often (fun s => P s \/ Q s) r.
Proof.  
  move : P Q r.
  cofix f => P Q r H.
  constructor.
  {
    inversion_clear H.
    clear f H1.
    induction H0.
    - constructor; left; auto.
    - constructor 2; auto.    
  }
  {
    inversion_clear H.
    inversion_clear H1.
    apply substream_infinitely_often with r'0.
    - eapply substream_trans with r';
      eapply until_substream; eauto.    


  }
Restart.
  
  
Abort.

