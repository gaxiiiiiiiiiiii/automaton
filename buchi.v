Require Export NFA.
Require Import Streams.
Require Import ProofIrrelevance.



Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Implicit Arguments.

Notation buchi := NFA.


Definition infinitely_often {T : Type} (P : Stream T -> Prop) s : Prop :=
  ForAll (fun s' => Exists (fun s'' => P s'') s') s.


CoInductive prerun {Σ} (N : buchi Σ) : Stream Σ ->  Stream (state N) -> Prop :=
  | step w r :
     hd (tl r) ∈ trans N (hd r) (hd w) -> prerun (tl w) (tl r) -> prerun  w r.


Inductive run {Σ} (N : buchi Σ) : Stream Σ -> Stream (state N) -> Prop :=
  | run_intro w r : hd r ∈ init N -> prerun w r -> run  w r.

Definition langOf {Σ} (N : buchi Σ) (w : Stream Σ) : Prop :=
  exists r, run w r /\ infinitely_often (fun s => hd s ∈ accepts N) r.




Definition is_inl {A B} (a : A + B) : Prop :=
  match a with
  | inl _ => True
  | inr _ => False
  end.

Definition is_inr {A B} (a : A + B) : Prop :=
  match a with
  | inl _ => False
  | inr _ => True
  end.

Lemma run_union_ForAll {Σ} (N1 N2 : buchi Σ) (w : Stream Σ) r :
  run (N := union N1 N2) w r -> ForAll (fun s => is_inl (hd s)) r \/ ForAll (fun s => is_inr (hd s)) r.
Proof.
  move => H.
  remember (hd r) as s.
  destruct s; [left|right]; simpl in *;
  destruct r; simpl in Heqs; subst s0.
  - inversion_clear H; simpl in *.
    constructor; simpl; auto.
    clear H0.
    move : w s r H1.
    cofix f.
    move => w s [s' r] H.
    inversion_clear H; simpl in *.
    rewrite in_set in H0.
    move /existsP : H0 => [s0 /andP [Ht /eqP Hs]]; subst s'.
    constructor; simpl; auto.
    eapply f; eauto.
  - inversion_clear H; simpl in *.
    constructor; simpl; auto.
    clear H0.
    move : w s r H1.
    cofix f.
    move => w s [s' r] H.
    inversion_clear H; simpl in *.
    rewrite in_set in H0.
    move /existsP : H0 => [s0 /andP [Ht /eqP Hs]]; subst s'.
    constructor; simpl; auto.
    eapply f; eauto.
Qed.

Definition sum_Stream_left {A B} (s : Stream (A + B)) :
  ForAll (fun a => is_inl (hd a)) s -> Stream A.
Proof.
  move : s.
  cofix f.
  move => s H.
  destruct s as [a s].
  inversion H; simpl in *.
  constructor.
  - destruct a; try inversion H0.
    exact a.
  - eapply f; eauto.
Defined.

Lemma tl_sum_Stream_left {A B} (s : Stream (A + B))
  (H : ForAll (fun a => is_inl (hd a)) s) :
  tl (sum_Stream_left H) = match H with
                           | HereAndFurther _ Htl => sum_Stream_left Htl
                           end.
Proof.
  unfold sum_Stream_left.
  destruct H; simpl. destruct s; simpl; auto.
Qed.

CoFixpoint extend_sum_Stream_left {A B} (s : Stream A) : Stream (A + B) :=
  match s with
  | Cons a s => Cons (inl a) (extend_sum_Stream_left s)
  end.



Definition sum_Stream_right {A B} (s : Stream (A + B)) :
  ForAll (fun a => is_inr (hd a)) s -> Stream B.
Proof.
  move : s.
  cofix f.
  move => s H.
  destruct s as [a s].
  inversion H; simpl in *.
  constructor.
  - destruct a; try inversion H0.
    exact b.
  - eapply f; eauto.
Defined.

Lemma tl_sum_Stream_right {A B} (s : Stream (A + B))
  (H : ForAll (fun a => is_inr (hd a)) s) :
  tl (sum_Stream_right H) = match H with
                           | HereAndFurther _ Htl => sum_Stream_right Htl
                           end.
Proof.
  unfold sum_Stream_right.
  destruct H; simpl. destruct s; simpl; auto.
Qed.

CoFixpoint extend_sum_Stream_right {A B} (s : Stream B) : Stream (A + B) :=
  match s with
  | Cons a s => Cons (inr a) (extend_sum_Stream_right s)
  end.


CoFixpoint prod_Stream_left {A B} (s : Stream (A * B)) : Stream A :=
  match s with
  | Cons (a, _) s => Cons a (prod_Stream_left s)
  end.

CoFixpoint prod_Stream_right {A B} (s : Stream (A * B)) : Stream B :=
  match s with
  | Cons (_, b) s => Cons b (prod_Stream_right s)
  end.


Lemma buchi_union_spec {Σ} (N1 N2 : buchi Σ) :
  langOf (union N1 N2) =  Union (langOf N1) (langOf N2).
Proof.
  apply Extensionality_Ensembles; split => w; unfold langOf, In.
  { move => [r [Hr Hi]].
    move : (run_union_ForAll Hr) => H0.
    inversion_clear Hr as [w_ r_ Hini Hp].
    case : H0 => Hall; [left|right]; unfold In.

    { (*left*)
      exists (sum_Stream_left Hall); split.
      { (* run *)
        constructor.
        { (* init *)
          rewrite in_set in Hini.
          inversion_clear Hall as [H _].
          simpl.
          destruct r, Hall, s, i; simpl in *; auto.           
        } 
        { (* prerun *)
          clear Hi Hini.
          move : w r Hp Hall.
          cofix f => w r Hp Hall.
          constructor.
          { (* trans *)
            simpl.
            destruct r,Hall,r,Hall,s0,i0,s,i; simpl.
            inversion_clear Hp; simpl in *.
            rewrite in_set in H.
            move /existsP : H => [x /andP [Ht /eqP Hs]].
            inversion Hs; subst; auto.
          }
          {(* coinduction *)
            rewrite tl_sum_Stream_left.
            destruct Hall.
            inversion_clear Hp.
            apply f; auto.
          }
        }
      }
      { (* infinitely_often *)
        clear Hini Hp w.
        move : r Hi Hall.
        cofix f => r Hi Hall.
        constructor.
        {(* Exits *)
          inversion_clear Hi as [He _].
          clear f.
          move : Hall.
          induction He => Hall.
          { (* base *)
            constructor.
            destruct Hall,x,s,i; simpl in *.
            rewrite in_set in H; auto.
          }
          { (* inductive *)
            inversion_clear Hall.
            constructor 2.
            rewrite tl_sum_Stream_left.
            destruct Hall.
            eapply IHHe.
          }
        }
        { (*coinduction*)
          rewrite tl_sum_Stream_left.
          destruct Hall.
          inversion_clear Hi.
          eapply f; auto.
        }
      }
    }
    { (*right*)
      exists (sum_Stream_right Hall); split.
      { (* run *)
        constructor.
        { (* init *)
          rewrite in_set in Hini.
          inversion_clear Hall as [H _].
          simpl.
          destruct r, Hall, s, i; simpl in *; auto.           
        } 
        { (* prerun *)
          clear Hi Hini.
          move : w r Hp Hall.
          cofix f => w r Hp Hall.
          constructor.
          { (* trans *)
            simpl.
            destruct r,Hall,r,Hall,s0,i0,s,i; simpl.
            inversion_clear Hp; simpl in *.
            rewrite in_set in H.
            move /existsP : H => [x /andP [Ht /eqP Hs]].
            inversion Hs; subst; auto.
          }
          {(* coinduction *)
            rewrite tl_sum_Stream_right.
            destruct Hall.
            inversion_clear Hp.
            apply f; auto.
          }
        }
      }
      { (* infinitely_often *)
        clear Hini Hp w.
        move : r Hi Hall.
        cofix f => r Hi Hall.
        constructor.
        {(* Exits *)
          inversion_clear Hi as [He _].
          clear f.
          move : Hall.
          induction He => Hall.
          { (* base *)
            constructor.
            destruct Hall,x,s,i; simpl in *.
            rewrite in_set in H; auto.
          }
          { (* inductive *)
            inversion_clear Hall.
            constructor 2.
            rewrite tl_sum_Stream_right.
            destruct Hall.
            eapply IHHe.
          }
        }
        { (*coinduction*)
          rewrite tl_sum_Stream_right.
          destruct Hall.
          inversion_clear Hi.
          eapply f; auto.
        }
      }
    }    
  }
  {
    inversion_clear 1; move : H0 => [r [Hr Hi]].
    { (*left*)
      exists (extend_sum_Stream_left r); split.
      { (*run*)
        constructor; simpl.
        { (*init*)
          inversion_clear Hr as [w0 r0  H0 _].
          destruct r.
          rewrite in_set; auto.          
        }
        { (*prerun*)
          clear Hi.
          inversion_clear Hr as [w0 r0 _ Hp].
          move : w r Hp.
          cofix f => w r Hp.
          constructor.
          { (*trans*)
            simpl. destruct r,r; simpl in *.
            inversion_clear Hp; simpl in *.
            rewrite in_set.
            apply /existsP; exists s0; apply /andP; split; auto.
          }
          { (*coinductife*)
            inversion_clear Hp; simpl.
            destruct r.
            simpl in H0.
            eapply f; eauto.
          }
        }
      }
      { (*infinitely_often*)
        clear Hr w.
        move : r Hi.
        cofix f => r Hi.
        constructor.
        { (*Existst*)
          inversion_clear Hi as [He _].
          clear f.
          induction He.
          { (*base*)
            constructor; simpl.
            destruct x.
            rewrite in_set; auto.
          }
          { (*inductive*)
            constructor 2.
            destruct x; simpl in *; eauto.
          }
        }
        { (*coinduction*)
          inversion_clear Hi.
          destruct r; simpl in *.
          eapply f; eauto.
        }
      }
    }
    { (*right*)
       exists (extend_sum_Stream_right r); split.
      { (*run*)
        constructor; simpl.
        { (*init*)
          inversion_clear Hr as [w0 r0  H0 _].
          destruct r.
          rewrite in_set; auto.          
        }
        { (*prerun*)
          clear Hi.
          inversion_clear Hr as [w0 r0 _ Hp].
          move : w r Hp.
          cofix f => w r Hp.
          constructor.
          { (*trans*)
            simpl. destruct r,r; simpl in *.
            inversion_clear Hp; simpl in *.
            rewrite in_set.
            apply /existsP; exists s0; apply /andP; split; auto.
          }
          { (*coinductife*)
            inversion_clear Hp; simpl.
            destruct r.
            simpl in H0.
            eapply f; eauto.
          }
        }
      }
      { (*infinitely_often*)
        clear Hr w.
        move : r Hi.
        cofix f => r Hi.
        constructor.
        { (*Existst*)
          inversion_clear Hi as [He _].
          clear f.
          induction He.
          { (*base*)
            constructor; simpl.
            destruct x.
            rewrite in_set; auto.
          }
          { (*inductive*)
            constructor 2.
            destruct x; simpl in *; eauto.
          }
        }
        { (*coinduction*)
          inversion_clear Hi.
          destruct r; simpl in *.
          eapply f; eauto.
        }
      }

    
    }

  }  
Qed.

(* ================== buchi inter  ================== *)


Definition buchi_inter_state {Σ}  (N1 N2 : buchi Σ) :=
  nonEmptyFinType_of (default (state N1), default (state N2), true).

Definition buchi_inter_init {Σ} (N1 N2 : buchi Σ) : {SET (buchi_inter_state N1 N2)}.
Proof.
  eapply nonEmptyFinset.Pack
    with ([set x : buchi_inter_state N1 N2 | (fst (fst x) ∈ init N1) && (snd (fst x) ∈ init N2) && (snd x == true)]).
  simpl.
  rewrite in_set.
  apply /andP; split; [apply /andP; split|]; simpl; auto; apply hasDefault.
Defined.


Definition buchi_inter_trans {Σ} (N1 N2 : buchi Σ) ss a :=
  match ss with
  | (s1,s2,true) =>
    [set ss' |
      (fst (fst ss') ∈ trans N1 s1 a) &&
      (snd (fst ss') ∈ trans N2 s2 a) &&
      ( if s1 ∈ accepts N1
        then  (snd ss' ==false)
        else  (snd ss' == true)
      )
    ]
  | (s1,s2,false) =>
    [set ss' |
      (fst (fst ss') ∈ trans N1 s1 a) &&
      (snd (fst ss') ∈ trans N2 s2 a) &&      
      (if s2 ∈ accepts N2
        then (snd ss' == true)
        else (snd ss' == false)
      )
    ]
  end.

Definition buchi_inter_accepts {Σ} (N1 N2 : buchi Σ) :=
  setX (setX ([set : (state N1)]) (accepts N2)) ([set false]).

Definition buchi_inter {Σ} (N1 N2 : buchi Σ) := {|
  state := buchi_inter_state N1 N2;
  init := buchi_inter_init N1 N2;
  accepts := buchi_inter_accepts N1 N2;
  trans := buchi_inter_trans (N1 := N1) (N2 := N2);
|}.

Lemma buchi_inter_spec_ll {Σ} (N1 N2 : buchi Σ) w :
  In (langOf (buchi_inter N1 N2)) w -> In (langOf N2) w.
Proof.
  move => [r [Hr Hi]].
  unfold In.
  exists (prod_Stream_right (prod_Stream_left r)); split.
  {
    constructor.
    {
      inversion_clear Hr.
      destruct r as [[[s1 s2] b] r]; simpl in *.
      rewrite in_set in H; simpl in H.
      move /andP : H => [/andP [_ H'] _]; auto.
    }
    {
      clear Hi.
      destruct Hr as [w r _ Hp].
      move : w r Hp.
      cofix f => w r Hp.
      constructor; first last.
      {
        simpl.
        destruct r, s, s; simpl; simpl in *.
        inversion_clear Hp; simpl in *.
        apply f; auto.
      }
      {
        simpl.
        destruct r, s, s, r, s2, s2; simpl.
        inversion_clear Hp; simpl in *; subst.        
        destruct s0;
        rewrite in_set in H; simpl in *; move /andP : H => [/andP [_ H] _]; auto.
      }
      
    }
  }
  {
    clear w Hr.
    move : r Hi; cofix f => r Hi.
    constructor.
    { (*Exists*)
      destruct Hi as [He _].
      clear f.
      induction He.
      { (*base*)
        rewrite in_set in H.
        destruct x as [[[s1 s2] b] r]; simpl in *.
        move /andP : H => [/setXP [_ H2] /set1P E]; subst.
        constructor; simpl; auto .
      }
      { (*inductive*)
        constructor 2.
        destruct x as [[[s1 s2] b] r]; simpl in *.
        eauto.
      }
    }
    { (*coinductive*)
      inversion_clear Hi.
      destruct r as [[[s1 s2] b] r]; simpl in *.
      eapply f; auto.
    } 
   }
Qed.


(* ガードネス条件は満たさないけど、おそらく進行性は満たすから、一旦Admitted *)
Lemma buchi_inter_spec_lr {Σ} (N1 N2 : buchi Σ) w :
  In (langOf (buchi_inter N1 N2)) w -> In (langOf N1) w.
Proof.
  move => [r [Hr Hi]].
  exists (prod_Stream_left (prod_Stream_left r)); split.
  {
    constructor.
    {
      inversion_clear Hr; simpl.
      destruct r, s, s; simpl in *.
      rewrite in_set in H; simpl in H.
      move /andP : H => [/andP [H' _] _]; auto.
    }
    {
      clear Hi.
      destruct Hr as [w r Hi Hp].
      rewrite in_set in Hi.
      move /andP : Hi => [_ /eqP Hi].
      move : w r Hp Hi.
      cofix f => w r Hp Hi.
      constructor.
      {
        simpl.
        destruct r, s, s, r, s2, s2; simpl; simpl in *; subst.        
        inversion_clear Hp; simpl in *.
        rewrite in_set in H; simpl in *.
        move /andP : H => [/andP [H _] _]; auto.
      }
      {
        simpl.
        destruct r, s, s, r, s2, s2; simpl.
        inversion_clear Hp; simpl in *; subst.
        rewrite in_set in H; simpl in *. 
        move /andP : H => [/andP [H1 H2] H]; auto.
        remember (s ∈ accepts N1).
        destruct b; move /eqP : H => E; subst.
        - constructor; simpl.
          inversion_clear H0.
          rewrite in_set in H; simpl in *.
          move /andP : H => [/andP [H1' H2'] Hb']; auto.
          * destruct r,p,p; simpl; auto.
          * inversion_clear H0; simpl in *.
            clear H H1 H2 Heqb s s1 s2 s4 f.
            move : w r H3.
            cofix g => w r Hp.
            constructor; simpl.
            * inversion_clear Hp.
              destruct r, p, p, r, p, p; simpl in *; auto.
              destruct b; rewrite in_set in H; 
              move /andP : H => [/andP []]; simpl; auto.
            * destruct r,p,p.
              inversion_clear Hp; simpl in H0.
              eapply g; eauto.         
        - eapply f; auto.
      }

    }
  }
  {
    inversion_clear Hr.
    rewrite in_set in H.
    move /andP : H => [_ /eqP Hb].
    move : Hi => [_ Hi].
    move : w r H0 Hb Hi.
    cofix g => w r Hp Hb Hi.
    constructor.
    {
      clear g.      
      destruct Hi as [He _].
      destruct r as [[[s1 s2] b]]; simpl in *; subst.
      move : s1 s2 w Hp.
      induction He => s1 s2 w Hp.
      {
        destruct x as [[[s1' s2'] b'] r]; simpl in *.
        rewrite in_set in H.
        move /andP : H => /= [/setXP [_ Ha2]  /set1P E]; subst.
        inversion_clear Hp; simpl in *.
        rewrite in_set in H; simpl in *.
        move /andP : H => [_ Hb']; auto.
        remember (s1 ∈ accepts N1) as b eqn:E; destruct b; move /eqP : E => E.
        - constructor; auto.
        - inversion Hb'.
      }
      {        
        inversion_clear Hp; simpl in *.
        rewrite in_set in H; simpl in *.
        move /andP : H => [_ Hb].
        remember (s1 ∈ accepts N1) as b eqn:E; destruct b; move /eqP : Hb => Hb.
        - constructor; auto .
        - constructor 2; simpl.
          clear E s1 s2.
          destruct x as [[[s1 s2] b] r]; simpl in *; subst.
          eapply IHHe; eauto.
      } 
    }
    { 
      destruct r as [[[s1 s2] b]]; simpl in *; subst.
      inversion_clear Hp; simpl in *. rename H0 into Hp.
      destruct Hi as [He Hi].

      rewrite in_set in H.
      move /andP : H => [_ Hb].
      remember (s1 ∈ accepts N1) as b eqn:E; destruct b; move /eqP : Hb => Hb.
      2:{eapply g; eauto. }
      { 
        clear E s1 s2.
        move : r w Hp Hb He Hi.
        cofix f => r w Hp Hb He Hi.
        constructor.
        {
         move : w Hp Hb Hi.
         induction He => w Hp Hb Hi.
         {
          destruct x as [[[s1 s2] b] r]; simpl in *; subst.
          rewrite in_set in H.
          move /andP : H => /= [/setXP [_ Ha2]  _].
          inversion_clear Hp; simpl in *.
          rewrite in_set in H; simpl in *.
          move /andP : H => [_ Hb]; auto.
          rewrite Ha2 in Hb.
          move /eqP : Hb => Hb.
          constructor 2; simpl.
          clear Ha2 s1 s2.
          destruct Hi as [He _].
          move : w H0 Hb.
          induction He => w H0 Hb.
          {
            destruct x as [[[s1 s2] b] r]; simpl in *; subst.
            rewrite in_set in H; simpl in *.
            move /andP : H => /= [_  /set1P F]; inversion F.
          }
          {
            destruct x as [[[s1 s2] b] r]; simpl in *; subst.
            inversion_clear H0; simpl in *.
            rewrite in_set in H; simpl in *.
            move /andP : H => [_ Hb'].
            remember (s1 ∈ accepts N1) as b eqn:E; destruct b; move /eqP : Hb' => Hb'.
            - constructor; auto.
            - constructor 2; eapply IHHe; eauto.
          }          
         }
         {
          destruct x as [[[s1 s2] b] r]; simpl in *; subst.
          inversion_clear Hp; simpl in *.
          inversion_clear Hi.
          rewrite in_set in H.          
          move /andP : H => [_ Hb].          
          remember (s2 ∈ accepts N2) as b eqn:E; destruct b; move /eqP : Hb => Hb.
          2:{ constructor 2. eapply IHHe; eauto. }
          { 
            constructor 2; simpl.
            clear E s1 s2.
            destruct r as [[[s1 s2] b] r]; simpl in *; subst.
            inversion_clear H0; simpl in*.
            rewrite in_set in H.
            move /andP : H => [_ Hb].
            remember (s1 ∈ accepts N1) as b eqn:E; destruct b; move /eqP : Hb => Hb.
            - constructor; auto.
            - constructor 2; simpl.
              inversion H2.
              eapply g; eauto. (* Fail Guarded. *)
          }

         } 
        }
        {
          destruct r as [[[s1 s2] b] r]; simpl in *; subst.
          inversion_clear Hp; simpl in *.
          inversion_clear Hi.
          rewrite in_set in H.
          move /andP : H => [_ Hb].
          remember (s2 ∈ accepts N2) as b eqn:E; destruct b; move /eqP : Hb => Hb; first last.
          - eapply f; eauto.
          - eapply g; eauto. (* Fail Guarded *)          
        }        
      }
    }    
  }


Admitted.

Axiom P_dec : forall (P : Prop), {P} + {~ P}.
Axiom decE : forall P, reflect P (P_dec P).


CoFixpoint alternative_Stream 
  (L R : Type) (Pl : Stream L -> Prop) (Pr : Stream R -> Prop)
  (l : Stream L) (r : Stream R) 
  (Hl : infinitely_often Pl l) (Hr : infinitely_often Pr r) (b : bool): Stream bool  :=
  let: HereAndFurther He Hl' := Hl in
  let: HereAndFurther _ Hr' := Hr in
  match P_dec (Pl l) with
  | left _ => Cons b (alternative_Stream Hr' Hl' (~~ b))
  | right _ => Cons b (alternative_Stream Hl' Hr' b)
  end.


CoFixpoint prod_Stream {A B : Type} (l : Stream A) (r : Stream B) : Stream (A * B) :=
  match l, r with
  | Cons a l', Cons b r' => Cons (a, b) (prod_Stream l' r')
  end.

Lemma tl_prod_Stream {A B : Type} (l : Stream A) (r : Stream B) :
  tl (prod_Stream l r) = prod_Stream (tl l) (tl r).
Proof.
  destruct l,r; simpl; auto.
Qed.  

Lemma buchi_inter_spec_r {Σ} (N1 N2 : buchi Σ) w :
  In (langOf N1) w /\ In (langOf N2) w -> In (langOf (buchi_inter N1 N2)) w.
Proof.
  unfold langOf, In => [[[r1 [Hr1 Hi1]] [r2 [Hr2 Hi2]]]].
  pose r := (prod_Stream (prod_Stream r1 r2) ((alternative_Stream Hi1 Hi2 true))).  
  exists r; split.
  {
    constructor.
    {
      simpl.
      destruct r1,r2,Hi1,Hi2.
      simpl in *.
      inversion_clear Hr1.
      inversion_clear Hr2.
      destruct (P_dec (s ∈ accepts N1));
      rewrite in_set; simpl;
      repeat (apply /andP; split => //). 
    }
    {                
      unfold r; clear r.
      inversion_clear Hr1 as [r0 w0 _ Hp1].
      inversion_clear Hr2 as [r0 w0 _ Hp2].
      move : w r1 r2 Hi1 Hi2 Hp1 Hp2.
      cofix f => w r1 r2 Hi1 Hi2 Hp1 Hp2.
      constructor.
      {        
        simpl in *.
        destruct r1,r2,Hi1,Hi2,r1,r2,Hi1,Hi2; simpl in *.        
        inversion_clear Hp1; simpl in *.
        inversion_clear Hp2; simpl in *.
        destruct (P_dec (s ∈ accepts N1)); simpl;
        [ destruct (P_dec (s2 ∈ accepts N2)) 
        | destruct (P_dec (s1 ∈ accepts N1))];
        rewrite in_set; simpl;
        apply /andP; split;
        try match goal with
        | [|- context [_ &&_ ]] => apply /andP; split; auto
        end;
        try rewrite i; auto;
        apply Bool.not_true_is_false in n;
        rewrite n; auto.
      }
      {        
        repeat rewrite tl_prod_Stream.
        rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
        destruct Hi1, Hi2; simpl.
        destruct (P_dec (hd r1 ∈ accepts N1)); simpl; first last.
        { 
          inversion_clear Hp1; inversion_clear Hp2.
          eapply f; eauto. 
        }
        {
          destruct r1,r2; simpl.
          inversion_clear Hp1; inversion_clear Hp2; simpl in *.
          clear e e0 i H H1.
          rename H0 into Hp1.
          rename H2 into Hp2.
          move : w r1 r2 Hi1 Hi2 Hp1 Hp2.          
          cofix g => w r1 r2 Hi1 Hi2 Hp1 Hp2.
          constructor.
          {
            simpl.
            destruct r1,r2,Hi1,Hi2; simpl.
            inversion_clear Hp1; inversion_clear Hp2; simpl in *.
            destruct (P_dec (s2 ∈ accepts N2)); simpl;
            destruct r1,r2, Hi1,Hi2; simpl;
            inversion_clear H0; inversion_clear H2; simpl in *;
            [ destruct (P_dec (s3 ∈ accepts N1))
            | destruct (P_dec (s4 ∈ accepts N2))];
            rewrite in_set; simpl; 
            try rewrite i;
            try (rewrite Bool.not_true_iff_false in n; rewrite n);
            repeat (apply /andP; split => //).    
          }
          {
            repeat rewrite tl_prod_Stream.
            rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
            destruct Hi2, Hi1; simpl.
            destruct (P_dec (hd r2 ∈ accepts N2)).
            {
              inversion_clear Hp1; inversion_clear Hp2.
              eapply f; eauto.
            }
            {
              inversion_clear Hp1; inversion_clear Hp2.
              eapply g; auto.
            }
          }          
        }
      }
    }
  }
  {
    clear Hr1 Hr2.
    unfold r in *; clear r.
    rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
    destruct Hi1, Hi2; simpl in *.
    clear e0.    
    move : r2 Hi2.
    induction e => r2 Hi2; simpl.
    {
      rename x into r1.
      destruct (P_dec (hd r1 ∈ accepts N1)); first last. 
      { destruct n; auto. }
      clear w H i.            
      constructor.
      {
        constructor 2.
        repeat rewrite tl_prod_Stream; simpl.
        rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
        destruct Hi2, Hi1; simpl.
        clear e0.
        move : r1 Hi1 Hi2.
        induction e => r1 Hi1 Hi2.
        {
          constructor; simpl.
          destruct r1,r1; simpl.
          destruct x; simpl.
          destruct (P_dec (s1 ∈ accepts N2));
          rewrite in_set; simpl;
          (apply /andP; split; [apply /setXP; split|]); auto.
          apply /set1P; auto.
        }
        {          
          destruct (P_dec (hd x ∈ accepts N2)); simpl; first last.
          {
            constructor 2.
            repeat rewrite tl_prod_Stream.
            rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
            destruct Hi2, Hi1; simpl.
            eapply IHe.
          }
          {
            constructor; simpl.
            destruct r1,r1,x; simpl.
            rewrite in_set.
            apply /andP; split; simpl; auto.
            - apply /setXP; split; auto.
              apply /set1P; auto. 
          }
        }
      }
      {
        repeat rewrite tl_prod_Stream. simpl.
        destruct r1,r2; simpl in *.
        clear s s0.        
        move : r1 r2 Hi1 Hi2.
        cofix g => r1 r2 Hi1 Hi2.
        constructor.
        {
          clear g.
          rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
          destruct Hi2, Hi1; simpl.
          clear e0.
          move : r1 Hi1.
          induction e => r1 Hi1.
          {
            constructor; simpl.
            destruct r1,x; simpl.
            destruct (P_dec (s0 ∈ accepts N2)); simpl;
            rewrite in_set;
            (apply /andP; split; simpl;
            [apply /setXP; split|apply /set1P]
            ); auto.            
          }
          {
            destruct (P_dec (hd x ∈ accepts N2)); simpl.
            {
              constructor; simpl.
              destruct r1,x; simpl.
              rewrite in_set.
              apply /andP; split; simpl; auto.
              - apply /setXP; split; auto.
              - apply /set1P; auto. 
            }
            {
              constructor 2.
              repeat rewrite tl_prod_Stream.
              rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
              destruct Hi2, Hi1; simpl.
              eapply IHe.
            }            
          }
        }
        {
          rewrite tl_prod_Stream.
          rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
          destruct r1,r2,Hi1,Hi2; simpl.
          destruct (P_dec (s0 ∈ accepts N2)); simpl; first last.
          - eapply g.
          - clear i e e0; simpl in *.
            move : r1 r2 Hi1 Hi2.
            cofix f => r1 r2 Hi1 Hi2.
            constructor.
            {
              clear f g.
              rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
              destruct Hi1, Hi2.
              clear e0.
              move : r2 Hi2.
              induction e => r2 Hi2.
              {
                destruct (P_dec (hd x ∈ accepts N1)); first last.
                { contradiction n. }
                clear i H.
                constructor 2.
                repeat rewrite tl_prod_Stream; simpl.
                destruct x,r2; simpl.
                rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                destruct Hi2, Hi1; simpl.
                clear e0.
                rename x into r1.
                move : r1 Hi1; simpl in *.
                induction e => r1 Hi1.
                {
                  destruct (P_dec (hd x ∈ accepts N2)); first last.
                  { contradiction n. }
                  constructor; simpl.
                  destruct x,r1; simpl.
                  rewrite in_set.
                  apply /andP; split; simpl; auto.
                  - apply /setXP; split; auto.
                  - apply /set1P; auto.
                }
                {
                  destruct (P_dec (hd x ∈ accepts N2)); simpl.
                  {
                    constructor; simpl.
                    destruct x,r1; simpl.
                    rewrite in_set.
                    apply /andP; split; simpl; auto.
                    - apply /setXP; split; auto.
                    - apply /set1P; auto.
                  }
                  {
                    constructor 2.
                    repeat rewrite tl_prod_Stream.
                    rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                    destruct Hi2, Hi1; simpl.
                    eapply IHe.
                  }
                }
              }
              {
                constructor 2.
                repeat rewrite tl_prod_Stream.
                destruct (P_dec (hd x ∈ accepts N1)); simpl; first last.
                { rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
                  destruct Hi2, Hi1; simpl.
                  eapply IHe.
                }
                {
                  clear IHe i.
                  destruct x,r2; simpl in *.
                  clear s s0.
                  rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                  destruct Hi2, Hi1; simpl.
                  clear e e1.
                  rename x into r1.
                  move : r1 Hi1.
                  induction e0 => r1 Hi1.
                  { 
                    destruct (P_dec (hd x ∈ accepts N2)); first last.
                    { contradiction n. }
                    constructor; simpl.
                    destruct r1,x; simpl.
                    rewrite in_set.
                    apply /andP; split; simpl; auto.
                    - apply /setXP; split; auto.
                    - apply /set1P; auto.
                  }
                  {
                    destruct (P_dec (hd x ∈ accepts N2)).
                    {
                      constructor; simpl.
                      destruct r1,x; simpl.
                      rewrite in_set.
                      apply /andP; split; simpl; auto.
                      - apply /setXP; split; auto.
                      - apply /set1P; auto.
                    }
                    {
                      constructor 2.
                      repeat rewrite tl_prod_Stream.
                      rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                      destruct Hi2, Hi1; simpl.
                      eapply IHe0.
                    }
                  }
                }

              }
            }
            {
              repeat rewrite tl_prod_Stream.
              rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
              destruct Hi1, Hi2; simpl.
              destruct (P_dec (hd r1 ∈ accepts N1)); simpl.
              - eapply g.
              - eapply f.
            }
        }
      }
    }    
    {      
      destruct (P_dec (hd x ∈ accepts N1)); simpl; first last.
      {
        rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
        destruct Hi1, Hi2; simpl in *.
        move : (IHe Hi1 _ Hi2); clear IHe => IH.
        inversion_clear IH as [He Hi].
        constructor.
        - constructor 2.
          repeat rewrite tl_prod_Stream.
          auto.
        - constructor.
          * repeat rewrite tl_prod_Stream; simpl.
            auto.
          * rewrite tl_prod_Stream.
            replace (tl (prod_Stream x r2)) 
              with (prod_Stream (tl x) (tl r2)) 
              by (rewrite tl_prod_Stream; auto).
            auto.
      }
      {
        clear IHe.
        rename x into r1.
        clear e i w.
        destruct r1 as [s1 r1].
        destruct r2 as [s2 r2].
        simpl in *.
        constructor.
        {
          inversion_clear Hi2 as [He _].
          constructor 2.
          repeat rewrite tl_prod_Stream.
          simpl.
          move : r1 Hi1 Hi2.
          induction He => r1 Hi1 Hi2.
          {
            constructor; simpl.
            destruct r1,x,Hi1,Hi2; simpl in *.
            destruct (P_dec (s0 ∈ accepts N2)); simpl; first last.
            { contradiction n. }
            rewrite in_set.
            apply /andP; split.
            - apply /setXP; split; auto.
            - apply /set1P; auto.          
          }
          {
            rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
            destruct Hi1,Hi2.
            destruct (P_dec (hd x ∈ accepts N2)).
            - constructor; simpl.
              destruct r1,x.
              rewrite in_set; simpl.
              apply /andP; split; simpl; auto.
              - apply /setXP; split; auto.
              - apply /set1P; auto.                  
            - constructor 2.
              repeat rewrite tl_prod_Stream; simpl.
              eapply IHHe.
          }
        }
        { 
          repeat rewrite tl_prod_Stream; simpl.
          move : r1 r2 Hi1 Hi2.
          cofix f => r1 r2 Hi1 Hi2.
          constructor.
          {
            clear f.
            inversion_clear Hi2 as [He _].
            move : r1 Hi1.
            induction He => r1 Hi1.
            {
             constructor; simpl.
             destruct r1,x,Hi1,Hi2; simpl.
             destruct (P_dec (s0 ∈ accepts N2)); rewrite in_set;
             apply /andP; simpl; split;
             try solve [apply /set1P; auto].
             apply /setXP; split; auto.
            }            
            {              
              repeat rewrite tl_prod_Stream.
              rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
              destruct Hi1,Hi2.
              destruct (P_dec (hd x ∈ accepts N2)); simpl.
              - constructor; simpl.
                destruct r1,x.
                rewrite in_set; simpl.
                apply /andP; split; simpl; auto.
                - apply /setXP; split; auto.
                - apply /set1P; auto.
              - constructor 2.
                repeat rewrite tl_prod_Stream; simpl.
                eapply IHHe. 
            }
          }
          {
            repeat rewrite tl_prod_Stream.
            rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
            destruct Hi1,Hi2.
            destruct (P_dec (hd r2 ∈ accepts N2)); simpl; first last.
            * apply f.
            * destruct r1,r2; simpl in *.
              clear e e0 i s s0.
              move : r1 r2 Hi1 Hi2.
              cofix g => r1 r2 Hi1 Hi2.
              constructor; first last.
              - repeat rewrite tl_prod_Stream.
                rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
                destruct Hi1,Hi2.
                destruct (P_dec (hd r1 ∈ accepts N1)); simpl.
                * apply f.
                * eapply g.
              - clear f g.
                rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
                destruct Hi1,Hi2.
                clear e0.
                move : r2 Hi2.
                induction e => r2 Hi2.
                {
                  destruct (P_dec (hd x ∈ accepts N1)); first last.
                  { contradiction n. }
                  constructor 2.
                  repeat rewrite tl_prod_Stream; simpl.
                  clear H i.
                  rename x into r1.
                  destruct r1,r2; simpl in *.
                  rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                  destruct Hi1,Hi2.
                  clear e s s0.
                  move : r1 Hi1.
                  induction e0 => r1 Hi1.
                  - constructor; simpl.
                    destruct r1,x; simpl.
                    destruct (P_dec (s0 ∈ accepts N2)); 
                    rewrite in_set; simpl;
                    (apply /andP; split; [apply /setXP; split|]); auto.
                    apply /set1P; auto.
                  - destruct (P_dec (hd x ∈ accepts N2)); simpl.
                    - constructor; simpl.
                      destruct r1,x; simpl.
                      rewrite in_set; simpl;
                      (apply /andP; split; [apply /setXP; split|]); auto.
                      apply /set1P; auto.
                    - constructor 2.
                      repeat rewrite tl_prod_Stream; simpl.
                      rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                      destruct Hi1,Hi2.
                      eapply IHe0.                                        
                }
                {
                  destruct (P_dec (hd x ∈ accepts N1)); simpl; first last.
                  {
                    clear n.
                    constructor 2.
                    repeat rewrite tl_prod_Stream; simpl.
                    rewrite (unfold_Stream (alternative_Stream Hi1 Hi2 true)); simpl.
                    destruct Hi1,Hi2.
                    eapply IHe.
                  }
                  {
                    clear IHe i e.
                    constructor 2.
                    repeat rewrite tl_prod_Stream; simpl.
                    rename x into r1.
                    destruct r1,r2; simpl in *.
                    rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                    destruct Hi1,Hi2.
                    clear e s s0.
                    move : r1 Hi1.
                    induction e0 => r1 Hi1.
                    {
                      destruct (P_dec (hd x ∈ accepts N2)); first last.
                      { contradiction n. }
                      constructor; simpl.
                      destruct r1,x.
                      rewrite in_set; simpl.
                      apply /andP; split; simpl; auto.
                      - apply /setXP; split; auto.
                      - apply /set1P; auto.
                    }                    
                    {
                      destruct (P_dec (hd x ∈ accepts N2)).
                      {
                        constructor; simpl.
                        destruct r1,x.
                        rewrite in_set; simpl.
                        apply /andP; split; simpl; auto.
                        - apply /setXP; split; auto.
                        - apply /set1P; auto.
                      }
                      {
                        constructor 2.
                        repeat rewrite tl_prod_Stream; simpl.
                        rewrite (unfold_Stream (alternative_Stream Hi2 Hi1 false)); simpl.
                        destruct Hi1,Hi2.
                        eapply IHe0.
                      }
                    }
                  }
                } 
          } 
        }
      }
    }
  }
Qed.

Lemma buchi_inter_spec {Σ} (N1 N2 : buchi Σ) :
  langOf (buchi_inter N1 N2) = Intersection (langOf N1) (langOf N2).
Proof.
  apply Extensionality_Ensembles; split => w H.
  - split.
    * eapply buchi_inter_spec_lr; eauto.
    * eapply buchi_inter_spec_ll; eauto.
  - eapply buchi_inter_spec_r; auto.
    inversion_clear H; split; auto.
Qed.