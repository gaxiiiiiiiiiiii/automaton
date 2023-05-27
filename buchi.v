Require Export NFA.
Require Import Streams.

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
    cofix f => w r Hp Hb Hi.
    constructor.
    {
      clear f.      
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
      2:{eapply f; eauto. }
      { 
        clear E s1 s2.
        rename f into g.
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
              eapply g; eauto.              
              (* Fail Guarded. *)
          }

         } 
        }
        {
          destruct r as [[[s1 s2] b] r]; simpl in *; subst.
          inversion_clear Hp; simpl in *.
          inversion_clear Hi.
          rewrite in_set in H.
          move /andP : H => [_ Hb].
          remember (s2 ∈ accepts N2) as b eqn:E; destruct b; move /eqP : Hb => Hb.
          2:{
            eapply f; eauto.
          }
          {
            clear f He H1 E s1 s2.
            rename H2 into Hi.
            eapply g; eauto.
          }
        }        
      }
    }    
  }

Admitted.

CoFixpoint alternative_Stream 
  (L R : Type) (Pl : Stream L -> Prop) (Pr : Stream R -> Prop)
  (l : Stream L) (r : Stream R) 
  (Hl : infinitely_often Pl l) (Hr : infinitely_often Pr r) (b : bool): Stream bool  :=
  match Hl with
  | HereAndFurther He Hl' =>
    match He with
    | Here _ => 
      match Hr with
      | HereAndFurther _ Hr' => Cons b (alternative_Stream Hr' Hl' (~~ b))
      end   
    | Further He' => 
       match Hr with
      | HereAndFurther _ Hr' => Cons b (alternative_Stream Hl' Hr' b)
      end       
    end 
  end.
  


