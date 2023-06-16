From mathcomp Require Import fintype eqtype ssreflect ssrbool choice.

Require Import NonEmptyFintype.
Require Import NFA.

Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation bin := bool.
Notation L := true.
Notation R := false.

(* 教科書ではT := {1,0}^* としてるけど、ツリーのノードでは有限だから一応nilも含めている *)
(* CoInductive node := 
  | nil : node
  | cons : bin -> node -> node. *)
Notation node := (list bin).
Notation λ := nil.
(* Infix "::" := cons (at level 60, right associativity). *)
Definition sucL (u : node)  := cons L u.
Definition sucR (u : node)  := cons R u.

(* 必要かわかんないけど、一応 *)
(* Definition is_fin (u : node) : Prop := 
  match u with
  | nil => True
  | cons _ u' => False
  end.
Definition is_inf (u : node) : Prop := ~ is_fin u.
Definition inf_node := {u : node | is_inf u}.
Definition fin_node := {u : node | is_fin u}. *)




(* CoFixpoint app (u v : node) : node :=
  match u with
  | nil => v
  | cons b u' => cons b (app u' v)
  end. *)

Inductive above : node -> node -> Prop :=
  | above_refl u : above u u
  | above_cons b u v : above u v -> above u (cons b v).

(* Ensemble で良いのかは疑問が残る *)
Definition aboveOf (x : node) : Ensemble node := fun y => above x y.


(* おそらく無限の二分木だからCoInductiveだけど、ちょと自信がない。 *)
CoInductive tree : node -> Type :=
  | tree_intro u :  tree (cons L u) -> tree (cons R u) -> tree u.

Fixpoint subs (u : node) : Ensemble node := fun v => 
  match u with
  | nil => u = v
  | cons a u' => v = u \/ subs u' v
  end.


Definition path pi : Prop :=
  exists u, pi = subs u.


(* おそらく無限の二分木だからCoInductiveだけど、ちょと自信がない。 *)

(* Definition path (pi : Ensemble node) : Prop := *)
  (* In _ pi λ /\ (forall u, In _ pi u -> In _ pi (sucL u) \/ In _ pi (sucR u)). *)

Lemma subs_above u v :
  In (subs u) v -> above v u.
Proof.
  move : v.
  induction u; rewrite /In => /= v H.
  - subst.
    constructor.
  - case : H => H.
    * subst.
      constructor.
    * constructor 2; auto.
Qed.    


Lemma above_nil u : above λ u.
Proof.
  induction u.
  - by apply above_refl.
  - by apply above_cons.
Qed.

Lemma above_trans u v w : above u v -> above v w -> above u w.
Proof.
  move => Huv Hvw.
  move : u Huv.
  induction Hvw => u0 H //=.
  constructor 2.
  apply IHHvw; auto.
Qed.


Lemma path_total :
  forall pi x y, path pi -> In pi x -> In pi y -> above x y \/ above y x.
Proof.  
  move => pi x y [u] ->.
  move : x y.
  induction u => x y Hx Hy.
  - simpl in *.
    unfold In in *; subst.
    left; constructor.
  - unfold In in *.
    simpl in *.
    case : Hx => Hx;
    case : Hy => Hy; subst.
    * left; constructor.
    * right.
      constructor.      
      apply subs_above; auto.
    * left.
      constructor.
      apply subs_above; auto.
    * apply IHu; auto.
Qed.   

Definition lang (Σ : nonEmptyFintype) : Type:= (node -> Σ) * node .

Record rabin (Σ : nonEmptyFintype) := {
  stateR : nonEmptyFintype;
  initR : {SET stateR};
  transR : (stateR * Σ) -> {set (stateR * stateR)};
    (* nonEmptyFinType_of (default stateR, default stateR); *)
  accepts : {set stateR};
}.

(* Set Implicit Arguments of rabin fields *)
Arguments stateR {Σ}.
Arguments initR {Σ}.
Arguments transR {Σ}.
Arguments accepts {Σ}.

Definition runR {Σ}(N : rabin Σ) (l : lang Σ) (r : node -> stateR N):= 
  (r λ) ∈ (initR N ) /\  (forall u, (r (sucL u), (r (sucR u))) ∈ transR N (r u, fst l u)).

        
(* rabin automatonの受理条件が、パスが無限長である事を前提とした定義になってるから、やり直し *)
