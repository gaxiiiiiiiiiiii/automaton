From mathcomp Require Import fintype eqtype ssreflect ssrbool choice.

Require Import NonEmptyFintype.
Require Import NFA buchi.

Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation bin := bool.
Notation L := true.
Notation R := false.

CoInductive node := 
  | nil : node
  | cons : bin -> node -> node.

Definition unfold_node (u : node) : node :=
  match u with
  | nil => nil
  | cons b u' => cons b u'
  end.

Lemma unfold_node_eq u : u = unfold_node u.
Proof. destruct u; auto. Qed.


Notation λ := nil.
Infix "::" := cons (at level 60, right associativity).
Definition sucL (u : node)  := cons L u.
Definition sucR (u : node)  := cons R u.

CoInductive tree : node -> Type :=
  | tree_intro u :  tree (cons L u) -> tree (cons R u) -> tree u.


CoFixpoint app (u v : node) : node :=
  match u with
  | nil => v
  | cons b u' => cons b (app u' v)
  end.


Inductive above : node -> node -> Prop :=
  | above_nil u : above λ u
  | above_cons a u v : above u v -> above (cons a u) (cons a v).

Inductive above' : node -> node -> Prop :=
  | above'_refl u : above' u u
  | above'_cons a u v : above' u v -> above' u (cons a v). 




Definition aboveOf (x : node) : Ensemble node := 
  fun y => above x y.

Definition belowOf (u : node) : Ensemble node := 
  fun v => above v u.

Definition path pi : Prop :=
  exists u, pi = belowOf u.

Lemma belowOf_above u v :
  In (belowOf u) v -> above v u.
Proof. auto. Qed.  


Lemma above_trans u v w : 
  above u v -> above v w -> above u w.
Proof.
  move => H.
  move : w.
  induction H => w H'.
  - constructor.
  - inversion H'; subst; clear H'.
    constructor.
    eapply IHabove; auto.  
Qed.

Lemma above_antisym u v : 
  above u v -> above v u -> u = v.
Proof.  
  induction 1 => H0.
  - inversion H0; subst; auto.
  - congr cons; auto.
    inversion H0; subst.
    eauto.
Qed.    

  
Lemma above_total x y u: 
  above x u -> above y u -> above x y \/ above y x.
Proof.
  move => H.
  move : y.
  induction H => y H0.
  - left; constructor.
  - inversion H0; subst; clear H0.
    * right; constructor.
    * case : (IHabove _ H3) => In; clear IHabove; [left|right]; constructor; auto.
Qed.    


Lemma path_total pi x y:
  path pi -> In pi x -> In pi y -> above x y \/ above y x.
Proof.
  move => [u] ->.
  unfold belowOf, In => Hx Hy.
  eapply above_total; eauto.
Qed.
  

Definition lang (Σ : nonEmptyFintype) : Type:= (node -> Σ) * node .

Record rabin (Σ : nonEmptyFintype) := {
  stateR : nonEmptyFintype;
  initR : {SET stateR};
  transR : (stateR * Σ) -> {set (stateR * stateR)};
    (* nonEmptyFinType_of (default stateR, default stateR); *)
  accepts : {set stateR};
}.

Arguments stateR {Σ}.
Arguments initR {Σ}.
Arguments transR {Σ}.
Arguments accepts {Σ}.

Definition runR {Σ}(N : rabin Σ) (l : lang Σ) (r : node -> stateR N):= 
  (r λ) ∈ (initR N ) /\  (forall u, (r (sucL u), (r (sucR u))) ∈ transR N (r u, fst l u)).

        
(* rabin automatonの受理条件が、パスが無限長である事を前提とした定義になってるから、やり直し *)
