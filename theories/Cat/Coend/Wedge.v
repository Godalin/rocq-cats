From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Import
  Cat.Functor.OppositeProduct.
From Cats Require Export
  Cat.End.Wedge.

(** * Cowedges from Opposite Wedges *)

(** * 从反楔派生余楔 *)

(** A cowedge stores just a wedge of the opposite bifunctor. Its ordinary
    legs go from [F (X,X)] to the apex. *)

(** 余楔只存储反双函子的楔，其通常方向的腿从 [F (X,X)] 指向顶点。 *)

Record Cowedge {C D : Cat} (F : Functor ((C^op) ×C C) D) (W : @Ob D)
  :=
  (** The sole stored presentation is a wedge in the opposite categories. *)

  (** 唯一存储的表示是反范畴中的楔。 *)

  { op_wedge : @Wedge (C^op) (D^op) (BifunctorOpF F) W
  }.

Arguments op_wedge {_ _ _ _} _.

(** Read the same stored legs in the original category. *)

(** 在原范畴中读取同一份腿。 *)

Definition cowedge_leg {C D : Cat} {F : Functor ((C^op) ×C C) D} {W}
    (κ : Cowedge F W) (X : @Ob C)
  : Hom (F (X, X)) W
  := op_wedge κ X.

Coercion cowedge_leg : Cowedge >-> Funclass.

(** The cowedge equation is the opposite wedge equation read in reverse. *)

(** 余楔方程就是反楔方程的反向读取。 *)

Lemma cowedge_comm {C D : Cat} {F : Functor ((C^op) ×C C) D} {W}
    (κ : Cowedge F W) {X Y : @Ob C} (f : Hom X Y)
  : κ X ∘ fmap F (X := (Y, X)) (Y := (X, X)) (f, id)
    ≈ κ Y ∘ fmap F (X := (Y, X)) (Y := (Y, Y)) (id, f).
Proof.
  symmetry.
  exact (@wedge_comm (C^op) (D^op) (BifunctorOpF F) W
    (op_wedge κ) Y X f).
Qed.

(** Ordinary cowedge legs with their commuting equation enable the same
    opposite wedge, without another notion of dinaturality. *)

(** 通常方向的余楔腿及其交换方程启用同一个反楔，不另立双自然性概念。 *)

Program Definition CowedgeOf {C D : Cat}
    {F : Functor ((C^op) ×C C) D} {W}
    (κ : ∀ X : @Ob C, Hom (F (X, X)) W)
    (Hκ : ∀ (X Y : @Ob C) (f : Hom X Y),
      κ X ∘ fmap F (X := (Y, X)) (Y := (X, X)) (f, id)
      ≈ κ Y ∘ fmap F (X := (Y, X)) (Y := (Y, Y)) (id, f))
  : Cowedge F W
  :=
  {|op_wedge :=
      {|wedge_leg X := κ X
      |}
  |}.
Next Obligation. symmetry. exact (Hκ Y X f). Qed.

(** Compare cowedges using the equality of the stored opposite wedges. *)

(** 用存储的反楔相等比较余楔。 *)

Definition CowedgeEq {C D : Cat} {F : Functor ((C^op) ×C C) D} {W}
    (κ μ : Cowedge F W)
  := op_wedge κ ≈W op_wedge μ.

Infix "≈CW" := CowedgeEq (at level 50, no associativity) : cat_scope.

(** Cowedge equality inherits the pointwise equivalence laws. *)

(** 余楔相等继承逐点等价律。 *)

Global Instance CowedgeEq_Equivalence {C D F W}
  : Equivalence (@CowedgeEq C D F W).
Proof.
  unfold CowedgeEq. split.
  - intros κ. reflexivity.
  - intros κ μ H. symmetry. exact H.
  - intros κ μ ν H K. transitivity (op_wedge μ); assumption.
Defined.

(** Postcomposition is precomposition in the opposite category. *)

(** 后合成就是反范畴中的预合成。 *)

Definition cowedge_comp {C D : Cat}
    {F : Functor ((C^op) ×C C) D} {W V : @Ob D}
    (f : Hom W V) (κ : Cowedge F W)
  : Cowedge F V
  :=
  {|op_wedge := op_wedge κ ∘Wedge f
  |}.

Infix "∘Cowedge" := cowedge_comp
  (at level 40, left associativity) : cat_scope.

(** Postcomposition respects the two inherited equalities. *)

(** 后合成保持两种继承的相等。 *)

Global Instance cowedge_comp_proper {C D : Cat}
    {F : Functor ((C^op) ×C C) D} {W V : @Ob D}
  : Proper (@HomEq[W, V] ==> CowedgeEq ==> CowedgeEq)
      (@cowedge_comp C D F W V).
Proof.
  intros f g H κ μ K.
  exact (@wedge_comp_proper (C^op) (D^op) (BifunctorOpF F) W V
    (op_wedge κ) (op_wedge μ) K f g H).
Qed.

(** The identity law is inherited from wedge precomposition. *)

(** 恒等律继承自楔预合成。 *)

Lemma cowedge_comp_id {C D : Cat} {F : Functor ((C^op) ×C C) D} {W}
    (κ : Cowedge F W)
  : id ∘Cowedge κ ≈CW κ.
Proof. exact (wedge_comp_id (op_wedge κ)). Qed.

(** Associativity is the opposite wedge law with the map order reversed. *)

(** 结合律就是映射次序反转的反楔定律。 *)

Lemma cowedge_comp_assoc {C D : Cat}
    {F : Functor ((C^op) ×C C) D} {W V U}
    (g : Hom V U) (f : Hom W V) (κ : Cowedge F W)
  : g ∘Cowedge (f ∘Cowedge κ) ≈CW (g ∘ f) ∘Cowedge κ.
Proof. exact (wedge_comp_assoc (op_wedge κ) f g). Qed.

(** Precompose the legs by a bifunctor transformation, using the original
    wedge map in the opposite categories. *)

(** 用双函子自然变换预合成腿，底层使用反范畴中原来的楔映射。 *)

Definition cowedge_precompose {C D : Cat}
    {F G : Functor ((C^op) ×C C) D} {W}
    (κ : Cowedge G W) (α : F ⇒ G)
  : Cowedge F W
  :=
  {|op_wedge := wedge_map (bifunctor_op_nt α) (op_wedge κ)
  |}.

(** Precomposition respects both cowedge and transformation equality. *)

(** 预合成保持余楔及自然变换相等。 *)

Global Instance cowedge_precompose_proper {C D : Cat}
    {F G : Functor ((C^op) ×C C) D} {W}
  : Proper (CowedgeEq ==> NatEq ==> CowedgeEq)
      (@cowedge_precompose C D F G W).
Proof.
  intros κ μ H α β K. apply wedge_map_proper.
  - intros [X Y]. exact (K (X, Y)).
  - exact H.
Qed.
