From Cats Require Export
  Cat.Computational.Freyd.Core
  Cat.Binoidal.Transport
  Cat.Functor.Transport.
From Cats Require Import
  Cat.Terminal
  Cat.Product.Transport
  Cat.Monoidal.Cartesian.

Local Open Scope binoidal_scope.
Local Open Scope premonoidal_scope.

(** * Freyd Contexts at Value-Product Boundaries

    Transport the existing computation action to the chosen value products.
    Boundary equations compare these actions with the original tensor,
    keeping every equality witness explicit and computational. *)

(** * 值积边界上的 Freyd 上下文

    将已有计算作用运输到选定值积。边界方程将这些作用与原张量比较，显式
    保留每个可计算相等见证。 *)

Section Contexts.
Context {C K : Cat} (F : FreydCat C K).

Let D
  : Cat
  := FreydComputations F.
Let CC
  : CartesianCat C
  := @hasCartesian C K F.
Local Existing Instance CC.
Let SP
  : SymmetricPremonoidalCat D
  := @hasSymmetricPremonoidal C K F.
Local Existing Instance SP.

(** The tensor boundary uses precisely the Freyd structure's chosen path. *)

(** 张量边界恰好使用 Freyd 结构选定的路径。 *)

Definition FreydTensorIso (X Y : @Ob C)
  : (@Prod C hasProduct X Y) ≅[D] (@binoidal_tensor D SP X Y)
  := @EqualityIso D _ _ (@freyd_tensor_objects C K F X Y).

(** Conjugation makes the original left action a functor on value products. *)

(** 共轭将原左作用变成值积上的函子。 *)

Definition FreydContextF (Z : @Ob C)
  : Fct D D
  := TransportF (@BinoidalLeftF D SP Z)
    (λ X, @Prod C hasProduct Z X) (FreydTensorIso Z).

(** The computation passes through the same forward and inverse boundaries. *)

(** 计算穿过同一组正向及反向边界。 *)

Definition freyd_context {X Y : @Ob C} (Z : @Ob C)
    (f : (@Hom D) X Y)
  : (@Hom D) (@Prod C hasProduct Z X) (@Prod C hasProduct Z Y)
  := fmap (FreydContextF Z) f.

(** The original and transported actions form a natural boundary square. *)

(** 原作用与运输后的作用构成自然边界方块。 *)

Lemma freyd_context_boundary {X Y : @Ob C} (Z : @Ob C)
    (f : (@Hom D) X Y)
  : (FreydTensorIso Z Y).1 ∘ freyd_context Z f ≈
      (@binoidal_left D SP X Y Z f) ∘ (FreydTensorIso Z X).1.
Proof.
  exact (nt_naturality
    (TransportN (@BinoidalLeftF D SP Z)
      (λ X, @Prod C hasProduct Z X) (FreydTensorIso Z)) f).
Qed.

(** Pure maps recover the chosen value-product map under transport. *)

(** 运输后的纯映射恢复选定值积映射。 *)

Lemma freyd_context_pure {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
  : freyd_context Z (fmap (FreydPureF F) f) ≈ fmap (FreydPureF F) (@id Z × f).
Proof.
  apply (iso_cancel_l (FreydTensorIso Z Y)).
  rewrite freyd_context_boundary. symmetry.
  exact (@freyd_map_left C K F X Y Z f).
Qed.

(** Express pure right-context preservation using the selected boundary
    isomorphisms, so clients need not unfold their object transports. *)

(** 用选定边界同构表达纯右上下文保持性，使客户端无需展开对象运输。 *)

Lemma freyd_pure_right_boundary {X Y : @Ob C} (Z : @Ob C)
    (f : Hom X Y)
  : (FreydTensorIso Y Z).1 ∘ fmap (FreydPureF F) (f × @id Z) ≈
      (@binoidal_right D SP X Y Z (fmap (FreydPureF F) f)) ∘ (FreydTensorIso X Z).1.
Proof. exact (@freyd_map_right C K F X Y Z f). Qed.

(** Ordinary changes of context commute with an arbitrary computation. *)

(** 通常上下文变化与任意计算交换。 *)

Lemma freyd_context_natural {X Y Z W : @Ob C}
    (f : (@Hom D) X Y) (h : Hom Z W)
  : fmap (FreydPureF F) (h × @id Y) ∘ freyd_context Z f ≈
      freyd_context W f ∘ fmap (FreydPureF F) (h × @id X).
Proof.
  assert (Hc :
    (@binoidal_right D SP Z W Y (fmap (FreydPureF F) h)) ∘
      (@binoidal_left D SP X Y Z f) ≈
    (@binoidal_left D SP X Y W f) ∘
      (@binoidal_right D SP Z W X (fmap (FreydPureF F) h))).
  { exact (fst (@freyd_pure_central C K F Z W h X Y f)). }
  apply (iso_cancel_l (FreydTensorIso W Y)).
  fold D.
  rewrite <- !(@comp_assoc D), (freyd_pure_right_boundary Y h).
  rewrite !(@comp_assoc D), (freyd_context_boundary Z f).
  rewrite <- (@comp_assoc D), Hc.
  rewrite !(@comp_assoc D).
  rewrite <- (freyd_pure_right_boundary X h).
  rewrite <- !(@comp_assoc D), (freyd_context_boundary W f). reflexivity.
Qed.

(** Move the fixed context along one chosen object equality. *)

(** 沿一个选定对象相等移动固定上下文。 *)

Definition FreydContextBoundary {Z W : @Ob C} (p : Z = W) (X : @Ob C)
  : (@Prod C hasProduct Z X) ≅[D] (@binoidal_tensor D SP W X)
  := @EqualityIso D _ _
    (eq_trans (@freyd_tensor_objects C K F Z X)
      (f_equal (λ Q, @binoidal_tensor D SP Q X) p)).

(** Decompose the boundary using the same context path and tensor path. *)

(** 使用同一上下文路径及张量路径分解边界。 *)

Lemma freyd_context_boundary_decompose {Z W : @Ob C}
    (p : Z = W) (X : @Ob C)
  : (FreydContextBoundary p X).1 ≈
      @eq_to_hom D _ _
        (f_equal (λ Q, @binoidal_tensor D SP Q X) p) ∘
        (FreydTensorIso Z X).1.
Proof.
  exact (@eq_to_hom_comp D _ _ _ (@freyd_tensor_objects C K F Z X)
    (f_equal (λ Q, @binoidal_tensor D SP Q X) p)).
Qed.

(** The changed fixed context still has its natural boundary square. *)

(** 改变后的固定上下文仍具有自然边界方块。 *)

Lemma freyd_context_changed_boundary {Z W X Y : @Ob C}
    (p : Z = W) (f : (@Hom D) X Y)
  : (FreydContextBoundary p Y).1 ∘ freyd_context Z f ≈
      (@binoidal_left D SP X Y W f) ∘ (FreydContextBoundary p X).1.
Proof.
  rewrite !freyd_context_boundary_decompose, (@comp_assoc D),
    freyd_context_boundary, <- (@comp_assoc D), (@binoidal_context_eq D SP),
    (@comp_assoc D). reflexivity.
Qed.

(** Fixed-context boundary squares form one natural transformation. *)

(** 固定上下文的边界方块组成一个自然变换。 *)

Program Definition FreydContextBoundaryN {Z W : @Ob C} (p : Z = W)
  : FreydContextF Z ⇒ @BinoidalLeftF D SP W
  :=
  {|nt X := (FreydContextBoundary p X).1
  |}.
Next Obligation. exact (freyd_context_changed_boundary p f). Defined.

(** Two value contexts have a boundary into the nested computation tensor. *)

(** 两个值上下文具有到嵌套计算张量的边界。 *)

Definition FreydNestedBoundary (Z W X : @Ob C)
  : (@Prod C hasProduct Z (@Prod C hasProduct W X)) ≅[D]
      (@binoidal_tensor D SP Z (@binoidal_tensor D SP W X))
  := @EqualityIso D _ _
    (eq_trans (@freyd_tensor_objects C K F Z (@Prod C hasProduct W X))
      (f_equal (λ Q, @binoidal_tensor D SP Z Q)
        (@freyd_tensor_objects C K F W X))).

(** Nested boundaries compose the inner and outer selected boundaries. *)

(** 嵌套边界由内外两个选定边界复合而成。 *)

Lemma freyd_nested_boundary_decompose (Z W X : @Ob C)
  : (FreydNestedBoundary Z W X).1 ≈
      (@binoidal_left D SP _ _ Z (FreydTensorIso W X).1) ∘
        (FreydTensorIso Z (@Prod C hasProduct W X)).1.
Proof.
  change (@eq_to_hom D _ _
    (eq_trans (@freyd_tensor_objects C K F Z (@Prod C hasProduct W X))
      (f_equal (λ Q, @binoidal_tensor D SP Z Q)
        (@freyd_tensor_objects C K F W X))) ≈
    (@binoidal_left D SP _ _ Z
      (@eq_to_hom D _ _ (@freyd_tensor_objects C K F W X))) ∘
      @eq_to_hom D _ _
        (@freyd_tensor_objects C K F Z (@Prod C hasProduct W X))).
  etransitivity.
  - exact (@eq_to_hom_comp D _ _ _
      (@freyd_tensor_objects C K F Z (@Prod C hasProduct W X))
      (f_equal (λ Q, @binoidal_tensor D SP Z Q)
        (@freyd_tensor_objects C K F W X))).
  - apply (@comp_proper D); [| reflexivity]. symmetry.
    exact (@binoidal_left_eq_to_hom D SP Z _ _
      (@freyd_tensor_objects C K F W X)).
Qed.

(** Nested transported contexts recover the original two left actions. *)

(** 嵌套运输上下文恢复原有两个左作用。 *)

Lemma freyd_nested_context_boundary {X Y : @Ob C}
    (Z W : @Ob C) (f : (@Hom D) X Y)
  : (FreydNestedBoundary Z W Y).1 ∘
      freyd_context Z (freyd_context W f) ≈
      (@binoidal_left D SP _ _ Z (@binoidal_left D SP X Y W f)) ∘
        (FreydNestedBoundary Z W X).1.
Proof.
  rewrite !freyd_nested_boundary_decompose, (@comp_assoc D),
    freyd_context_boundary, <- (@comp_assoc D), <- (@binoidal_left_comp D SP),
    freyd_context_boundary, (@binoidal_left_comp D SP), (@comp_assoc D). reflexivity.
Qed.

(** Nested context boundaries form a natural isomorphism. *)

(** 嵌套上下文边界组成一个自然同构。 *)

Program Definition FreydNestedBoundaryN (Z W : @Ob C)
  : (FreydContextF Z ∘F FreydContextF W) ⇒
      (@BinoidalLeftF D SP Z ∘F @BinoidalLeftF D SP W)
  :=
  {|nt X := (FreydNestedBoundary Z W X).1
  |}.
Next Obligation. exact (freyd_nested_context_boundary Z W f). Defined.

(** The inverse components are the same selected nested inverse boundaries. *)

(** 逆分量就是同一组选定的嵌套反向边界。 *)

Definition FreydNestedBoundaryIso (Z W : @Ob C)
  : (FreydContextF Z ∘F FreydContextF W) ≅N
      (@BinoidalLeftF D SP Z ∘F @BinoidalLeftF D SP W)
  := (FreydNestedBoundaryN Z W; λ X, (FreydNestedBoundary Z W X).2).

(** The transported action obeys the value left-unit equation. *)

(** 运输后的作用满足值左单位方程。 *)

Lemma freyd_context_unit {X Y : @Ob C} (f : (@Hom D) X Y)
  : fmap (FreydPureF F) (π2 : Hom (1 × Y) Y) ∘ freyd_context 1 f ≈
      f ∘ fmap (FreydPureF F) (π2 : Hom (1 × X) X).
Proof.
  apply (nt_naturality_boundary
    (FreydContextBoundaryN (@freyd_unit_object C K F))
    (@idN D D (@IdF D); nt_id_NatIso (@IdF D))
    (@PremonoidalLeftUnitorN D SP)
    (λ T : @Ob C, fmap (FreydPureF F) (π2 : Hom (1 × T) T))).
  intro T. etransitivity.
  - exact (@comp_id_l D _ _ (fmap (FreydPureF F)
      (π2 : (@Hom C) (@Prod C hasProduct (@Term C hasTerminal) T) T))).
  - exact (@freyd_unit_l C K F T).
Qed.

(** Value reassociation preserves two transported contexts coherently. *)

(** 值括号重排相干地保持两个运输上下文。 *)

Lemma freyd_context_assoc {X Y : @Ob C} (Z W : @Ob C)
    (f : (@Hom D) X Y)
  : fmap (FreydPureF F) (@product_assoc C hasProduct Z W Y).1 ∘
      freyd_context (Z × W)%ob f ≈
      freyd_context Z (freyd_context W f) ∘
        fmap (FreydPureF F) (@product_assoc C hasProduct Z W X).1.
Proof.
  apply (nt_naturality_boundary
    (FreydContextBoundaryN (@freyd_tensor_objects C K F Z W))
    (FreydNestedBoundaryIso Z W)
    (@PremonoidalContextAssociatorN D SP Z W)
    (λ T : @Ob C, fmap (FreydPureF F)
      (@product_assoc C hasProduct Z W T).1)).
  intro T. exact (@freyd_assoc C K F Z W T).
Qed.

End Contexts.
