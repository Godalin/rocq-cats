From Cats Require Export
  Cat.Cartesian.Core
  Cat.Premonoidal.Symmetric
  Cat.Induced.
From Cats Require Import
  Cat.Terminal
  Cat.Product.Transport.

Local Open Scope binoidal_scope.
Local Open Scope premonoidal_scope.

(** * Freyd Categories

    Values have chosen finite products. Computations form a symmetric
    premonoidal category on those same objects, and pure maps are central
    and strictly preserve the structure. An ambient functor supplies the
    hom-sets; reindexing its codomain by value objects makes the actual
    inclusion identity on objects, without a bijection or object-map
    equality. Unused ambient objects play no role.

    Strict preservation of chosen tensor/unit objects is witnessed by
    native object equality. Every arrow law uses the corresponding
    explicit boundary transports and specified hom equality; no equality
    of functions, functor records or law witnesses is required. *)

(** * Freyd 范畴

    值具有选定有限积。计算在同一批对象上构成对称预幺半范畴，纯映射为中心
    态射并严格保持结构。环境函子提供 Hom 广集；以值对象重索引其余域，使
    实际嵌入在对象上恒等，无需求对象双射或对象映射的相等。未使用的环境
    对象不参与构造。

    选定张量／单位对象的严格保持性由对象原生相等见证。每个态射定律均使用
    对应的显式边界运输及指定 Hom 相等，不要求函数、函子记录或定律见证相等。 *)

Class FreydCat (C K : Cat)
  :=
  (** The pure functor is the unique primary view. *)

  (** 纯函子是唯一主要视图。 *)

  { FreydF :> Fct C K

  (** Compute the actual computation category on value objects. *)

  (** 计算以值对象为对象的实际计算范畴。 *)

  ; FreydComputations : Cat := InducedCat (@Ob C) FreydF

  (** Select cartesian values and symmetric premonoidal computations. *)

  (** 选定笛卡尔值结构及对称预幺半计算结构。 *)

  ; hasCartesian :: CartesianCat C
  ; hasSymmetricPremonoidal :: SymmetricPremonoidalCat FreydComputations

  (** Tensor and unit agree on objects. The chosen equality witnesses
      determine every boundary transport below. *)

  (** 张量及单位在对象上一致。选定相等见证确定以下全部边界运输。 *)

  ; freyd_tensor_objects (X Y : @Ob C)
    : @Prod C hasProduct X Y =
        @binoidal_tensor FreydComputations hasSymmetricPremonoidal X Y
  ; freyd_unit_object
    : @Term C hasTerminal = PremonoidalUnit hasSymmetricPremonoidal

  (** Pure maps commute with arbitrary computations in both positions. *)

  (** 纯映射在两个位置均与任意计算交换。 *)

  ; freyd_pure_central {X Y : @Ob C} (f : Hom X Y)
    : @is_central FreydComputations hasSymmetricPremonoidal
        X Y (fmap FreydF f)

  (** Preserve each context action across the same object boundaries. *)

  (** 跨同一对象边界保持每种上下文作用。 *)

  ; freyd_map_left {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
    : @eq_to_hom FreydComputations _ _ (freyd_tensor_objects Z Y) ∘
        fmap FreydF (@id Z × f) ≈
        @binoidal_left FreydComputations hasSymmetricPremonoidal
          X Y Z (fmap FreydF f) ∘
          @eq_to_hom FreydComputations _ _ (freyd_tensor_objects Z X)
  ; freyd_map_right {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
    : @eq_to_hom FreydComputations _ _ (freyd_tensor_objects Y Z) ∘
        fmap FreydF (f × @id Z) ≈
        @binoidal_right FreydComputations hasSymmetricPremonoidal
          X Y Z (fmap FreydF f) ∘
          @eq_to_hom FreydComputations _ _ (freyd_tensor_objects X Z)

  (** Preserve the unitors, transporting the tensor and the unit together. *)

  (** 保持单位子，同时运输张量及单位对象。 *)

  ; freyd_unit_l (X : @Ob C)
    : fmap FreydF (π2 : Hom (1 × X) X) ≈
        (@premonoidal_left_unitor FreydComputations
          hasSymmetricPremonoidal X).1 ∘
          @eq_to_hom FreydComputations _ _
            (eq_trans (freyd_tensor_objects 1 X)
              (f_equal (λ Q, @binoidal_tensor FreydComputations
                hasSymmetricPremonoidal Q X) freyd_unit_object))
  ; freyd_unit_r (X : @Ob C)
    : fmap FreydF (π1 : Hom (X × 1) X) ≈
        (@premonoidal_right_unitor FreydComputations
          hasSymmetricPremonoidal X).1 ∘
          @eq_to_hom FreydComputations _ _
            (eq_trans (freyd_tensor_objects X 1)
              (f_equal (λ Q, @binoidal_tensor FreydComputations
                hasSymmetricPremonoidal X Q) freyd_unit_object))

  (** Both nested tensor boundaries are transported coherently. *)

  (** 相干地运输两个嵌套张量边界。 *)

  ; freyd_assoc (X Y Z : @Ob C)
    : @eq_to_hom FreydComputations _ _
        (eq_trans (freyd_tensor_objects X (Y × Z)%ob)
          (f_equal (λ Q, @binoidal_tensor FreydComputations
            hasSymmetricPremonoidal X Q) (freyd_tensor_objects Y Z))) ∘
        fmap FreydF (@product_assoc C hasProduct X Y Z).1 ≈
        (@premonoidal_associator FreydComputations
          hasSymmetricPremonoidal X Y Z).1 ∘
          @eq_to_hom FreydComputations _ _
            (eq_trans (freyd_tensor_objects (X × Y)%ob Z)
              (f_equal (λ Q, @binoidal_tensor FreydComputations
                hasSymmetricPremonoidal Q Z) (freyd_tensor_objects X Y)))

  (** Preserve symmetry as well as the premonoidal structure. *)

  (** 除预幺半结构外还保持对称性。 *)

  ; freyd_symmetry (X Y : @Ob C)
    : @eq_to_hom FreydComputations _ _ (freyd_tensor_objects Y X) ∘
        fmap FreydF (⟨π2, π1⟩ : Hom (X × Y) (Y × X)) ≈
        @premonoidal_symmetry FreydComputations hasSymmetricPremonoidal
          X Y ∘
          @eq_to_hom FreydComputations _ _ (freyd_tensor_objects X Y)
  }.

Arguments FreydF {_ _} _.
Arguments FreydComputations {_ _} _.

(** The actual value inclusion has identity object map by construction.
    It reuses the same pure-arrow action and retains its universe levels. *)

(** 实际值嵌入的对象映射按构造为恒等。它复用同一纯态射作用并保留其宇宙层级。 *)

Definition FreydPureF {C K : Cat} (F : FreydCat C K)
  : Fct C (FreydComputations F)
  := InducedF F.
