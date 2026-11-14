From Cats Require Import
  Instance.Set.Simplicial.Vertex.Cartesian
  Instance.Set.Simplicial.Vertex.Monoid
  Instance.Bool.Group
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Functor.Cartesian
  Cat.Functor.FiniteProducts
  Instance.Set.Product.

Local Open Scope nat_scope.

(** * Computing through Chosen Finite Products and Their Preservation *)

(** * 穿过选定有限积及其保持性进行计算 *)

Definition SmallPresentations
  : Cat
  := VertexPresentationCat@{Set Set Set Set Set Set Set Set
      _ _ _ _ _ _ _ _ _ _}.

Definition SmallProducts
  : HasProduct SmallPresentations
  := VertexPresentationCat_HasProduct.

Definition SmallTerminal
  : HasTerminal SmallPresentations
  := VertexPresentationCat_HasTerminal.

Definition SmallPointwiseProducts
  : HasProduct (FctCat (Δ^op) SetCat@{Set Set _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

(** The bundle's coercion exposes the original computational nerve. *)

(** 打包的强制转换暴露原有可计算 nerve。 *)

Definition SmallNerve
  : @CartFct SmallPresentations
      (FctCat (Δ^op) SetCat@{Set Set _ _ _ _ _}) SmallTerminal SmallProducts
  := VertexNerveCartesianF.

(** The original full-faithfulness interface remains usable by coercion. *)

(** 原有全忠实性接口仍可通过强制转换使用。 *)

Example cartesian_full_faithfulness
  : is_fully_faithful SmallNerve.
Proof. exact vertex_nerve_fully_faithful. Qed.

Definition BooleanPresentation
  : VertexPresentation@{Set Set Set Set Set Set Set Set}
  := VertexPresentationOf (MonoidObjF BoolS (HM := BoolS_Monoid)).

(** The actual source product mediator retains both nonidentity arrows. *)

(** 实际源积中介保留两个非恒等箭头。 *)

Example chosen_pair_computes
  : let P := BooleanPresentation in
    fmap (@pair SmallPresentations SmallProducts P P P
      (@Cats.Cat.Core.id SmallPresentations P)
      (@Cats.Cat.Core.id SmallPresentations P))
      (true : (@Hom (VertexCat P)) tt tt) = (true, true).
Proof. reflexivity. Qed.

(** Applying the bundled nerve to the mediator preserves its two edges. *)

(** 将打包 nerve 作用于中介，保持其中的两条边。 *)

Example nerve_pair_computes
  : let P := BooleanPresentation in
    let edge := △₁[P; tt; tt] true in
    fmap (lower (fmap SmallNerve
      (@pair SmallPresentations SmallProducts P P P
        (@Cats.Cat.Core.id SmallPresentations P)
        (@Cats.Cat.Core.id SmallPresentations P)) 1 edge))
      (ordinal_step fin_first) = (true, true).
Proof. reflexivity. Qed.

(** The generic inverse comparison uses the stored preservation witness;
    it computes even when the two boolean arrows are different. *)

(** 通用逆比较使用实际存储的保持性见证；即使两条布尔箭头不同也能计算。 *)

Example stored_product_inverse_computes
  : let P := BooleanPresentation in
    let inverse := @functor_product_inv _ _ SmallNerve
      SmallTerminal SmallProducts SmallPointwiseProducts
      (cartesian_isCartF SmallNerve) P P in
    fmap (lower (inverse 1 (△₁[P; tt; tt] true, △₁[P; tt; tt] false)))
      (ordinal_step fin_first) = (true, false).
Proof. reflexivity. Qed.

(** The stored terminal universal arrow contains an actual constant diagram. *)

(** 存储的终泛箭头包含实际的常值图式。 *)

Example stored_terminal_arrow_computes
  : let P := BooleanPresentation in
    let terminal := @functor_terminal _ _ SmallNerve
      SmallTerminal SmallProducts (cartesian_isCartF SmallNerve) in
    lower ((terminal (SmallNerve P)).1 1 (△₁[P; tt; tt] true)) fin_first = tt.
Proof. reflexivity. Qed.
