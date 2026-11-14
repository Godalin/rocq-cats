From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.OppositeProduct
  Cat.Natural
  Cat.Arrow.Core
  Cat.Limit.Core
  Cat.Diagram.Discrete
  Cat.Coequalizer
  Cat.Coproduct.Indexed
  Cat.End.Construction.
From Cats Require Export
  Cat.Coend.Core.

(** * Coends from Coproducts and a Coequalizer *)

(** * 由余积和余等化子构造 coend *)

(** The diagonal family is the opposite end's diagonal family, read in [D]. *)

(** 对角族就是将反 end 的对角族读回 [D]。 *)

Definition CoendDiag {C D : Cat} (F : Fct ((C^op) ×C C) D)
    (X : @Ob C)
  : @Ob D
  := EndDiag (BifunctorOpF F) X.

(** Reversed arrows index the original opposite constraints. An original
    arrow [X → Y] contributes [F (Y,X)], without storing an equality proof. *)

(** 反向箭头为原反约束提供指标。原箭头 [X → Y] 贡献 [F (Y,X)]，不存储相等证明。 *)

Definition CoendSources {C D : Cat} (F : Fct ((C^op) ×C C) D)
    (a : ArrowOb (C^op))
  : @Ob D
  := EndTargets (BifunctorOpF F) a.

(** ** Coproduct Constraints

    Fix a bifunctor and chosen coproducts of its diagonal and arrow families.
    Adapt these choices to opposite products and reuse the end construction. *)

(** ** 余积约束

    固定双函子及其对角族和箭头族的选定余积。将这些选择适配为反积，复用 end 构造。 *)

Section CoproductsCoequalizer.
Context {C D : Cat} (F : Fct ((C^op) ×C C) D).
Context `{HO : !HasColimit D (DiscreteF (CoendDiag F))}.
Context `{HA : !HasColimit D (DiscreteF (CoendSources F))}.

(** Retain the selected diagonal coproduct as the opposite product. *)

(** 将选定对角余积保留为反积。 *)

Local Definition coend_diagonal_product
  : HasLimit (D^op) (@DiscreteF (D^op) _ (CoendDiag F))
  := @IndexedCoproductOpProduct D _ (CoendDiag F) HO.

(** Retain the selected arrow coproduct as the opposite product. *)

(** 将选定箭头余积保留为反积。 *)

Local Definition coend_sources_product
  : HasLimit (D^op) (@DiscreteF (D^op) _ (CoendSources F))
  := @IndexedCoproductOpProduct D _ (CoendSources F) HA.

(** For [f : X → Y], apply [F (f,id)] then inject at [X]. This is the
    original opposite contravariant constraint. *)

(** 对 [f : X → Y]，先作用 [F (f,id)] 再注入 [X]，即原反逆变约束。 *)

Definition coend_coproduct_source
  : Hom ∐[CoendSources F] ∐[CoendDiag F]
  := @end_product_contravariant (C^op) (D^op) (BifunctorOpF F)
      coend_diagonal_product coend_sources_product.

(** For [f : X → Y], apply [F (id,f)] then inject at [Y]. This is the
    original opposite covariant constraint. *)

(** 对 [f : X → Y]，先作用 [F (id,f)] 再注入 [Y]，即原反协变约束。 *)

Definition coend_coproduct_target
  : Hom ∐[CoendSources F] ∐[CoendDiag F]
  := @end_product_covariant (C^op) (D^op) (BifunctorOpF F)
      coend_diagonal_product coend_sources_product.

(** A coequalizing arrow gives a cowedge through the same opposite wedge. *)

(** 余等化箭头通过同一个反楔给出余楔。 *)

Definition CoproductsCoequalizerCowedge {E : @Ob D}
    (e : Hom ∐[CoendDiag F] E)
    (H : e ∘ coend_coproduct_target ≈ e ∘ coend_coproduct_source)
  : Cowedge F E
  :=
  {|op_wedge := @ProductsEqualizerWedge (C^op) (D^op) (BifunctorOpF F)
      coend_diagonal_product coend_sources_product E e H
  |}.

(** A candidate coequalizer has the coend property by the opposite end
    theorem; no mediator or uniqueness argument is repeated. *)

(** 候选余等化子由反 end 定理得到 coend 性质，不重复中介或唯一性论证。 *)

Definition coproducts_coequalizer_coend {E : @Ob D}
    (e : Hom ∐[CoendDiag F] E)
    (H : e ∘ coend_coproduct_target ≈ e ∘ coend_coproduct_source)
    (HE : is_coequalizer coend_coproduct_target coend_coproduct_source E e)
  : is_coend (CoproductsCoequalizerCowedge e H)
  := @products_equalizer_end (C^op) (D^op) (BifunctorOpF F)
      coend_diagonal_product coend_sources_product E e H HE.

(** One candidate coequalizer selects the same opposite end. *)

(** 一个候选余等化子选取同一个反 end。 *)

Program Definition CoproductsCoequalizerCoendOf {E : @Ob D}
    (e : Hom ∐[CoendDiag F] E)
    (HE : is_coequalizer coend_coproduct_target coend_coproduct_source E e)
  : HasCoend D F
  :=
  {|hasOpEnd := @ProductsEqualizerEndOf (C^op) (D^op) (BifunctorOpF F)
      coend_diagonal_product coend_sources_product E e HE
  |}.

(** Two coproducts and chosen coequalizers select a coend. Its sole stored
    universal object is the end already constructed in the opposite category. *)

(** 两个余积及选定余等化子选取 coend；唯一存储的泛对象是反范畴中已经构造的 end。 *)

Program Definition CoproductsCoequalizerCoend `{HE : !HasCoequalizer D}
  : HasCoend D F
  := CoproductsCoequalizerCoendOf
      πcoeq[coend_coproduct_target, coend_coproduct_source]
      coequalizer_universal.

End CoproductsCoequalizer.
