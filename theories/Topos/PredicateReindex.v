From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Logic.Natural
  Cat.Terminal
  Cat.Pullback
  Topos.Sub
  Topos.PredicateOrder
  Topos.PredicateCategory.

(** * Natural Comparisons for Predicate Reindexing

    Fix named terminal, classifier and pullback choices. Reuse the general
    preorder comparison bridge to retain classifier factors in both
    directions. Functor comparisons use natural equality; no native
    equality of predicates, context arrows or functor records is assumed. *)

(** * 谓词重索引的自然比较

    固定具名终对象、分类子与拉回选择。复用一般预序比较桥梁，保留两个方向
    的分类子因子。函子比较使用自然相等，不假设谓词、上下文箭头或函子记录
    的原生相等。 *)

Section PredicateReindexComparisons.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{PB : !HasPullback C}.

(** Equal context arrows give equal substituted classifier arrows. *)

(** 相等上下文箭头给出相等的代入后分类箭头。 *)

Definition predicate_reindex_eq {X Y : C} {k k' : Hom X Y}
    (H : k ≈ k') (f : Hom Y Ω)
  : PredicateReindexF k f ≈ PredicateReindexF k' f.
Proof. unfold PredicateReindexF; cbn. now rewrite H. Defined.

(** Transport along specified context-arrow equality keeps the two
    factors obtained by classifier reflection, even for reflexive [H]. *)

(** 沿指定上下文箭头相等的运输保留分类反射得到的两个因子，即使 [H] 自反。 *)

Definition PredicateReindexEqIso {X Y : C} {k k' : Hom X Y}
    (H : k ≈ k')
  : PredicateReindexF k ≅N PredicateReindexF k'
  := PreorderNatIso (PredicateReindexF k) (PredicateReindexF k')
      (λ f, classified_sub_congr (predicate_reindex_eq H f)).

(** Identity substitution is naturally isomorphic to the identity
    functor, using the existing classifier-arrow unit law. *)

(** 恒等代入借助既有分类箭头单位律自然同构于恒等函子。 *)

Definition PredicateReindexIdIso (X : C)
  : PredicateReindexF (@Cats.Cat.Core.id C X) ≅N IdF
  := PreorderNatIso (PredicateReindexF (@Cats.Cat.Core.id C X)) IdF
      (λ f, classified_sub_congr (predicate_reindex_id f)).

(** Composition is contravariant up to a selected natural isomorphism;
    its components retain the original classifier comparison factors. *)

(** 复合按选定自然同构逆变，其分量保留原有分类子比较因子。 *)

Definition PredicateReindexCompIso {X Y Z : C}
    (k : Hom X Y) (l : Hom Y Z)
  : PredicateReindexF k ∘F PredicateReindexF l
    ≅N PredicateReindexF (l ∘ k)
  := PreorderNatIso (PredicateReindexF k ∘F PredicateReindexF l)
      (PredicateReindexF (l ∘ k))
      (λ f, classified_sub_congr (predicate_reindex_comp k l f)).

(** The equality comparison computes to its selected forward factor. *)

(** 相等比较计算为选定正向因子。 *)

Definition predicate_reindex_eq_data {X Y : C} {k k' : Hom X Y}
    (H : k ≈ k') (f : Hom Y Ω)
  : (PredicateReindexEqIso H).1 f
    = fst (classified_sub_congr (predicate_reindex_eq H f))
  := eq_refl.

(** Its derived inverse computes to the selected reverse factor. *)

(** 其派生逆计算为选定反向因子。 *)

Definition predicate_reindex_eq_inv_data {X Y : C} {k k' : Hom X Y}
    (H : k ≈ k') (f : Hom Y Ω)
  : NatIso_inv (PredicateReindexEqIso H).1
      (PredicateReindexEqIso H).2 f
    = snd (classified_sub_congr (predicate_reindex_eq H f))
  := eq_refl.

(** The identity comparison retains its classifier factor by conversion. *)

(** 恒等比较按转换保留其分类子因子。 *)

Definition predicate_reindex_id_data {X : C} (f : Hom X Ω)
  : (PredicateReindexIdIso X).1 f
    = fst (classified_sub_congr (predicate_reindex_id f))
  := eq_refl.

(** The inverse identity comparison retains the other classifier factor. *)

(** 逆恒等比较保留另一个分类子因子。 *)

Definition predicate_reindex_id_inv_data {X : C} (f : Hom X Ω)
  : NatIso_inv (PredicateReindexIdIso X).1
      (PredicateReindexIdIso X).2 f
    = snd (classified_sub_congr (predicate_reindex_id f))
  := eq_refl.

(** The composition comparison retains its forward classifier factor. *)

(** 复合比较保留其正向分类子因子。 *)

Definition predicate_reindex_comp_data {X Y Z : C}
    (k : Hom X Y) (l : Hom Y Z) (f : Hom Z Ω)
  : (PredicateReindexCompIso k l).1 f
    = fst (classified_sub_congr (predicate_reindex_comp k l f))
  := eq_refl.

(** Its derived inverse retains the reverse classifier factor. *)

(** 其派生逆保留反向分类子因子。 *)

Definition predicate_reindex_comp_inv_data {X Y Z : C}
    (k : Hom X Y) (l : Hom Y Z) (f : Hom Z Ω)
  : NatIso_inv (PredicateReindexCompIso k l).1
      (PredicateReindexCompIso k l).2 f
    = snd (classified_sub_congr (predicate_reindex_comp k l f))
  := eq_refl.

(** ** Unit and Association Diagrams

    Use the existing functor unitors, associator and whiskering. Transport
    the composite context arrows by their specified category laws before
    comparing parallel paths. The target preorder supplies [NatEq]; the
    selected factors and their native computations remain distinct data. *)

(** ** 单位与结合图

    使用既有函子单位比较、结合比较及 whiskering。先沿指定范畴律运输复合
    上下文箭头，再比较平行路径。目标预序提供 [NatEq]，选定因子及其原生
    计算仍是不同数据。 *)

(** The left context unit agrees with the left functor unitor. *)

(** 上下文左侧的恒等与左函子单位比较相容。 *)

Definition predicate_reindex_unit_left {X Y : C} (k : Hom X Y)
  : ((PredicateReindexEqIso (comp_id_r k)).1
      ∘Nv (PredicateReindexCompIso (@Cats.Cat.Core.id C X) k).1)
    ≈N ((CompF_id_l (PredicateReindexF k)).1
      ∘Nv ((PredicateReindexIdIso X).1 ∘Nr PredicateReindexF k))
  := preorder_nat_eq _ _.

(** The right context unit agrees with the right functor unitor. *)

(** 上下文右侧的恒等与右函子单位比较相容。 *)

Definition predicate_reindex_unit_right {X Y : C} (k : Hom X Y)
  : ((PredicateReindexEqIso (comp_id_l k)).1
      ∘Nv (PredicateReindexCompIso k (@Cats.Cat.Core.id C Y)).1)
    ≈N ((CompF_id_r (PredicateReindexF k)).1
      ∘Nv (PredicateReindexF k ∘Nl (PredicateReindexIdIso Y).1))
  := preorder_nat_eq _ _.

(** The two paths for three substitutions agree after the existing
    functor associator and specified base associativity transport. *)

(** 三次代入的两条路径经既有函子结合比较和指定基范畴结合律运输后相等。 *)

Definition predicate_reindex_association {W X Y Z : C}
    (k : Hom W X) (l : Hom X Y) (m : Hom Y Z)
  : ((PredicateReindexCompIso (l ∘ k) m).1
      ∘Nv ((PredicateReindexCompIso k l).1 ∘Nr PredicateReindexF m))
    ≈N ((PredicateReindexEqIso (comp_assoc m l k)).1
      ∘Nv (PredicateReindexCompIso k (m ∘ l)).1
      ∘Nv (PredicateReindexF k ∘Nl (PredicateReindexCompIso l m).1)
      ∘Nv (CompF_assoc (PredicateReindexF k)
        (PredicateReindexF l) (PredicateReindexF m)).1)
  := preorder_nat_eq _ _.

End PredicateReindexComparisons.
