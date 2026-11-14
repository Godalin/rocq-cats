From Cats Require Export
  Cat.Diagram.Arrow.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Functor.Uncurry
  Cat.Natural.

(** * Prisms from Natural Transformations

    A natural transformation is an arrow in a functor category. Uncurrying
    its walking-arrow diagram produces the prism, with no invertibility
    assumption on its components. The ordinal [1] supplies the time axis. *)

(** * 自然变换给出的棱柱

    自然变换是函子范畴中的箭头。对其步行箭头图式去柯里化，便得到棱柱，
    无须假设分量可逆。序数 [1] 提供时间轴。 *)

(** Read the two concrete ordinal positions as the walking-arrow vertices. *)

(** 将两个具体序数位置读作步行箭头的顶点。 *)

Definition ordinal_interval_side (i : Ordinal 1)
  : bool
  := match i with inl _ => false | inr _ => true end.

(** The ordinal interval maps to the existing walking arrow. Only these
    concrete finite positions and their computational order are inspected. *)

(** 序数区间映到已有步行箭头；仅分析这些具体有限位置及其可计算顺序。 *)

Program Definition OrdinalArrowF
  : Fct [Ord 1] ArrowShape
  :=
  {|F0 := ordinal_interval_side
  ; F1 i j a := _
  |}.
Next Obligation.
  destruct i as [[] | [[] | []]], j as [[] | [[] | []]];
    cbn in *; try exact tt; destruct a.
Defined.
Next Obligation. intros f g H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** Uncurry the arrow between functors, putting the original source first
    and the ordinal time coordinate second. All functor laws are reused. *)

(** 对函子之间的箭头去柯里化，将原源范畴置于第一坐标，序数时间置于第二坐标；
    全部函子律均复用既有构造。 *)

Definition NaturalPrismF {C D : Cat} {F G : Fct C D} (α : F ⇒ G)
  : Fct (C ×C [Ord 1]) D
  := (@ArrowDiagram (FctCat C D) F G α)^uncF ∘F
      PairF (OrdinalArrowF ∘F SndF C [Ord 1]) (FstF C [Ord 1]).

(** Restrict the prism along a diagram and a monotone time diagram.
    This also applies to shapes other than finite ordinals. *)

(** 沿图式及保序时间图式限制棱柱；此构造也适用于有限序数以外的形状。 *)

Definition PrismDiagramF {C D J : Cat} {F G : Fct C D}
    (α : F ⇒ G) (P : Fct J C) (θ : Fct J [Ord 1])
  : Fct J D
  := NaturalPrismF α ∘F PairF P θ.

(** The time edge at a fixed source object computes to the component. *)

(** 固定源对象处的时间边计算为相应分量。 *)

Lemma natural_prism_step {C D : Cat} {F G : Fct C D}
    (α : F ⇒ G) (x : @Ob C)
  : fmap (NaturalPrismF α)
      (X := (x, fin_first)) (Y := (x, fin_next fin_first))
      (id, ordinal_step fin_first) ≈ α x.
Proof. cbn. rewrite functor_id. apply comp_id_l. Defined.

(** Componentwise equal transformations give equal prism arrows. Their
    object maps are definitionally the same, so only hom equality is used. *)

(** 分量逐点相等的自然变换给出相等的棱柱箭头；其对象映射定义相同，
    因此只使用 Hom 相等。 *)

Lemma natural_prism_map_proper {C D : Cat} {F G : Fct C D}
    (α β : F ⇒ G) (H : α ≈N β) {x y : @Ob C}
    {i j : Ordinal 1} (f : Hom x y) (a : (@Hom [Ord 1]) i j)
  : fmap (NaturalPrismF α) (X := (x, i)) (Y := (y, j)) (f, a) ≈
      fmap (NaturalPrismF β) (X := (x, i)) (Y := (y, j)) (f, a).
Proof.
  destruct i as [[] | [[] | []]], j as [[] | [[] | []]];
    cbn in *; try solve [destruct a]; try reflexivity.
  rewrite (H x). reflexivity.
Defined.
