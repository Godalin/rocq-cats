From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Equalizer
  Cat.Pullback.
From Cats Require Export Cat.Shape.Finite.
From Cats Require Import
  Cat.Limit.Graph.Finite
  Cat.Limit.Reindex.

(** * Two Bases for Finite Limits

    Each candidate construction uses only the structures it needs. Chosen
    structures are explicit conversions, not global instances. *)

(** * 有限极限的两套基础

    各候选构造仅使用所需结构；选定结构通过显式转换给出，不注册全局实例。 *)

(** An equalizer inside a product gives a pullback. *)

(** 积内部的等化子给出拉回。 *)

Definition product_equalizer_pullback {C : Cat} `{HP : !HasProduct C}
    {X Y Z E : @Ob C} {f : Hom X Z} {g : Hom Y Z} {e : Hom E (X × Y)}
    (HE : is_equalizer (f ∘ π1) (g ∘ π2) E e)
  : is_pullback f g E (π1 ∘ e) (π2 ∘ e).
Proof.
  split.
  - rewrite <- !comp_assoc. exact (fst HE).
  - intros Q p q Hpq.
    assert (H : (f ∘ π1) ∘ ⟨p, q⟩ ≈ (g ∘ π2) ∘ ⟨p, q⟩).
    { rewrite !comp_assoc, product_β1, product_β2. exact Hpq. }
    destruct (snd HE Q ⟨p, q⟩ H) as [h Hh].
    exists h. refine {|this := _
                     ; that := _
                     |}.
    + split; rewrite comp_assoc, (@this _ _ _ _ _ Hh);
        [apply product_β1 | apply product_β2].
    + intros k [Hk1 Hk2]. apply (@that _ _ _ _ _ Hh).
      rewrite (product_η (e ∘ k)), <- !comp_assoc, Hk1, Hk2. reflexivity.
Defined.

(** Choose pullbacks using selected products and equalizers. *)

(** 利用选定积与等化子选择拉回。 *)

Program Definition ProductEqualizerPullback {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasEqualizer C}
  : HasPullback C
  :=
  {|Pb X Y Z f g := Eq[f ∘ π1, g ∘ π2]
  ; pb1 X Y Z f g := π1 ∘ ιeq[f ∘ π1, g ∘ π2]
  ; pb2 X Y Z f g := π2 ∘ ιeq[f ∘ π1, g ∘ π2]
  |}.
Next Obligation. apply product_equalizer_pullback. exact equalizer_universal. Defined.

(** Products from pullbacks over the chosen terminal object. *)

(** 在选定终对象上拉回得到积。 *)

Program Definition PullbackProduct {C : Cat}
    `{HT : !HasTerminal C} `{HPb : !HasPullback C}
  : HasProduct C
  :=
  {|Prod X Y := X ×[!, !] Y
  ; π1 X Y := pb1 ! !
  ; π2 X Y := pb2 ! !
  |}.
Next Obligation. apply pullback_product. Defined.

(** Pull back the diagonal of Y along the pair of parallel arrows. *)

(** 将 [Y] 的对角箭头沿给定平行箭头的配对拉回。 *)

Definition pullback_equalizer {C : Cat} `{HP : !HasProduct C}
    {X Y E : @Ob C} {f g : Hom X Y} {e : Hom E X} {d : Hom E Y}
    (HPb : is_pullback ⟨f, g⟩ ⟨id, id⟩ E e d)
  : is_equalizer f g E e.
Proof.
  assert (Hf : f ∘ e ≈ d).
  { transitivity (π1 ∘ (⟨f, g⟩ ∘ e)).
    - rewrite <- comp_assoc, product_β1. reflexivity.
    - rewrite (fst HPb), <- comp_assoc, product_β1, comp_id_l. reflexivity. }
  assert (Hg : g ∘ e ≈ d).
  { transitivity (π2 ∘ (⟨f, g⟩ ∘ e)).
    - rewrite <- comp_assoc, product_β2. reflexivity.
    - rewrite (fst HPb), <- comp_assoc, product_β2, comp_id_l. reflexivity. }
  split.
  - rewrite Hf, Hg. reflexivity.
  - intros Q q Hq.
    assert (H : ⟨f, g⟩ ∘ q ≈ ⟨id, id⟩ ∘ (f ∘ q)).
    { rewrite !product_comp_r, !comp_id_l, Hq. reflexivity. }
    destruct (snd HPb Q q (f ∘ q) H) as [h Hh].
    exists h. refine {|this := _
                     ; that := _
                     |}.
    + exact (fst (@this _ _ _ _ _ Hh)).
    + intros k Hk. apply (@that _ _ _ _ _ Hh). split; [exact Hk |].
      rewrite <- Hf, comp_assoc, Hk. reflexivity.
Defined.

(** Choose equalizers by pulling back the diagonal into a product. *)

(** 通过将对角箭头拉回到积中选择等化子。 *)

Program Definition ProductPullbackEqualizer {C : Cat}
    `{HP : !HasProduct C} `{HPb : !HasPullback C}
  : HasEqualizer C
  :=
  {|EqObj X Y f g := Pb ⟨f, g⟩ ⟨id, id⟩
  ; eqι X Y f g := pb1 ⟨f, g⟩ ⟨id, id⟩
  |}.
Next Obligation. apply (pullback_equalizer (d := pb2 _ _)). exact pullback_universal. Defined.

(** No independent product structure is required when terminal objects and
    pullbacks are already selected. *)

(** 已选择终对象和拉回时，不再需要独立的积结构。 *)

Definition PullbackEqualizer {C : Cat}
    `{HT : !HasTerminal C} `{HPb : !HasPullback C}
  : HasEqualizer C
  := @ProductPullbackEqualizer C (@PullbackProduct C HT HPb) HPb.

(** These Type-valued implications convert chosen data. They assert no
    equality of records or of the choices made by a round trip. *)

(** 这些 Type 值蕴含转换选定数据；不声称记录或往返过程中作出的选择原生相等。 *)

Theorem finite_limit_bases (C : Cat)
  : (HasTerminal C ∧ HasPullback C)
    ↔ (HasTerminal C ∧ HasProduct C ∧ HasEqualizer C).
Proof.
  split.
  - intros [HT HPb].
    exact (HT, (@PullbackProduct C HT HPb, @PullbackEqualizer C HT HPb)).
  - intros [HT [HP HE]]. exact (HT, @ProductEqualizerPullback C HP HE).
Defined.

(** ** Limits of Finitely Generated and Finite Shapes

    Restrict to a finite generating graph, form its limit by products and an
    equalizer, then extend its cone. The existing shape-transfer theorem
    supplies the universal property without a new uniqueness proof. *)

(** ** 有限生成形状与有限形状的极限

    先限制到有限生成图，用积与等化子构造极限，再延拓锥。已有形状传递定理给出
    泛性质，无需重新证明唯一性。 *)

Section FiniteShapeLimits.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}.
Context `{HE : !HasEqualizer C}.

(** Choose all limits of a shape equipped with finite generators. The shape
    may have infinitely many arrows or additional path equations. *)

(** 为带有限生成元的形状选择全部极限；形状可以有无限多条箭头或额外路径方程。 *)

Definition GeneratedLimits {J : Cat} `{HG : !HasFiniteGenerators J}
  : HasLimitsOfShape C J
  := @ReindexedLimits _ J C generator_functor generator_full
    generator_essentially_surjective (FiniteGraphLimits generator_edges).

(** Finite object representatives and finite hom covers suffice for every
    diagram of that shape to have a selected limit. Enable it explicitly. *)

(** 有限对象代表与有限 Hom 覆盖足以为该形状的每个图式选择极限；须显式启用。 *)

Definition FiniteLimits {J : Cat} `{HJ : !HasFiniteHomCover J}
  : HasLimitsOfShape C J
  := @GeneratedLimits J FiniteHomGenerators.

(** Select the limit of one finite-shape diagram. All its mediator laws and
    the associated limit functor come from the general limit interface. *)

(** 选择单个有限形状图式的极限；中介定律及相应极限函子均来自一般极限接口。 *)

Definition FiniteLimit {J : Cat} `{HJ : !HasFiniteHomCover J}
    (D : Functor J C)
  : HasLimit C D
  := @hasLimit C J FiniteLimits D.

End FiniteShapeLimits.

(** Terminal objects and pullbacks give the same finite-shape existence
    theorem through the already established conversion of bases. *)

(** 终对象与拉回通过已有基础结构转换给出同样的有限形状极限存在定理。 *)

Definition PullbackFiniteLimits {C J : Cat}
    `{HT : !HasTerminal C} `{HPb : !HasPullback C}
    `{HJ : !HasFiniteHomCover J}
  : HasLimitsOfShape C J
  := @FiniteLimits C HT (@PullbackProduct C HT HPb)
    (@PullbackEqualizer C HT HPb) J HJ.
