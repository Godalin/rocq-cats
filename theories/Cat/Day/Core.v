From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Coend.Core
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Product.

(** * Covariant Day Convolution *)

(** * 协变 Day 卷积 *)

(** At this stage only a binary functor [T] is required. A monoidal
    category supplies its tensor bifunctor later; its unit, associator and
    strength are not needed to form the pointwise convolution. Hom values
    are raised explicitly to the common target setoid universes. *)

(** 此阶段只需二元函子 [T]。幺半范畴稍后提供其张量双函子；构造逐点卷积
    不需要单位、结合子或强度。Hom 值显式提升到共同的目标广集宇宙。 *)

Definition DayHomF@{u p +} {C : Cat} (T : Functor (C ×C C) C)
    (Z : @Ob C)
  : Functor ((C ×C C)^op) (SetCat@{u p _ _ _ _ _})
  := (LiftF ∘F Hom(-, Z)) ∘F (T^opF).

(** External products evaluate the two input functors independently. *)

(** 外积独立求值两个输入函子。 *)

Definition DayValuesF@{u p +} {C : Cat}
    (F G : Functor C (SetCat@{u p _ _ _ _ _}))
  : Functor (C ×C C) SetCat
  := @PointwiseProductF _ SetCat SetCat_HasProduct
      (F ∘F FstF C C) (G ∘F SndF C C).

(** The contravariant coordinate contributes [Hom (T (X,Y)) Z]; the
    covariant coordinate contributes [F X] and [G Y]. Functoriality is
    inherited from Hom, composition and pointwise products. *)

(** 逆变坐标贡献 [Hom (T (X,Y)) Z]，协变坐标贡献 [F X] 和 [G Y]。
    函子性由 Hom、复合及逐点积继承。 *)

Definition DayKernel@{u p +} {C : Cat} (T : Functor (C ×C C) C)
    (F G : Functor C (SetCat@{u p _ _ _ _ _})) (Z : @Ob C)
  : Functor (((C ×C C)^op) ×C (C ×C C)) SetCat
  := @PointwiseProductF _ SetCat SetCat_HasProduct
      (DayHomF T Z ∘F FstF ((C ×C C)^op) (C ×C C))
      (DayValuesF F G ∘F SndF ((C ×C C)^op) (C ×C C)).

(** ** Target and Input Parameters

    Fix the binary functor and two setoid-valued functors. Target arrows
    postcompose the Hom coordinate; input transformations act only on
    their own value coordinates. *)

(** ** 目标及输入参数

    固定二元函子及两个广集值函子。目标箭头在 Hom 坐标后合成；输入自然变换
    只作用于各自的值坐标。 *)

Section KernelMaps.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).
Context {F G : Functor C (SetCat@{u p _ _ _ _ _})}.

(** Postcomposition in the Hom weight changes the output parameter. *)

(** Hom 权重中的后合成改变输出参数。 *)

Definition DayPostN {Z Z' : @Ob C} (f : Hom Z Z')
  : DayKernel T F G Z ⇒ DayKernel T F G Z'
  := @PointwiseProductN _ SetCat SetCat_HasProduct _ _ _ _
      (((LiftF ∘Nl (f _*N)) ∘Nr (T^opF))
        ∘Nr FstF ((C ×C C)^op) (C ×C C)) idN.

(** Equal target arrows induce equal kernel transformations. *)

(** 相等目标箭头诱导相等的核自然变换。 *)

Global Instance day_post_proper {Z Z' : @Ob C}
  : Proper (@HomEq C Z Z' ==> NatEq) (@DayPostN Z Z').
Proof.
  intros f g H [[X Y] [X' Y']] [h [x y]].
  split; [exact {|lower := comp_proper _ _ H _ _ (reflexivity _)|} |
    split; reflexivity].
Defined.

(** Identity postcomposition leaves the kernel unchanged. *)

(** 恒等后合成保持核不变。 *)

Lemma day_post_id (Z : @Ob C)
  : DayPostN (@id Z) ≈N idN.
Proof.
  intros [[X Y] [X' Y']] [h [x y]].
  split; [exact {|lower := comp_id_l (lower h)|} | split; reflexivity].
Defined.

(** Successive target changes compose by ordinary vertical composition. *)

(** 连续目标变换按通常的垂直复合合成。 *)

Lemma day_post_comp {Z Z' Z'' : @Ob C}
    (g : Hom Z' Z'') (f : Hom Z Z')
  : DayPostN (g ∘ f) ≈N (DayPostN g ∘Nv DayPostN f).
Proof.
  intros [[X Y] [X' Y']] [h [x y]].
  split; [exact {|lower := comp_assoc g f (lower h)|} |
    split; reflexivity].
Defined.

End KernelMaps.

(** Only the coends of this particular kernel family are selected. There
    is no global completeness assumption or fixed-size self-indexing claim. *)

(** 只为这一特定核族选择 coend，没有全局余完备假设或固定大小自索引的断言。 *)

Class HasDay@{u p +} (C : Cat) (T : Functor (C ×C C) C)
    (F G : Functor C (SetCat@{u p _ _ _ _ _}))
  :=
  { hasDayCoend (Z : @Ob C) :: HasCoend (SetCat@{u p _ _ _ _ _})
      (DayKernel T F G Z)
  }.

(** ** Convolution with Chosen Pointwise Coends

    Assume the indicated coends for [F] and [G]. Their existing natural
    transformation action assembles the covariant output functor. *)

(** ** 具有选定逐点 coend 的卷积

    假定 [F] 和 [G] 所需的 coend，利用已有的自然变换作用组装协变输出函子。 *)

Section ChosenDay.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).
Context (F G : Functor C (SetCat@{u p _ _ _ _ _})) `{HD : !HasDay C T F G}.

(** Day convolution is the coend of its Hom-weighted kernel. *)

(** Day 卷积是其 Hom 加权核的 coend。 *)

Program Definition DayF
  : Functor C (SetCat@{u p _ _ _ _ _})
  :=
  {|F0 Z := coend[DayKernel T F G Z]
  ; F1 Z Z' f := coend_map (DayPostN T f)
  |}.
Next Obligation.
  intros f g H.
  exact (@coend_map_proper (C ×C C) SetCat _ _ _ _
    (DayPostN T f) (DayPostN T g) (@day_post_proper C T F G X Y f g H)).
Defined.
Next Obligation.
  transitivity (coend_map (idN (F := DayKernel T F G X))).
  - apply (@coend_map_proper (C ×C C) SetCat). apply day_post_id.
  - apply (@coend_map_id (C ×C C) SetCat).
Defined.
Next Obligation.
  transitivity (coend_map (DayPostN T f ∘Nv DayPostN T g)).
  - apply (@coend_map_proper (C ×C C) SetCat). apply day_post_comp.
  - apply (@coend_map_comp (C ×C C) SetCat).
Defined.

End ChosenDay.
