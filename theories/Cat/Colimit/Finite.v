From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Coproduct.Core
  Cat.Coequalizer
  Cat.Pushout
  Cat.Pullback
  Cat.Limit.Finite.

(** * Two Bases for Finite Colimits *)

(** * 有限余极限的两套基础 *)

(** A coequalizer of the two maps into a coproduct gives a pushout, by the
    original product/equalizer construction in the opposite category. *)

(** 将进入余积的两条映射余等化可得到推出，直接复用反范畴中的原积／等化子构造。 *)

Definition coproduct_coequalizer_pushout {C : Cat}
    `{HC : !HasCoproduct C} {X Y Z E : @Ob C}
    {f : Hom Z X} {g : Hom Z Y} {e : Hom (X ⊔ Y) E}
    (HE : is_coequalizer (ι1 ∘ f) (ι2 ∘ g) E e)
  : is_pushout f g E (e ∘ ι1) (e ∘ ι2)
  := @product_equalizer_pullback (C^op) (@hasOpProduct C HC)
      X Y Z E f g e HE.

(** Select pushouts using the original selected product/equalizer pullbacks.
    The only stored structure is still an opposite pullback structure. *)

(** 用原选定积／等化子拉回选择推出；唯一存储的结构仍是反范畴拉回结构。 *)

Program Definition CoproductCoequalizerPushout {C : Cat}
    `{HC : !HasCoproduct C} `{HE : !HasCoequalizer C}
  : HasPushout C
  :=
  {|hasOpPullback := @ProductEqualizerPullback (C^op)
      (@hasOpProduct C HC) (@hasOpEqualizer C HE)
  |}.

(** Push out the initial arrows to obtain the ordinary coproduct property. *)

(** 将始箭头推出得到通常的余积性质。 *)

Definition pushout_coproduct {C : Cat}
    `{HI : !HasInitial C} `{HP : !HasPushout C} {X Y : @Ob C}
  : is_coproduct X Y (X ⊔[¡,¡] Y) ιpo1[¡,¡] ιpo2[¡,¡]
  := @pullback_product (C^op) (@hasOpTerminal C HI)
      (@hasOpPullback C HP) X Y.

(** Select coproducts by the original pullbacks over the opposite terminal
    object. The given initial-object data are retained. *)

(** 通过在反终对象上取原拉回来选择余积；保留给定始对象数据。 *)

Program Definition PushoutCoproduct {C : Cat}
    `{HI : !HasInitial C} `{HP : !HasPushout C}
  : HasCoproduct C
  :=
  {|hasOpProduct := @PullbackProduct (C^op)
      (@hasOpTerminal C HI) (@hasOpPullback C HP)
  |}.

(** A pushout of a copair and a codiagonal gives a coequalizer. This is the
    original pullback-of-diagonal construction read in the opposite category. *)

(** 将余配对与余对角推出得到余等化子；这就是在反范畴中读取原对角拉回构造。 *)

Definition pushout_coequalizer {C : Cat} `{HC : !HasCoproduct C}
    {X Y E : @Ob C} {f g : Hom X Y} {e : Hom Y E} {d : Hom X E}
    (HP : is_pushout ⦗f,g⦘ ⦗(@id X),(@id X)⦘ E e d)
  : is_coequalizer f g E e
  := @pullback_equalizer (C^op) (@hasOpProduct C HC) Y X E f g e d HP.

(** Select coequalizers from coproducts and pushouts through the original
    product/pullback equalizer structure. *)

(** 通过原积／拉回等化子结构，从余积和推出选择余等化子。 *)

Program Definition CoproductPushoutCoequalizer {C : Cat}
    `{HC : !HasCoproduct C} `{HP : !HasPushout C}
  : HasCoequalizer C
  :=
  {|hasOpEqualizer := @ProductPullbackEqualizer (C^op)
      (@hasOpProduct C HC) (@hasOpPullback C HP)
  |}.

(** Initial objects and pushouts suffice; no independently selected
    coproduct structure is needed. *)

(** 始对象和推出已经足够，不需要独立选定的余积结构。 *)

Program Definition PushoutCoequalizer {C : Cat}
    `{HI : !HasInitial C} `{HP : !HasPushout C}
  : HasCoequalizer C
  :=
  {|hasOpEqualizer := @PullbackEqualizer (C^op)
      (@hasOpTerminal C HI) (@hasOpPullback C HP)
  |}.

(** The original finite-limit basis theorem converts the stored opposite
    structures. Both directions retain the supplied initial structure; no
    equality of records or round-trip choices is asserted. *)

(** 原有限极限基础定理转换存储的反结构；两个方向都保留给定始对象结构，
    不要求记录或往返选择相等。 *)

Theorem finite_colimit_bases (C : Cat)
  : (HasInitial C ∧ HasPushout C)
      ↔ (HasInitial C ∧ HasCoproduct C ∧ HasCoequalizer C).
Proof.
  split.
  - intros [HI HP].
    destruct (fst (finite_limit_bases (C^op))
      (@hasOpTerminal C HI, @hasOpPullback C HP)) as [HT [HC HE]].
    exact (HI, ({|hasOpProduct := HC|}, {|hasOpEqualizer := HE|})).
  - intros [HI [HC HE]].
    destruct (snd (finite_limit_bases (C^op))
      (@hasOpTerminal C HI, (@hasOpProduct C HC, @hasOpEqualizer C HE)))
      as [HT HP].
    exact (HI, {|hasOpPullback := HP|}).
Defined.
