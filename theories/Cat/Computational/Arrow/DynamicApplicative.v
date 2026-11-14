From Cats Require Export
  Cat.Computational.Arrow.DynamicRecovery
  Cat.Applicative.Morphism.
From Cats Require Import
  Cat.Computational.Arrow.Applicative
  Instance.Set.Arrow
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Applicative Compatibility of Dynamic Reconstruction

    Fix a native-setoid ArrowApply with independent computation-object,
    Hom carrier and equality levels. Naming preserves the derived ordered
    operations by its already proved pure, composition and context laws.
    Its terminal-input specialization identifies the Monad-derived
    Applicative pairing with the original Arrow pairing. The existing
    underlying natural isomorphism preserves Applicative operations in
    both directions; no closed structure or common native size is needed. *)

(** * 动态重建的 Applicative 相容性

    固定原生广集上的 ArrowApply，保持计算对象、Hom 载体与相等层级独立。
    命名通过已有纯箭头、复合及上下文律保持导出的有序运算。其终输入特化将
    Monad 导出的 Applicative 配对与原 Arrow 配对相识别。已有底层自然同构
    双向保持 Applicative 运算，不需要闭结构或共同原生大小。 *)

Section Comparison.
Universes o u p.
Context {K : Cat@{o u p _ _}} (AA : ArrowApply K).

(** Naming preserves right context, since exchange is a pure arrow. *)

(** 交换为纯箭头，因此命名保持右上下文。 *)

Lemma dynamic_naming_first {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : Hom (AA X) (AA Y))
  : arrow_dynamic_name AA first[AA; f; Z] ≈f
      first[ArrowKleisli AA; arrow_dynamic_name AA f; Z].
Proof.
  change (@HomEq (KleisliCat (ArrowMonad AA)) (X ×S Z) (Y ×S Z)
    (fmap (DynamicNamingF AA) first[AA; f; Z])
    first[ArrowKleisli AA; arrow_dynamic_name AA f; Z]).
  unfold arrow_first, arrow_second.
  etransitivity.
  - exact (@functor_comp (ComputationCat AA)
      (KleisliCat (ArrowMonad AA)) (DynamicNamingF AA)
      (X ×S Z) (Z ×S X) (Y ×S Z) _ _).
  - apply (@comp_proper (KleisliCat (ArrowMonad AA))
      (X ×S Z) (Z ×S X) (Y ×S Z)).
    + etransitivity.
      * exact (@functor_comp (ComputationCat AA)
          (KleisliCat (ArrowMonad AA)) (DynamicNamingF AA)
          (Z ×S X) (Z ×S Y) (Y ×S Z) _ _).
      * apply (@comp_proper (KleisliCat (ArrowMonad AA))
          (Z ×S X) (Z ×S Y) (Y ×S Z)).
        -- exact (dynamic_naming_pure AA _).
        -- exact (dynamic_naming_context AA Z f).
    + exact (dynamic_naming_pure AA _).
Qed.

(** Ordered splitting is preserved without exchanging its two effects. *)

(** 保持有序 split，不交换其中两个效应。 *)

Lemma dynamic_naming_split {X Y X' Y' : SetC@{u p}}
    (f : Hom (AA X) (AA Y)) (g : Hom (AA X') (AA Y'))
  : arrow_dynamic_name AA (f ***[AA] g) ≈f
      (arrow_dynamic_name AA f ***[ArrowKleisli AA] arrow_dynamic_name AA g).
Proof.
  change (@HomEq (KleisliCat (ArrowMonad AA)) (X ×S X') (Y ×S Y')
    (fmap (DynamicNamingF AA) (f ***[AA] g))
    (arrow_dynamic_name AA f ***[ArrowKleisli AA] arrow_dynamic_name AA g)).
  unfold arrow_split, arrow_second.
  etransitivity.
  - exact (@functor_comp (ComputationCat AA)
      (KleisliCat (ArrowMonad AA)) (DynamicNamingF AA)
      (X ×S X') (Y ×S X') (Y ×S Y') _ _).
  - apply (@comp_proper (KleisliCat (ArrowMonad AA))
      (X ×S X') (Y ×S X') (Y ×S Y')).
    + exact (dynamic_naming_context AA Y g).
    + exact (dynamic_naming_first X' f).
Qed.

(** Pure copying and ordered splitting give the fanout comparison in every
    shared ordinary input, not only at terminal input. *)

(** 纯复制与有序 split 在每个共同通常输入处给出 fanout 比较，不限于终输入。 *)

Lemma dynamic_naming_fanout {W X Y : SetC@{u p}}
    (f : Hom (AA W) (AA X)) (g : Hom (AA W) (AA Y))
  : arrow_dynamic_name AA (f &&&[AA] g) ≈f
      (arrow_dynamic_name AA f &&&[ArrowKleisli AA] arrow_dynamic_name AA g).
Proof.
  change (@HomEq (KleisliCat (ArrowMonad AA)) W (X ×S Y)
    (fmap (DynamicNamingF AA) (f &&&[AA] g))
    (arrow_dynamic_name AA f &&&[ArrowKleisli AA] arrow_dynamic_name AA g)).
  unfold arrow_fanout.
  etransitivity.
  - exact (@functor_comp (ComputationCat AA)
      (KleisliCat (ArrowMonad AA)) (DynamicNamingF AA)
      W (W ×S W) (X ×S Y) _ _).
  - apply (@comp_proper (KleisliCat (ArrowMonad AA)) W (W ×S W) (X ×S Y)).
    + exact (dynamic_naming_split f g).
    + exact (dynamic_naming_pure AA _).
Qed.

(** Both Applicatives have the same global-computation values. Reuse the
    identity-component comparison of the recovered Monad's functor. *)

(** 两个 Applicative 具有相同全局计算值；复用回收 Monad 函子的恒等分量比较。 *)

Definition DynamicApplicativeIso
  : MonadA (ArrowStrongM AA) ≅N ArrowA K AA
  := ArrowMonadUnderlyingIso AA.

(** Use the operation laws while leaving their computations abstract;
    transparency is restored before exposing clients. *)

(** 使用运算定律，同时保持其计算抽象；暴露客户端前恢复透明性。 *)

Local Opaque monad_pair arrow_fanout.

(** Pair abstract global computations before specializing to computations
    stored inside lifted products. Specialize the general Kleisli fanout
    comparison and cancel naming at terminal input. *)

(** 先配对抽象全局计算，再特化到存于提升积中的计算。特化一般 Kleisli fanout
    比较，并消去终输入处的命名。 *)

Lemma dynamic_applicative_pair (X Y : SetC@{u p})
    (f : ArrowGlobalF AA X) (g : ArrowGlobalF AA Y)
  : φ₂[MonadA (ArrowStrongM AA); X; Y] (f,g) ≈S
      φ₂[ArrowA K AA; X; Y] (f,g).
Proof.
  symmetry.
  pose (nf := @arrow_dynamic_name K AA UnitS X f).
  pose (ng := @arrow_dynamic_name K AA UnitS Y g).
  transitivity (@arrow_dynamic_name K AA UnitS (X ×S Y)
    (@arrow_fanout SetCat K SetCat_HasTerminal SetCat_HasProduct
      AA UnitS X Y f g) tt).
  + symmetry. exact (@arrow_dynamic_name_global K AA (X ×S Y) _).
  + transitivity (@arrow_fanout SetCat (KleisliCat (ArrowMonad AA))
      SetCat_HasTerminal SetCat_HasProduct (ArrowKleisli AA)
      UnitS X Y nf ng tt).
    * exact (@dynamic_naming_fanout UnitS X Y f g tt).
    * transitivity (@monad_pair SetCat SetCat_HasTerminal
        SetCat_HasProduct (ArrowStrongM AA) X Y (nf tt,ng tt)).
      -- exact (@kleisli_arrow_fanout SetCat SetCat_HasTerminal
           SetCat_HasProduct (ArrowStrongM AA) UnitS X Y nf ng tt).
      -- apply func_proper. split;
           [exact (@arrow_dynamic_name_global K AA X f)|
            exact (@arrow_dynamic_name_global K AA Y g)].
Qed.

(** The direct and recovered routes preserve pure and ordered pairing,
    using the preceding abstract-value comparison. *)

(** 直接路径与回收路径通过前面的抽象值比较，保持纯值与有序配对。 *)

Lemma dynamic_applicative_hom
  : is_applicative_hom (MonadA (ArrowStrongM AA)) (ArrowA K AA)
      DynamicApplicativeIso.1.
Proof.
  split.
  - intros X x. exact (arrow_monad_unit AA X x).
  - intros X Y.
    change (@HomEq SetCat (ArrowGlobalF AA X ×S ArrowGlobalF AA Y)
      (ArrowGlobalF AA (X ×S Y))
      (id_resp ∘r φ₂[MonadA (ArrowStrongM AA); X; Y])
      (φ₂[ArrowA K AA; X; Y] ∘r
        (@cross SetCat SetCat_HasProduct
          (ArrowGlobalF AA X) (ArrowGlobalF AA Y)
          (ArrowGlobalF AA X) (ArrowGlobalF AA Y) id_resp id_resp))).
    rewrite (@comp_id_l SetCat), (@cross_id SetCat SetCat_HasProduct),
      (@comp_id_r SetCat).
    intros [f g]. exact (dynamic_applicative_pair X Y f g).
Qed.

(** The same chosen natural inverse preserves both operations by the
    general inverse theorem, without another calculation of Monad pairing. *)

(** 同一个选定自然逆由一般求逆定理保持两种运算，无需再次计算 Monad 配对。 *)

Lemma dynamic_applicative_inverse_hom
  : is_applicative_hom (ArrowA K AA) (MonadA (ArrowStrongM AA))
      (DynamicApplicativeIso.1 ^-1N DynamicApplicativeIso.2).
Proof.
  exact (applicative_hom_inverse _ _ _ dynamic_applicative_hom
    DynamicApplicativeIso.2).
Qed.

Local Transparent monad_pair arrow_fanout.

End Comparison.
