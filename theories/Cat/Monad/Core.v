From Cats Require Export
  Cat.Monoidal.Monoid
  Cat.Monoidal.Endomorphism.
From Cats Require Import
  Cat.Bicategory.Core
  Cat.Bicategory.Cat.

(** * Monads as Monoid Objects

    A bicategorical monad is a monoid object in its endomorphism monoidal
    category. This is a transparent specialization, not a second record of
    the same data and laws. In the category bicategory the carrier is an
    endofunctor, and its unit and multiplication are natural transformations.
    Equalities of these transformations are [NatEq]. *)

(** * 作为幺半群对象的 Monad

    双范畴中的 Monad 就是自同态幺半范畴中的幺半群对象。这是透明特化，不再用
    第二个记录重复数据与定律。在范畴双范畴中，载体是自函子，单位和乘法是
    自然变换，其相等使用 [NatEq]。 *)

Definition BicatMonad (B : Bicat) (X : ObB B)
  : Type
  := MonoidObject (EndoMonoidal B X).

(** Endofunctor composition is the tensor; the identity functor is its
    unit. Coherence is inherited through [CatBicat]. *)

(** 自函子复合是张量，恒等函子是单位；相干性通过 [CatBicat] 继承。 *)

Definition EndofunctorMonoidal (C : Cat)
  : MonoidalCategory (Fct C C)
  := EndoMonoidal CatBicat C.

(** Ordinary monads use the same monoid-object structure. No conversion or
    equality of proof-bearing records is required by this identification. *)

(** 普通 Monad 使用同一个幺半群对象结构；这个识别不需要转换或含证明记录的
    相等。 *)

Definition Monad (C : Cat)
  : Type
  := MonoidObject (EndofunctorMonoidal C).

(** The underlying endofunctor. *)

(** 底层自函子。 *)

Definition MonadF {C : Cat} (M : Monad C)
  : Functor C C
  := MonoidCarrier M.

(** The unit, from the identity endofunctor. *)

(** 从恒等自函子出发的单位。 *)

Definition monad_unit {C : Cat} (M : Monad C)
  : IdF ⇒ MonadF M
  := monoid_object_unit M.

(** The multiplication, from the composite endofunctor. *)

(** 从复合自函子出发的乘法。 *)

Definition monad_mul {C : Cat} (M : Monad C)
  : MonadF M ∘F MonadF M ⇒ MonadF M
  := monoid_object_mul M.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "'T[' M ']'" := (MonadF M) : monad_scope.
Notation "'η[' M ']'" := (monad_unit M) : monad_scope.
Notation "'μ[' M ']'" := (monad_mul M) : monad_scope.
Local Open Scope monad_scope.

(** The first unit equation, evaluating the unit at [T X]. *)

(** 第一条单位方程，在 [T X] 处计算单位。 *)

Lemma monad_unit_l {C : Cat} (M : Monad C)
  : (μ[M] ∘Nv (η[M] ∘Nr T[M])) ≈N (CompF_id_l T[M]).1.
Proof.
  intros X. pose proof (monoid_object_unit_l M X) as H.
  change (μ[M] X ∘ (η[M] (T[M] X) ∘ id) ≈ id) in H.
  rewrite comp_id_r in H. exact H.
Qed.

(** The second unit equation, applying [T] to a unit component. *)

(** 第二条单位方程，将 [T] 作用于单位分量。 *)

Lemma monad_unit_r {C : Cat} (M : Monad C)
  : (μ[M] ∘Nv (T[M] ∘Nl η[M])) ≈N (CompF_id_r T[M]).1.
Proof.
  intros X. pose proof (monoid_object_unit_r M X) as H.
  change (μ[M] X ∘ (id ∘ fmap T[M] (η[M] X)) ≈ id) in H.
  rewrite comp_id_l in H. exact H.
Qed.

(** Pointwise, the canonical unitors reduce to identity arrows. *)

(** 逐点求值时，规范单位子归约为恒等箭头。 *)

Lemma monad_unit_l_component {C : Cat} (M : Monad C) (X : @Ob C)
  : μ[M] X ∘ η[M] (T[M] X) ≈ id.
Proof. exact (monad_unit_l M X). Qed.

(** The second pointwise unit equation applies the endofunctor to [η]. *)

(** 第二条逐点单位方程将自函子作用于 [η]。 *)

Lemma monad_unit_r_component {C : Cat} (M : Monad C) (X : @Ob C)
  : μ[M] X ∘ fmap T[M] (η[M] X) ≈ id.
Proof. exact (monad_unit_r M X). Qed.

(** Componentwise associativity is the familiar multiplication equation.
    Functor identity laws remove the identity factors introduced by
    horizontal composition; no native equality of functors is used. *)

(** 逐分量结合律就是通常的乘法方程。函子恒等律消去水平复合引入的恒等因子，
    不使用函子的原生相等。 *)

Lemma monad_assoc_component {C : Cat} (M : Monad C) (X : @Ob C)
  : μ[M] X ∘ μ[M] (T[M] X) ≈ μ[M] X ∘ fmap T[M] (μ[M] X).
Proof.
  pose proof (monoid_object_assoc M X) as H.
  change (μ[M] X ∘ (μ[M] (T[M] X) ∘ fmap T[M] (fmap T[M] id)) ≈
    (μ[M] X ∘ (id ∘ fmap T[M] (μ[M] X))) ∘ id) in H.
  rewrite !functor_id, !comp_id_l, !comp_id_r in H. exact H.
Qed.

(** At the natural-transformation level the canonical associator aligns
    the two source functors. Its identity components recover the preceding
    pointwise equation. *)

(** 在自然变换层面，用规范结合子对齐两侧来源函子；其恒等分量恢复前面的逐点
    方程。 *)

Lemma monad_assoc {C : Cat} (M : Monad C)
  : (μ[M] ∘Nv (μ[M] ∘Nr T[M])) ≈N
      (μ[M] ∘Nv (T[M] ∘Nl μ[M]) ∘Nv
        (CompF_assoc T[M] T[M] T[M]).1).
Proof.
  intros X. cbn. rewrite comp_id_r. exact (monad_assoc_component M X).
Qed.

(** A convenient constructor from the ordinary pointwise monad laws.
    The natural transformations already supply naturality. The constructor
    derives the coherent monoid-object laws rather than storing another
    primitive Monad structure. *)

(** 从通常的逐点 Monad 定律构造结构的便捷入口。自然变换已提供自然性；构造器
    导出带相干比较的幺半群对象定律，不再保存另一种原始 Monad 结构。 *)

Program Definition MonadFromComponents {C : Cat} (T : Functor C C)
    (η : IdF ⇒ T) (μ : T ∘F T ⇒ T)
    (Hu : ∀ X, μ X ∘ η (T X) ≈ id)
    (Hv : ∀ X, μ X ∘ fmap T (η X) ≈ id)
    (Ha : ∀ X, μ X ∘ μ (T X) ≈ μ X ∘ fmap T (μ X))
  : Monad C
  :=
  {|MonoidCarrier := T
  ; monoid_object_unit := η
  ; monoid_object_mul := μ
  |}.
Next Obligation.
  intros X. change (μ X ∘ (η (T X) ∘ id) ≈ id).
  rewrite comp_id_r. apply Hu.
Defined.
Next Obligation.
  intros X. change (μ X ∘ (id ∘ fmap T (η X)) ≈ id).
  rewrite comp_id_l. apply Hv.
Defined.
Next Obligation.
  intros X.
  change (μ X ∘ (μ (T X) ∘ fmap T (fmap T id)) ≈
    (μ X ∘ (id ∘ fmap T (μ X))) ∘ id).
  rewrite !functor_id, !comp_id_l, !comp_id_r. apply Ha.
Defined.

(** Fixed-base monad morphisms are precisely the monoid homomorphisms in
    this endofunctor monoidal category. This does not define moving-base
    lax or oplax bicategorical monad morphisms. *)

(** 固定基底上的 Monad 态射就是此自函子幺半范畴中的幺半群同态；这里没有定义
    移动基底的 lax 或 oplax 双范畴 Monad 态射。 *)

Definition MonadCat (C : Cat)
  : Cat
  := MonoidCat (EndofunctorMonoidal C).

(** A fixed-base monad morphism preserves the unit natural transformation. *)

(** 固定基底的 Monad 态射保持单位自然变换。 *)

Lemma monad_hom_unit {C : Cat} {M N : Monad C}
    (α : (@Hom (MonadCat C)) M N)
  : (α.1 ∘Nv η[M]) ≈N η[N].
Proof. exact (fst α.2). Qed.

(** Multiplication preservation uses horizontal composition of the same
    natural transformation with itself, not a product of endofunctors. *)

(** 乘法保持性使用同一自然变换与自身的水平复合，不使用自函子的积。 *)

Lemma monad_hom_mul {C : Cat} {M N : Monad C}
    (α : (@Hom (MonadCat C)) M N)
  : (α.1 ∘Nv μ[M]) ≈N (μ[N] ∘Nv (α.1 ∘Nh α.1)).
Proof. exact (snd α.2). Qed.
