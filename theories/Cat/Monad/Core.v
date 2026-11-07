From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Ordinary Monads

    A monad is an endofunctor with natural unit and multiplication satisfying
    three componentwise equations. The specified hom-set equality is the
    strict equality used by these laws. Naturality is already part of the
    transformations; no equality of functor records is requested.

    The monoid characterization is proved in [monad_monoid_laws]. *)

(** * 普通 Monad

    Monad 是带有自然单位和乘法的自函子，满足三条逐分量方程。指定 Hom 广集
    相等就是这些定律使用的严格相等。自然变换已经包含自然性，不要求函子记录
    的相等。独立的幺半群对象刻画见 [monad_monoid_laws]。 *)

(** The usual axioms for fixed data. All three witnesses live in [Type],
    and naturality is supplied by [η] and [μ]. *)

(** 固定数据上的通常公理。三条定律的见证均保留在 [Type] 中，自然性由 [η]
    和 [μ] 提供。 *)

Definition is_monad {C : Cat} (T : Functor C C)
    (η : IdF ⇒ T) (μ : T ∘F T ⇒ T)
  : Type
  := (∀ X, μ X ∘ η (T X) ≈ id) ∧
      (∀ X, μ X ∘ fmap T (η X) ≈ id) ∧
      (∀ X, μ X ∘ μ (T X) ≈ μ X ∘ fmap T (μ X)).

(** A chosen ordinary monad, with its familiar axiomatic presentation.
    Computational data and their laws are bundled in one class. *)

(** 以通常公理呈现的选定普通 Monad；计算数据及其定律打包在同一个类中。 *)

Class Monad (C : Cat)
  :=
  { MonadF : Functor C C
  ; monad_unit : IdF ⇒ MonadF
  ; monad_mul : MonadF ∘F MonadF ⇒ MonadF
  ; monad_axioms : is_monad MonadF monad_unit monad_mul
  }.

Arguments MonadF {_} _.
Arguments monad_unit {_} _.
Arguments monad_mul {_} _.
Arguments monad_axioms {_} _.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "'T[' M ']'" := (MonadF M) : monad_scope.
Notation "'η[' M ']'" := (monad_unit M) : monad_scope.
Notation "'μ[' M ']'" := (monad_mul M) : monad_scope.
Local Open Scope monad_scope.

(** The first unit equation evaluates the unit at [T X]. *)

(** 第一条单位方程在 [T X] 处计算单位。 *)

Lemma monad_unit_l_component {C : Cat} (M : Monad C) (X : @Ob C)
  : μ[M] X ∘ η[M] (T[M] X) ≈ id.
Proof. exact (fst (monad_axioms M) X). Qed.

(** The second unit equation applies the endofunctor to the unit. *)

(** 第二条单位方程将自函子作用于单位。 *)

Lemma monad_unit_r_component {C : Cat} (M : Monad C) (X : @Ob C)
  : μ[M] X ∘ fmap T[M] (η[M] X) ≈ id.
Proof. exact (fst (snd (monad_axioms M)) X). Qed.

(** Associativity compares the two iterated multiplications. *)

(** 结合律比较两种迭代乘法。 *)

Lemma monad_assoc_component {C : Cat} (M : Monad C) (X : @Ob C)
  : μ[M] X ∘ μ[M] (T[M] X) ≈ μ[M] X ∘ fmap T[M] (μ[M] X).
Proof. exact (snd (snd (monad_axioms M)) X). Qed.

(** The canonical left unitor aligns the source functors. Its components
    are identity arrows, so this is precisely the first component law. *)

(** 规范左单位子对齐来源函子，其分量是恒等箭头，因此恰好恢复第一条分量律。 *)

Lemma monad_unit_l {C : Cat} (M : Monad C)
  : (μ[M] ∘Nv (η[M] ∘Nr T[M])) ≈N (CompF_id_l T[M]).1.
Proof. exact (monad_unit_l_component M). Qed.

(** The right unitor gives the transformation-level second unit law. *)

(** 右单位子给出自然变换层面的第二条单位律。 *)

Lemma monad_unit_r {C : Cat} (M : Monad C)
  : (μ[M] ∘Nv (T[M] ∘Nl η[M])) ≈N (CompF_id_r T[M]).1.
Proof. exact (monad_unit_r_component M). Qed.

(** The canonical associator aligns differently bracketed composites.
    This comparison uses [NatEq], not native equality of functors. *)

(** 规范结合子对齐不同加括号方式的复合；比较使用 [NatEq]，不用函子原生相等。 *)

Lemma monad_assoc {C : Cat} (M : Monad C)
  : (μ[M] ∘Nv (μ[M] ∘Nr T[M])) ≈N
      (μ[M] ∘Nv (T[M] ∘Nl μ[M]) ∘Nv
        (CompF_assoc T[M] T[M] T[M]).1).
Proof.
  intros X. cbn. rewrite comp_id_r. exact (monad_assoc_component M X).
Qed.

(** Construct directly from the three ordinary laws. The underlying
    endofunctor, unit and multiplication remain computationally unchanged. *)

(** 由三条通常定律直接构造 Monad；底层自函子、单位和乘法的计算行为保持不变。 *)

Program Definition MonadFromComponents {C : Cat} (T : Functor C C)
    (η : IdF ⇒ T) (μ : T ∘F T ⇒ T)
    (Hu : ∀ X, μ X ∘ η (T X) ≈ id)
    (Hv : ∀ X, μ X ∘ fmap T (η X) ≈ id)
    (Ha : ∀ X, μ X ∘ μ (T X) ≈ μ X ∘ fmap T (μ X))
  : Monad C
  :=
  {|MonadF := T
  ; monad_unit := η
  ; monad_mul := μ
  ; monad_axioms := (Hu, (Hv, Ha))
  |}.
