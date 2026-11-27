From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Ordinary Monads

    A monad is an endofunctor with natural unit and multiplication satisfying
    three componentwise equations. The specified hom-set equality is the
    strict equality used by these laws. Naturality is already part of the
    transformations; no equality of functor records is requested. Coercion
    exposes the underlying endofunctor, allowing [M X] and [fmap M f].

    The monoid characterization is proved in [monad_monoid_laws]. *)

(** * 普通 Monad

    Monad 是带有自然单位和乘法的自函子，满足三条逐分量方程。指定 Hom 广集
    相等就是这些定律使用的严格相等。自然变换已经包含自然性，不要求函子记录
    的相等。强制转换暴露底层自函子，可直接写 [M X] 和 [fmap M f]。
    独立的幺半群对象刻画见 [monad_monoid_laws]。 *)

(** The usual axioms for fixed data. All three witnesses live in [Type],
    and naturality is supplied by [η] and [μ]. *)

(** 固定数据上的通常公理。三条定律的见证均保留在 [Type] 中，自然性由 [η]
    和 [μ] 提供。 *)

Minks.Mixin IsMonad {C : Cat} (T : Fct C C)
    (η : IdF ⇒ T) (μ : T ∘F T ⇒ T)
  :=
  { monad_unit_l_component (X : C)
    : μ X ∘ η (T X) ≈ id
  ; monad_unit_r_component (X : C)
    : μ X ∘ fmap T (η X) ≈ id
  ; monad_assoc_component (X : C)
    : μ X ∘ μ (T X) ≈ μ X ∘ fmap T (μ X)
  }.

Arguments monad_unit_l_component {_} _ {_ _ _} _.
Arguments monad_unit_r_component {_} _ {_ _ _} _.
Arguments monad_assoc_component {_} _ {_ _ _} _.

(** Choose the unit and multiplication on a fixed endofunctor. *)

(** 在固定的自函子上选取单位和乘法。 *)

Minks.Mixin HasMonad {C : Cat} (T : Fct C C)
  :=
  { monad_unit : IdF ⇒ T
  ; monad_mul : T ∘F T ⇒ T
  ; isMonad
    :: IsMonad T monad_unit monad_mul
  }.

Arguments monad_unit {_} _ {_}.
Arguments monad_mul {_} _ {_}.
Arguments isMonad {_} _ {_}.

(** On a fixed endofunctor, the monad operations use the local [HasMonad]
    instance. *)

(** 在固定的自函子上，Monad 运算使用上下文中的 [HasMonad] 实例。 *)

Declare Scope monad_fct_scope.
Delimit Scope monad_fct_scope with monad_fct.
Notation "'η[' T ']'" := (monad_unit T)
  (at level 0, format "η[ T ]")
  : monad_fct_scope.
Notation "'μ[' T ']'" := (monad_mul T)
  (at level 0, format "μ[ T ]")
  : monad_fct_scope.

(** Bundle the endofunctor with its chosen monad structure. *)

(** 将自函子与其选定的 Monad 结构打包。 *)

Minks.Struct Monad (C : Cat)
  extends Fct C C
  with  hasMonad as hasMonad
        : HasMonad [C, carrier].

Arguments MakeMonad {_} _ _.
Arguments MonadToFct {_} _.
Arguments hasMonad {_} _.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "'T[' M ']'" := (MonadToFct M)
  (at level 0, format "T[ M ]")
  : monad_scope.
Notation "'η[' M ']'"
  := (@monad_unit _ _ (hasMonad M))
  (at level 0, format "η[ M ]")
  : monad_scope.
Notation "'μ[' M ']'"
  := (@monad_mul _ _ (hasMonad M))
  (at level 0, format "μ[ M ]")
  : monad_scope.
Local Open Scope monad_scope.

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
  : (μ[M] ∘Nv (μ[M] ∘Nr T[M]))
    ≈N (μ[M] ∘Nv (T[M] ∘Nl μ[M])
      ∘Nv (CompF_assoc T[M] T[M] T[M]).1).
Proof.
  intros X. cbn. rewrite comp_id_r.
  exact (monad_assoc_component M X).
Qed.
