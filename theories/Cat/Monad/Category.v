From Cats.Set Require Import
  Subset.
From Cats Require Export
  Cat.Monad.Core.

Local Open Scope monad_scope.

(** * Fixed-base Monad Morphisms

    A morphism on a fixed category is a natural transformation preserving
    unit and multiplication. Its equality compares components, retaining
    preservation witnesses without asking them to be equal. *)

(** * 固定基底的 Monad 态射

    固定范畴上的态射是保持单位与乘法的自然变换；相等逐分量比较，保持性见证
    保留在数据中，但无需比较它们是否相等。 *)

Section MonadMorphisms.
Context {C : Cat}.

(** Multiplication preservation uses horizontal composition, not a
    categorical product. This concerns fixed-base morphisms only. *)

(** 乘法保持性使用水平复合，而非范畴积；这里只处理固定基底态射。 *)

Definition is_monad_hom (M N : Monad C) (α : M ⇒ N)
  : Type
  := (α ∘Nv η[M]) ≈N η[N] ∧
      (α ∘Nv μ[M]) ≈N (μ[N] ∘Nv (α ∘Nh α)).

(** Equal natural transformations satisfy the same preservation laws. *)

(** 相等自然变换满足相同的保持定律。 *)

Lemma monad_hom_equiv (M N : Monad C) (α β : M ⇒ N)
    (E : α ≈N β)
  : is_monad_hom M N α ↔ is_monad_hom M N β.
Proof.
  split; intros [Hu Hm]; split.
  - rewrite <- E. exact Hu.
  - rewrite <- E. exact Hm.
  - rewrite E. exact Hu.
  - rewrite E. exact Hm.
Qed.

(** The subset of natural transformations satisfying both diagrams. *)

(** 满足两个交换图表的自然变换子广集。 *)

Definition MonadHomS (M N : Monad C)
  : SetC
  := SubsetS (@HomSet (Fct C C) M N) (is_monad_hom M N).

(** The identity transformation preserves the operations. *)

(** 恒等自然变换保持运算。 *)

Definition monad_hom_id (M : Monad C)
  : MonadHomS M M.
Proof.
  exists idN. split; intros X.
  - exact (comp_id_l (η[M] X)).
  - cbn. rewrite functor_id, !comp_id_l, !comp_id_r. reflexivity.
Defined.

(** Vertical composition preserves multiplication by interchange. *)

(** 由交换律，垂直复合保持乘法。 *)

Definition monad_hom_comp {M N P : Monad C}
    (β : MonadHomS N P) (α : MonadHomS M N)
  : MonadHomS M P.
Proof.
  exists (β.1 ∘Nv α.1).
  destruct α as [α [Hαu Hαm]], β as [β [Hβu Hβm]].
  cbn. split; intros X.
  - change ((β X ∘ α X) ∘ η[M] X ≈ η[P] X).
    rewrite comp_assoc, (Hαu X). exact (Hβu X).
  - change ((β X ∘ α X) ∘ μ[M] X ≈
      μ[P] X ∘ ((β ∘Nv α) ∘Nh (β ∘Nv α)) X).
    rewrite (nt_comp_h_interchange β α β α X).
    change ((β X ∘ α X) ∘ μ[M] X ≈
      μ[P] X ∘ ((β ∘Nh β) X ∘ (α ∘Nh α) X)).
    transitivity (β X ∘ (μ[N] X ∘ (α ∘Nh α) X)).
    + rewrite comp_assoc. apply comp_proper; [reflexivity | exact (Hαm X)].
    + transitivity ((β X ∘ μ[N] X) ∘ (α ∘Nh α) X).
      * symmetry. apply comp_assoc.
      * transitivity ((μ[P] X ∘ (β ∘Nh β) X) ∘ (α ∘Nh α) X).
        -- apply comp_proper; [exact (Hβm X) | reflexivity].
        -- apply comp_assoc.
Defined.

End MonadMorphisms.

(** Monads and their fixed-base morphisms form a category. *)

(** Monad 及其固定基底态射组成范畴。 *)

Program Definition MonadCat (C : Cat)
  : Cat
  :=
  {|Ob := Monad C
  ; HomSet := MonadHomS
  ; id := monad_hom_id
  ; comp _ _ _ := monad_hom_comp
  |}.
Next Obligation.
  intros [β Hβ] [β' Hβ'] Eβ [α Hα] [α' Hα'] Eα.
  exact (@comp_proper (Fct C C) _ _ _ β β' Eβ α α' Eα).
Defined.
Next Obligation. exact (@comp_id_r (Fct C C) _ _ f.1). Defined.
Next Obligation. exact (@comp_id_l (Fct C C) _ _ f.1). Defined.
Next Obligation. exact (@comp_assoc (Fct C C) _ _ _ _ f.1 g.1 h.1). Defined.

(** A monad morphism preserves its unit. *)

(** Monad 态射保持单位。 *)

Lemma monad_hom_unit {C : Cat} {M N : Monad C}
    (α : (@Hom (MonadCat C)) M N)
  : (α.1 ∘Nv η[M]) ≈N η[N].
Proof. exact (fst α.2). Qed.

(** A monad morphism preserves its multiplication. *)

(** Monad 态射保持乘法。 *)

Lemma monad_hom_mul {C : Cat} {M N : Monad C}
    (α : (@Hom (MonadCat C)) M N)
  : (α.1 ∘Nv μ[M]) ≈N (μ[N] ∘Nv (α.1 ∘Nh α.1)).
Proof. exact (snd α.2). Qed.
