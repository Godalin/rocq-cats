From Cats Require Export
  Cat.Shape.Simplex.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Presheaf.

(** * Simplicial Sets with Specified Equality

    Simplicial sets are setoid-valued presheaves on the simplex category.
    Their maps are natural transformations, compared by pointwise specified
    equality. No quotient or native equality of functions is required.
    Write [X[θ]Δ] for restriction along a simplex operator. *)

(** * 带指定相等的单纯集合

    单纯集合是单纯范畴上的广集值预层；映射是自然变换，按逐点指定相等比较。
    此处不要求商集或函数的原生相等；沿单纯算子的限制记为 [X[θ]Δ]。 *)

Definition SimplicialCat@{u p +}
  : Cat
  := Fct (Δ^op) SetCat@{u p _ _ _ _ _}.

Notation sSet := SimplicialCat.

(** Restriction along a simplex operator reverses its direction. Its source
    and target are the original value setoids, with independent sizes. *)

(** 沿单纯算子的限制反转其方向；源和目标沿用原值广集，保持大小的独立性。 *)

Definition simplex_restrict@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {m n : nat}
    (θ : (@Hom Δ) m n)
  : X n →r X m
  := fmap X θ.

Notation "X '[' θ ']Δ'" := (simplex_restrict (X := X) θ)
  (at level 8, left associativity, format "X [ θ ]Δ") : hom_scope.

(** Restriction along the identity is the identity map. *)

(** 沿恒等的限制是恒等映射。 *)

Lemma simplex_restrict_id@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} (n : nat)
  : X[(id : (@Hom Δ) n n)]Δ ≈f id_resp.
Proof. exact (functor_id _ _ X). Qed.

(** Restriction reverses composition. *)

(** 限制反转复合次序。 *)

Lemma simplex_restrict_comp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {l m n : nat}
    (θ : (@Hom Δ) m n) (φ : (@Hom Δ) l m)
  : X[θ ∘ φ]Δ ≈f (X[φ]Δ ∘r X[θ]Δ).
Proof. exact (functor_comp _ _ X φ θ). Qed.

(** Equivalent simplex operators induce equal restriction maps. *)

(** 等价的单纯算子诱导相等的限制映射。 *)

Global Instance simplex_restrict_proper@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {m n : nat}
  : Proper (@HomEq Δ m n ==> FunEq) (@simplex_restrict X m n).
Proof. exact (@functor_fmap_proper _ _ X n m). Qed.

(** A map of simplicial sets commutes with every restriction. *)

(** 单纯集合映射与每个限制交换。 *)

Lemma simplex_restrict_natural@{u p +}
    {X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    (α : X ⇒ Y) {m n : nat} (θ : (@Hom Δ) m n)
  : (α m ∘r X[θ]Δ) ≈f (Y[θ]Δ ∘r α n).
Proof. exact (nt_naturality α θ). Qed.
