From Cats Require Export
  Instance.Set.Simplicial.Operators.
From Cats Require Import
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Yoneda.

Local Open Scope nat_scope.

(** * Standard Simplices and Their Elements

    Standard simplices are representables, raised to the selected value
    universes. The wrappers express an ordinary size inclusion, not resizing.
    Write [Δ[n]] for the standard simplex and [⟦x⟧Δ[X; n]] for the map
    determined by an n-simplex x of X. *)

(** * 标准单形及其元素

    标准单形是提升到所选值宇宙的可表函子；包装表达通常的大小嵌入，不是大小重设。
    标准单形记作 [Δ[n]]，X 的 n-单形 x 所确定的映射记作 [⟦x⟧Δ[X; n]]。 *)

Definition StandardSimplex@{u p +} (n : nat)
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := RaisedEmbedding (C := Δ) n.

Notation "'Δ[' n ']'" := (StandardSimplex n) : ob_scope.

(** The standard-simplex embedding inherits all functor laws from raised
    Yoneda, including its action by postcomposition. *)

(** 标准单形嵌入继承提升的 Yoneda 的全部函子律，其箭头作用是后合成。 *)

Definition StandardSimplexF@{u p +}
  : Functor Δ (Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := RaisedEmbedding (C := Δ).

(** The simplex category is fully faithfully embedded among simplicial sets. *)

(** 单纯范畴全忠实地嵌入单纯集合中。 *)

Theorem standard_simplex_fully_faithful@{u p +}
  : is_fully_faithful
      (StandardSimplexF : Functor Δ (Fct (Δ^op) SetCat@{u p _ _ _ _ _})).
Proof. apply raised_embedding_fully_faithful. Defined.

(** The generic n-simplex is the lifted identity of [n]. *)

(** 泛 n-单形是 [n] 的提升恒等。 *)

Definition simplex_generic@{u p +} (n : nat)
  : (Δ[n] : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n
  :=
  {|lower := (id : (@Hom Δ) n n)
  |}.

(** Every n-simplex of X determines a unique map from the standard n-simplex.
    Both directions are respectful and retain their computation. *)

(** X 的每个 n-单形唯一确定从标准 n-单形出发的映射；双向均保持相等和计算。 *)

Definition simplex_element_resp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
  : Nat_SetS Δ[n] X →r X n
  := presheaf_yoneda_resp (C := Δ) (P := X) (X := n).

(** Reconstruct a map from a simplex by restriction along each simplex
    operator. *)

(** 沿各单纯算子限制一个单形，重构由它确定的映射。 *)

Definition simplex_map_resp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
  : X n →r Nat_SetS Δ[n] X
  := presheaf_yoneda_inv_resp (C := Δ) (P := X) (X := n).

Notation "'⟦' x '⟧Δ[' X ';' n ']'" := (@simplex_map_resp X n x)
  : hom_scope.

(** Evaluation of a reconstructed map recovers the chosen simplex. *)

(** 求值重构的映射恢复所选单形。 *)

Lemma simplex_element_β@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} (x : X n)
  : simplex_element_resp ⟦x⟧Δ[X; n] ≈S x.
Proof. apply presheaf_yoneda_β. Qed.

(** Reconstruction of the generic image recovers a simplicial map. *)

(** 从泛单形的像重构恢复原单纯映射。 *)

Lemma simplex_element_η@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} (α : Δ[n] ⇒ X)
  : ⟦simplex_element_resp α⟧Δ[X; n] ≈N α.
Proof. apply presheaf_yoneda_η. Qed.

(** Maps from the standard n-simplex correspond to n-simplices as setoids.
    Lift both sides only to package their different native sizes together. *)

(** 从标准 n-单形出发的映射与 n-单形构成广集同构；仅为统一包装不同的原生大小
    而提升两侧。 *)

Definition simplex_element_iso@{u p v q +}
    {X : Functor (Δ^op) SetCat@{v q _ _ _ _ _}} (n : nat)
  : LiftS@{_ _ u p} (Nat_SetS Δ[n] X) ≅[SetCat]
      LiftS@{_ _ u p} (X n)
  := presheaf_yoneda_iso (C := Δ) (P := X) (X := n).

(** Maps out of a standard simplex agree exactly when their generic images
    agree. *)

(** 从标准单形出发的映射相等，当且仅当其泛单形的像相等。 *)

Lemma simplex_map_unique@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} (α β : Δ[n] ⇒ X)
  : α ≈N β ↔ simplex_element_resp α ≈S simplex_element_resp β.
Proof.
  split.
  - intros H. exact (H n (simplex_generic n)).
  - intros H. transitivity ⟦simplex_element_resp α⟧Δ[X; n].
    + symmetry. apply simplex_element_η.
    + transitivity ⟦simplex_element_resp β⟧Δ[X; n].
      * exact (@func_proper _ _ simplex_map_resp _ _ H).
      * apply simplex_element_η.
Qed.

(** The Yoneda correspondence commutes with a map of simplicial sets. *)

(** Yoneda 对应与单纯集合映射交换。 *)

Lemma simplex_element_natural@{u p +}
    {X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (α : X ⇒ Y) (β : Δ[n] ⇒ X)
  : simplex_element_resp (α ∘Nv β) ≈S α n (simplex_element_resp β).
Proof. apply presheaf_yoneda_natural_presheaf. Qed.

(** Precomposing with a map of standard simplices corresponds to restriction
    of its generic image, including all faces and degeneracies. *)

(** 与标准单形之间的映射预合成，对应于限制泛单形的像；特别包含全部面和退化。 *)

Lemma simplex_element_restrict@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {m n : nat}
    (θ : (@Hom Δ) m n) (α : Δ[n] ⇒ X)
  : simplex_element_resp (α ∘Nv fmap StandardSimplexF θ) ≈S
      X[θ]Δ (simplex_element_resp α).
Proof.
  exact (presheaf_yoneda_natural_object (C := Δ) (P := X) θ α).
Qed.
