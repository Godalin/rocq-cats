From Cats Require Export
  Instance.Set.Simplicial.Core
  Cat.Shape.Simplex.Operators.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Faces and Degeneracies

    All simplicial identities follow by applying restriction to the
    corresponding equations in the simplex category. Write [d[X; i]] and
    [s[X; i]], or [d[X; n; i]] and [s[X; n; i]] with an explicit degree. *)

(** * 面与退化

    所有单纯恒等式均通过对单纯范畴中的对应方程施加限制得到。记作 [d[X; i]]、
    [s[X; i]]，也可用 [d[X; n; i]]、[s[X; n; i]] 显式指定维数。 *)

(** A face deletes the position selected by a bounded index. *)

(** 面删除由有界索引选定的位置。 *)

Definition simplex_face@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i : Ordinal (S n))
  : X (S n) →r X n
  := X[δ[n; i]]Δ.

Notation "'d[' X ';' i ']'" := (simplex_face (X := X) i)
  : hom_scope.
Notation "'d[' X ';' n ';' i ']'" := (@simplex_face X n i)
  : hom_scope.

(** A degeneracy repeats the selected position. *)

(** 退化重复选定位置。 *)

Definition simplex_degeneracy@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i : Ordinal n)
  : X n →r X (S n)
  := X[σ[n; i]]Δ.

Notation "'s[' X ';' i ']'" := (simplex_degeneracy (X := X) i)
  : hom_scope.
Notation "'s[' X ';' n ';' i ']'" := (@simplex_degeneracy X n i)
  : hom_scope.

(** Two faces commute with the appropriate index shift. *)

(** 两个面在适当的索引移位下交换。 *)

Lemma simplex_face_comp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i j : Ordinal (S n)) (H : fin_rank i ≤ fin_rank j)
  : (d[X; n; j] ∘r d[X; S n; i↑]) ≈f
      (d[X; n; i] ∘r d[X; S n; j⁺]).
Proof.
  unfold simplex_face. rewrite <- !simplex_restrict_comp.
  apply simplex_restrict_proper. exact (coface_comp i j H).
Qed.

(** Two degeneracies commute with the appropriate index shift. *)

(** 两个退化在适当的索引移位下交换。 *)

Lemma simplex_degeneracy_comp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i j : Ordinal n) (H : fin_rank i ≤ fin_rank j)
  : (s[X; S n; j⁺] ∘r s[X; n; i]) ≈f
      (s[X; S n; i↑] ∘r s[X; n; j]).
Proof.
  unfold simplex_degeneracy. rewrite <- !simplex_restrict_comp.
  apply simplex_restrict_proper. exact (codegeneracy_comp i j H).
Qed.

(** The face at a repeated position cancels its degeneracy. *)

(** 重复位置处的面消去其退化。 *)

Lemma simplex_face_degeneracy_id@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i : Ordinal n)
  : (d[X; n; i↑] ∘r s[X; n; i]) ≈f id_resp.
Proof.
  unfold simplex_face, simplex_degeneracy.
  rewrite <- simplex_restrict_comp.
  transitivity (X[(id : (@Hom Δ) n n)]Δ).
  - apply simplex_restrict_proper. apply codegeneracy_coface_id.
  - apply simplex_restrict_id.
Qed.

(** The face at the next position also cancels the degeneracy. *)

(** 紧邻后继位置处的面同样消去退化。 *)

Lemma simplex_face_degeneracy_next@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i : Ordinal n)
  : (d[X; n; i⁺] ∘r s[X; n; i]) ≈f id_resp.
Proof.
  unfold simplex_face, simplex_degeneracy.
  rewrite <- simplex_restrict_comp.
  transitivity (X[(id : (@Hom Δ) n n)]Δ).
  - apply simplex_restrict_proper. apply codegeneracy_coface_next.
  - apply simplex_restrict_id.
Qed.

(** Interchange a face with a later degeneracy. *)

(** 交换面与在其后的退化。 *)

Lemma simplex_face_degeneracy_before@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i : Ordinal (S n)) (j : Ordinal n)
    (H : fin_rank i ≤ fin_rank j)
  : (d[X; S n; i↑] ∘r s[X; S n; j⁺]) ≈f
      (s[X; n; j] ∘r d[X; n; i]).
Proof.
  unfold simplex_face, simplex_degeneracy.
  rewrite <- !simplex_restrict_comp.
  apply simplex_restrict_proper. exact (codegeneracy_coface_before i j H).
Qed.

(** Interchange a face with an earlier degeneracy. *)

(** 交换面与在其前的退化。 *)

Lemma simplex_face_degeneracy_after@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (i : Ordinal (S n)) (j : Ordinal n)
    (H : fin_rank j < fin_rank i)
  : (d[X; S n; i⁺] ∘r s[X; S n; j↑]) ≈f
      (s[X; n; j] ∘r d[X; n; i]).
Proof.
  unfold simplex_face, simplex_degeneracy.
  rewrite <- !simplex_restrict_comp.
  apply simplex_restrict_proper. exact (codegeneracy_coface_after i j H).
Qed.

(** Simplicial maps commute with faces. *)

(** 单纯映射与面交换。 *)

Lemma simplex_face_natural@{u p +}
    {X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} (α : X ⇒ Y)
    {n : nat} (i : Ordinal (S n))
  : (α n ∘r d[X; n; i]) ≈f (d[Y; n; i] ∘r α (S n)).
Proof. apply simplex_restrict_natural. Qed.

(** Simplicial maps commute with degeneracies. *)

(** 单纯映射与退化交换。 *)

Lemma simplex_degeneracy_natural@{u p +}
    {X Y : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} (α : X ⇒ Y)
    {n : nat} (i : Ordinal n)
  : (α (S n) ∘r s[X; n; i]) ≈f (s[Y; n; i] ∘r α n).
Proof. apply simplex_restrict_natural. Qed.
