From Cats Require Export
  Instance.Set.Simplicial.Horn
  Instance.Set.Sieve.Matching.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Compatible Boundary and Horn Faces

    The generated-sieve matching correspondence specializes uniformly to
    boundaries and horns. Face indices and overlap factorizations remain
    explicit data. *)

(** * 边界与 horn 的相容面

    生成筛的匹配对应统一特化到边界与 horn；面索引及交叠分解均保留为显式数据。 *)

(** A boundary matching datum gives all faces and their overlap equations. *)

(** 边界匹配数据给出全部面及其交叠方程。 *)

Definition BoundaryMatchingS@{u p +}
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
  : SetC
  := @SieveMatchingS Δ (S n) (Ordinal (S n))
      (λ _, n) (λ j, δ[n; j]) X.

(** Evaluate a boundary map at its generic face. *)

(** 在泛面处求值边界映射。 *)

Program Definition boundary_face_resp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (j : Ordinal (S n))
  : BoundaryS X (S n) →r X n
  :=
  {|func b := b n {|lower := (δ[n; j]; boundary_face_member j)
                  |}
  |}.
Next Obligation. intros b c E. apply E. Defined.

Notation "'face∂[' j ']'" := (boundary_face_resp j) : hom_scope.

(** Boundary maps are equal exactly when their generic faces are equal. *)

(** 边界映射相等，当且仅当其泛面相等。 *)

Definition boundary_map_eq_iff@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (b c : BoundaryS X (S n))
  : b ≈S c ↔ ∀ j, face∂[j] b ≈S face∂[j] c
  := @generated_sieve_map_eq Δ (S n) (Ordinal (S n))
      (λ _, n) (λ j, δ[n; j]) X b c.

(** Restrict a boundary's faces along any equal pair of common factors. *)

(** 沿任意相等的共同因子对限制边界的面。 *)

Definition boundary_face_overlap@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (b : BoundaryS X (S n)) (j k : Ordinal (S n))
    {m : nat} (f g : (@Hom Δ) m n)
    (E : δ[n; j] ∘ f ≈ δ[n; k] ∘ g)
  : X[f]Δ (face∂[j] b) ≈S X[g]Δ (face∂[k] b)
  := @matching_overlap Δ (S n) (Ordinal (S n))
      (λ _, n) (λ j, δ[n; j]) X
      (@SieveMatchingOfN Δ (S n) (Ordinal (S n))
        (λ _, n) (λ j, δ[n; j]) X b) m j k f g E.

(** All face intersections satisfy the usual shifted face equation. *)

(** 全部面交满足通常的移位面方程。 *)

Definition boundary_face_comp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (b : BoundaryS X (S (S n)))
    (i j : Ordinal (S n)) (H : fin_rank i ≤ fin_rank j)
  : d[X; n; j] (face∂[i↑] b) ≈S d[X; n; i] (face∂[j⁺] b)
  := boundary_face_overlap b _ _ _ _ (coface_comp i j H).

(** Generated-sieve descent gives the full boundary matching isomorphism. *)

(** 生成筛下降给出完整的边界匹配同构。 *)

Definition boundary_matching_iso@{u p v q +}
    {X : Functor (Δ^op) SetCat@{v q _ _ _ _ _}} (n : nat)
  : LiftS@{_ _ u p} (BoundaryMatchingS X n) ≅[SetCat]
      LiftS@{_ _ u p} (BoundaryS X (S n))
  := @sieve_matching_iso Δ (S n) (Ordinal (S n))
      (λ _, n) (λ j, δ[n; j]) X.

(** Matching values on all retained faces, with every overlap equation. *)

(** 全部保留面上的匹配值及每个交叠方程。 *)

Definition HornMatchingS@{u p +}
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
    (n : nat) (i : Ordinal (S n))
  : SetC
  := @SieveMatchingS Δ (S n) (∃ j : Ordinal (S n), ¬ j = i)
      (λ _, n) (λ j, δ[n; j.1]) X.

(** Extract the value on a retained face. It is the image of that coface,
    so no identity substitution is inserted into the computational data. *)

(** 提取保留面的值；它是该余面的像，不向计算数据插入恒等替换。 *)

Program Definition horn_face_resp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (i j : Ordinal (S n)) (H : ¬ j = i)
  : HornS X (S n) i →r X n
  :=
  {|func h := h n {|lower := (δ[n; j]; horn_face_member i j H)
                  |}
  |}.
Next Obligation. intros h k E. apply E. Defined.

Notation "'face[' i ';' j ';' H ']'" := (horn_face_resp i j H) : hom_scope.

(** Passing from a boundary to a horn retains each permitted face. *)

(** 从边界转到 horn 保留每个容许的面。 *)

Lemma boundary_horn_face@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (i j : Ordinal (S n)) (H : ¬ j = i)
    (b : BoundaryS X (S n))
  : face[i; j; H] (boundary_horn_resp (S n) i b) ≈S face∂[j] b.
Proof.
  apply (@func_proper _ _ (b n)).
  exact {|lower := reflexivity δ[n; j]
         |}.
Defined.

(** Different retained-face proofs give equal values, without equating the
    proofs. They represent the same underlying coface in the sieve. *)

(** 不同保留面证明给出相等的值，无需等同证明；它们在筛中表示同一底层余面。 *)

Lemma horn_face_witness_independent@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} {i j : Ordinal (S n)} (H K : ¬ j = i)
    (h : HornS X (S n) i)
  : face[i; j; H] h ≈S face[i; j; K] h.
Proof.
  apply (@func_proper _ _ (h n)).
  exact {|lower := reflexivity δ[n; j]
         |}.
Defined.

(** Naturality and equality of common factors give every face overlap. *)

(** 自然性及共同因子相等给出全部面交叠。 *)

Definition horn_face_overlap@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} {i j k : Ordinal (S n)} (Hj : ¬ j = i) (Hk : ¬ k = i)
    (h : HornS X (S n) i) {m : nat}
    (f g : (@Hom Δ) m n) (E : δ[n; j] ∘ f ≈ δ[n; k] ∘ g)
  : X[f]Δ (face[i; j; Hj] h) ≈S X[g]Δ (face[i; k; Hk] h)
  := @matching_overlap Δ (S n) (∃ j : Ordinal (S n), ¬ j = i)
      (λ _, n) (λ j, δ[n; j.1]) X
      (@SieveMatchingOfN Δ (S n) (∃ j : Ordinal (S n), ¬ j = i)
        (λ _, n) (λ j, δ[n; j.1]) X h) m (j; Hj) (k; Hk) f g E.

(** A simplex fills an actual horn exactly when each retained face is the
    corresponding extracted value. All degrees follow from the generators. *)

(** 单形填充实际 horn，当且仅当其每个保留面等于相应提取值；全部维度由生成元
    判等导出。 *)

Definition horn_filler_faces_iff@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} {i : Ordinal (S n)} (h : HornS X (S n) i) (x : X (S n))
  : is_horn_filler h x ↔
      ∀ j (H : ¬ j = i), d[X; n; j] x ≈S face[i; j; H] h.
Proof.
  split.
  - intros H j E. exact (H n {|lower := (δ[n; j]; horn_face_member i j E)
                             |}).
  - intros H. apply (snd (@generated_sieve_map_eq Δ (S n)
      (∃ j : Ordinal (S n), ¬ j = i) (λ _, n) (λ j, δ[n; j.1]) X _ _)).
    intros [j E]. exact (H j E).
Defined.

(** The general matching isomorphism gives the complete two-way horn-map
    correspondence, with only ordinary lifts to common universes. *)

(** 一般匹配同构给出完整的双向 horn 映射对应，仅使用进入共同宇宙的通常提升。 *)

Definition horn_matching_iso@{u p v q +}
    {X : Functor (Δ^op) SetCat@{v q _ _ _ _ _}}
    (n : nat) (i : Ordinal (S n))
  : LiftS@{_ _ u p} (HornMatchingS X n i) ≅[SetCat]
      LiftS@{_ _ u p} (HornS X (S n) i)
  := @sieve_matching_iso Δ (S n) (∃ j : Ordinal (S n), ¬ j = i)
      (λ _, n) (λ j, δ[n; j.1]) X.
