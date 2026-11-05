From Cats Require Export
  Instance.Set.Simplicial.Horn
  Instance.Set.Sieve.Matching.

Local Open Scope nat_scope.

(** * Compatible Faces of a Horn

    The generated-sieve matching correspondence specializes uniformly to
    horns. Face indices and overlap factorizations remain explicit data. *)

(** * horn 的相容面

    生成筛的匹配对应统一特化到 horn；面索引及交叠分解均保留为显式数据。 *)

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
