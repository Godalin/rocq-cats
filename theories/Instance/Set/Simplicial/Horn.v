From Cats Require Export
  Instance.Set.Simplicial.Boundary.

Local Open Scope nat_scope.

(** * Horn Maps and Fillers

    A horn datum is a map from an actual horn subpresheaf. All overlap and
    restriction compatibility is included in that natural transformation.
    Fillers are simplices with a specified equality of their horn maps. *)

(** * horn 映射与填充

    horn 数据是从实际 horn 子预层出发的映射，其自然变换已包含全部交叠及限制
    相容性。填充是单形，且其 horn 映射与给定映射按指定相等比较。 *)

(** Boundary maps form the matching setoid, with pointwise equality. Its
    size may exceed the value sizes; no resizing of this setoid is imposed. *)

(** 边界映射按逐点相等组成匹配广集；其大小可以超过值大小，不要求大小重设。 *)

Definition BoundaryS@{u p +}
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat)
  : SetC
  := Nat_SetS ∂Δ[n] X.

(** Horn maps form the corresponding partial matching setoid. *)

(** horn 映射组成相应的部分匹配广集。 *)

Definition HornS@{u p +}
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat) (i : Ordinal n)
  : SetC
  := Nat_SetS Λ[n; i] X.

(** Restrict a simplex to its whole boundary using the general sieve map. *)

(** 使用一般筛映射，将单形限制到整个边界。 *)

Definition boundary_restrict_resp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} (n : nat)
  : X n →r BoundaryS X n
  := sieve_restrict_resp (BoundarySieve n).

Notation "x '↾∂[' X ';' n ']'" := (@boundary_restrict_resp X n x)
  (at level 8, left associativity, format "x ↾∂[ X ;  n ]") : hom_scope.

(** Restrict a simplex to a selected horn by the same construction. *)

(** 使用同一构造，将单形限制到选定 horn。 *)

Definition horn_restrict_resp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} (i : Ordinal n)
  : X n →r HornS X n i
  := sieve_restrict_resp (HornSieve n i).

Notation "x '↾Λ[' X ';' n ';' i ']'" := (@horn_restrict_resp X n i x)
  (at level 8, left associativity, format "x ↾Λ[ X ;  n ;  i ]") : hom_scope.

(** A filler is an n-simplex whose entire restricted map is the given horn.
    There is no comparison of naturality proofs. *)

(** 填充是整个限制映射等于给定 horn 的 n-单形；不比较自然性证明。 *)

Definition is_horn_filler@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} {i : Ordinal n}
    (h : HornS X n i) (x : X n)
  : Type
  := x↾Λ[X; n; i] ≈S h.

(** Chosen filling at dimension n retains the filler and its equation.
    No uniqueness is assumed. At dimension zero this selects a vertex;
    the Kan filling structure below quantifies only positive dimensions. *)

(** n 维选定填充保留填充及其方程，不预先要求唯一性。零维时这要求选取顶点；
    后续 Kan 填充结构只量化正维度。 *)

Class HasHornFillers@{u p +}
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
    (n : nat) (i : Ordinal n)
  :=
  { horn_fill (h : HornS X n i)
    : ∃ x : X n, is_horn_filler h x
  }.

(** Chosen Kan filling supplies every positive-dimensional horn filler.
    These are retained choices, not mere existence. The choices need not
    be respectful or functorial, and no choice axiom is used. *)

(** 选定 Kan 填充提供全部正维 horn 的填充。这是保留的选择数据，不仅是存在性；
    不要求选择保持相等或具有函子性，也不使用选择公理。 *)

Class HasKanFillers@{u p +}
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
  :=
  { hasHornFillers (n : nat) (i : Ordinal (S n))
    :: HasHornFillers X (S n) i
  }.

(** Extending a horn map to the standard simplex is equivalent to giving
    a filler simplex. The general sieve extension theorem supplies both maps. *)

(** 将 horn 映射延拓到标准单形，等价于给出填充单形；一般筛延拓定理提供双向
    转换。 *)

Definition horn_extension_iff@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} {i : Ordinal n} (h : HornS X n i)
  : (∃ α : Δ[n] ⇒ X, (α ∘Nv ιΛ[n; i]) ≈N h) ↔
      (∃ x : X n, is_horn_filler h x)
  := sieve_extension_iff (HornSieve n i) h.

(** Restricting a boundary map to a horn forgets its excluded face. *)

(** 将边界映射限制到 horn，忘却其排除的面。 *)

Program Definition boundary_horn_resp@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} (n : nat) (i : Ordinal n)
  : BoundaryS X n →r HornS X n i
  :=
  {|func h := h ∘Nv HornBoundaryN n i
  |}.
Next Obligation. intros h k H m a. exact (H m (HornBoundaryN n i m a)). Defined.

(** Restriction to the boundary and then to a horn is direct restriction. *)

(** 先限制到边界再到 horn，等于直接限制到 horn。 *)

Lemma boundary_horn_restrict@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (i : Ordinal n) (x : X n)
  : boundary_horn_resp n i (x↾∂[X; n]) ≈S x↾Λ[X; n; i].
Proof. intros m a. reflexivity. Defined.

(** Evaluating a restricted horn map on a retained generic face recovers
    exactly that face of the original simplex. *)

(** 在保留面的泛单形处求值限制后的 horn 映射，恰好恢复原单形的相应面。 *)

Lemma horn_restrict_face@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (i j : Ordinal (S n)) (H : ¬ j = i) (x : X (S n))
  : simplex_element_resp
      (x↾Λ[X; S n; i] ∘Nv HornFaceN i j H) ≈S d[X; n; j] x.
Proof.
  change (X[δ[n; j] ∘ id]Δ x ≈S X[δ[n; j]]Δ x).
  exact (simplex_restrict_proper _ _ (comp_id_r δ[n; j]) x).
Defined.

(** The same computation recovers every face from the boundary map. *)

(** 同一计算从边界映射恢复每个面。 *)

Lemma boundary_restrict_face@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} (j : Ordinal (S n)) (x : X (S n))
  : simplex_element_resp
      (x↾∂[X; S n] ∘Nv BoundaryFaceN j) ≈S d[X; n; j] x.
Proof.
  change (X[δ[n; j] ∘ id]Δ x ≈S X[δ[n; j]]Δ x).
  exact (simplex_restrict_proper _ _ (comp_id_r δ[n; j]) x).
Defined.
