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

(** ** Reading a Triangle and a Repeated Vertex

    Return to %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict}
    {%[simplex_restrict]%}%: selecting a face of the shape reads a face
    of the data. For an edge e with ordered vertices zero and one, [d[X; 0]]
    reads the endpoint at position one, whereas [d[X; 1]] reads position
    zero. The index says which position to omit, not which one to keep.

    For a triangle t, [d[X; 0]] reads edge 12, [d[X; 1]] edge 02, and
    [d[X; 2]] edge 01. In the picture, t denotes the entire two-dimensional
    datum. Its edges may coincide in a particular X; drawing distinct
    vertices is only a way to keep track of the positions. *)

(** ** 读出三角形的面与重复顶点

    回到 %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict}
    {%[simplex_restrict]%}%：选取形状的一个面，就读出数据的一个面。
    对顶点按零、一排序的边 e，[d[X; 0]] 读出位置一的端点，
    [d[X; 1]] 读出位置零的端点。索引说的是省略哪个位置，而非保留哪个位置。

    对三角形 t，[d[X; 0]] 读出边 12，[d[X; 1]] 读出边 02，
    [d[X; 2]] 读出边 01。图中的 t 表示整份二维数据。在具体的 X 中，
    这些边可能重合；将顶点画开只是为了辨认位置。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& 1 \arrow[dr,"{d_0t}"] & \\
0 \arrow[ur,"{d_2t}"] \arrow[rr,"{d_1t}"'] && 2
\end{tikzcd}
\end{center}%
*)

(** A degeneracy goes the other way in degree. For a vertex v, [s[X; 0]]
    produces an edge whose two endpoints are both v. It does not assert
    that every edge with equal endpoints is degenerate: a nerve can also
    contain nonidentity loops. The two cancellation laws
    %\coqref{Cats.Instance.Set.Simplicial.Operators.simplex face degeneracy id}
    {%[simplex_face_degeneracy_id]%}% and %\coqref{Cats.Instance.Set.Simplicial.Operators.simplex face degeneracy next}
    {%[simplex_face_degeneracy_next]%}% express
    that either endpoint of this degenerate edge recovers v.

    The remaining identities compare two routes to the same face or repeated
    position. The shifted indices track the renumbering after an omission
    or repetition. They all follow from the shape equations, through
    %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict comp}
    {%[simplex_restrict_comp]%}%, rather than independent axioms about X. *)

(** 退化在维数上沿相反方向行进。对顶点 v，[s[X; 0]] 产生两个端点都为 v
    的边。这并不表示每条端点相同的边都退化：nerve 中也可能有非恒等的环。
    两条消去律 %\coqref{Cats.Instance.Set.Simplicial.Operators.simplex face degeneracy id}
    {%[simplex_face_degeneracy_id]%}% 与
    %\coqref{Cats.Instance.Set.Simplicial.Operators.simplex face degeneracy next}
    {%[simplex_face_degeneracy_next]%}% 表示，取这条退化边的任一端点都会恢复 v。

    其余恒等式比较通向同一个面或重复位置的两条路径；索引的移位记录省略或
    重复之后的重新编号。它们都由形状方程经 %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict comp}
    {%[simplex_restrict_comp]%}% 得到，
    无须另行给 X 添加公理。 *)

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
