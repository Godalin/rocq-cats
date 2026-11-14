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

(** ** One Generator, All Its Faces and Degeneracies

    [Δ[n]] is a whole simplicial set, not a single element in degree n.
    Its k-simplices are monotone maps from the k-dimensional ordered shape
    to the n-dimensional shape, with the explicit universe lift used below.
    Restriction is precomposition, so it automatically keeps track of every
    face and every repetition.

    Take [Δ[1]]. It has two vertices, zero and one. Its edges are the three
    monotone lists [00], [01] and [11]. The middle one is the generating edge;
    the other two repeat one vertex and are degenerate. In degree two its
    lists are [000], [001], [011] and [111], all degenerate. High-dimensional
    data are present even though the drawing looks like one interval.

    In [Δ[2]], the list [012] is the generating triangle. Its three faces
    are [12], [02] and [01], in the order computed by %\coqref{Cats.Instance.Set.Simplicial.Operators.simplex face}
    {%[simplex_face]%}%. The
    six edges also include [00], [11] and [22]. Thus the word ``standard''
    includes the faces and degeneracies around the generator, not an
    additional requirement that arbitrary triangles of X behave like it. *)

(** ** 一个生成单形及其全部面与退化

    [Δ[n]] 是整个单纯集合，不是 n 维中的一个元素。它的 k-单形是从 k 维有序
    形状到 n 维有序形状的保序映射，并带上下文所需的显式宇宙提升。限制就是
    预合成，因此会自动记录每个面与每次重复。

    看 [Δ[1]]：它有零、一两个顶点，边是三个保序列表 [00]、[01] 和 [11]。
    中间一条是生成边，另两条各自重复一个顶点，属于退化边。二维的列表是
    [000]、[001]、[011]、[111]，全都退化。因此，尽管图画像一条区间，
    它仍有高维数据。

    在 [Δ[2]] 中，[012] 是生成三角形，三个面按 %\coqref{Cats.Instance.Set.Simplicial.Operators.simplex face}
    {%[simplex_face]%}% 计算的次序
    分别为 [12]、[02]、[01]。它的六条边还包括 [00]、[11]、[22]。
    所以，“标准单形”包括生成单形周围的面与退化，并不额外要求 X 中任意
    三角形都具有相同的整体结构。 *)

(** ** Why Maps from a Standard Simplex Encode Elements

    An element x of [X n] determines where the generating n-simplex goes.
    Commutation with restriction then determines the image of every simplex
    of [Δ[n]]: a shape operator [θ] is sent to [X[θ]Δ x]. This is
    %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex map resp}
    {%[simplex_map_resp]%}%. Conversely, %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element resp}
    {%[simplex_element_resp]%}% evaluates a map
    on %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex generic}
    {%[simplex_generic]%}%, the identity shape operator.

    The laws %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element xCExB2}
    {%[simplex_element_β]%}% and %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element xCExB7}
    {%[simplex_element_η]%}% say that these
    operations undo each other in specified equality. This is the concrete
    content of Yoneda here; a first reading can start with these computations
    before the general proof. Later, %\coqref{Cats.Instance.Set.Simplicial.Boundary.Boundary}
    {%[Boundary]%}% and %\coqref{Cats.Instance.Set.Simplicial.Boundary.Horn}
    {%[Horn]%}% keep only selected
    parts of this standard domain, so extending their maps becomes a precise
    way to ask for a filler. *)

(** ** 为什么从标准单形出发的映射表示元素

    [X n] 中的元素 x 指定生成 n-单形的去向。与限制交换的要求随后确定
    [Δ[n]] 中每个单形的像：形状算子 [θ] 被送到 [X[θ]Δ x]。
    这就是 %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex map resp}
    {%[simplex_map_resp]%}%。反过来，%\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element resp}
    {%[simplex_element_resp]%}% 将映射在
    %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex generic}
    {%[simplex_generic]%}% 处求值；后者就是恒等形状算子。

    %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element xCExB2}
    {%[simplex_element_β]%}% 和 %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element xCExB7}
    {%[simplex_element_η]%}% 表明这两种操作在指定相等下
    互逆。这是此处 Yoneda 对应的具体内容；初读可以先看这些计算，再读一般
    证明。后面的 %\coqref{Cats.Instance.Set.Simplicial.Boundary.Boundary}
    {%[Boundary]%}% 与 %\coqref{Cats.Instance.Set.Simplicial.Boundary.Horn}
    {%[Horn]%}% 只保留这个标准定义域的部分数据，
    因而“延拓它们的映射”将成为询问填充是否存在的精确定义。 *)

Definition StandardSimplex@{u p +} (n : nat)
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := RaisedEmbedding (C := Δ) n.

Notation "'Δ[' n ']'" := (StandardSimplex n) : ob_scope.

(** The standard-simplex embedding inherits all functor laws from raised
    Yoneda, including its action by postcomposition. *)

(** 标准单形嵌入继承提升的 Yoneda 的全部函子律，其箭头作用是后合成。 *)

Definition StandardSimplexF@{u p +}
  : Fct Δ (FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
  := RaisedEmbedding (C := Δ).

(** The simplex category is fully faithfully embedded among simplicial sets. *)

(** 单纯范畴全忠实地嵌入单纯集合中。 *)

Theorem standard_simplex_fully_faithful@{u p +}
  : is_fully_faithful
      (StandardSimplexF : Fct Δ (FctCat (Δ^op) SetCat@{u p _ _ _ _ _})).
Proof. apply raised_embedding_fully_faithful. Defined.

(** The generic n-simplex is the lifted identity of [n]. *)

(** 泛 n-单形是 [n] 的提升恒等。 *)

Definition simplex_generic@{u p +} (n : nat)
  : (Δ[n] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n
  :=
  {|lower := (id : (@Hom Δ) n n)
  |}.

(** Every n-simplex of X determines a unique map from the standard n-simplex.
    Both directions are respectful and retain their computation. *)

(** X 的每个 n-单形唯一确定从标准 n-单形出发的映射；双向均保持相等和计算。 *)

Definition simplex_element_resp@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
  : Nat_SetS Δ[n] X →r X n
  := presheaf_yoneda_resp (C := Δ) (P := X) (X := n).

(** Reconstruct a map from a simplex by restriction along each simplex
    operator. *)

(** 沿各单纯算子限制一个单形，重构由它确定的映射。 *)

Definition simplex_map_resp@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
  : X n →r Nat_SetS Δ[n] X
  := presheaf_yoneda_inv_resp (C := Δ) (P := X) (X := n).

Notation "'⟦' x '⟧Δ[' X ';' n ']'" := (@simplex_map_resp X n x)
  : hom_scope.

(** Evaluation of a reconstructed map recovers the chosen simplex. *)

(** 求值重构的映射恢复所选单形。 *)

Lemma simplex_element_β@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} (x : X n)
  : simplex_element_resp ⟦x⟧Δ[X; n] ≈S x.
Proof. apply presheaf_yoneda_β. Qed.

(** Reconstruction of the generic image recovers a simplicial map. *)

(** 从泛单形的像重构恢复原单纯映射。 *)

Lemma simplex_element_η@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} (α : Δ[n] ⇒ X)
  : ⟦simplex_element_resp α⟧Δ[X; n] ≈N α.
Proof. apply presheaf_yoneda_η. Qed.

(** Maps from the standard n-simplex correspond to n-simplices as setoids.
    Lift both sides only to package their different native sizes together. *)

(** 从标准 n-单形出发的映射与 n-单形构成广集同构；仅为统一包装不同的原生大小
    而提升两侧。 *)

Definition simplex_element_iso@{u p v q +}
    {X : Fct (Δ^op) SetCat@{v q _ _ _ _ _}} (n : nat)
  : LiftS@{_ _ u p} (Nat_SetS Δ[n] X) ≅[SetCat]
      LiftS@{_ _ u p} (X n)
  := presheaf_yoneda_iso (C := Δ) (P := X) (X := n).

(** Maps out of a standard simplex agree exactly when their generic images
    agree. *)

(** 从标准单形出发的映射相等，当且仅当其泛单形的像相等。 *)

Lemma simplex_map_unique@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat} (α β : Δ[n] ⇒ X)
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
    {X Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (α : X ⇒ Y) (β : Δ[n] ⇒ X)
  : simplex_element_resp (α ∘Nv β) ≈S α n (simplex_element_resp β).
Proof. apply presheaf_yoneda_natural_presheaf. Qed.

(** In the following triangle, [α : Δ[n] ⇒ X] represents an n-simplex
    x, its image of %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex generic}
    {%[simplex_generic]%}%. The diagonal is the map represented
    by [X[θ]Δ x]. The two routes agree as natural transformations by
    %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element restrict}
    {%[simplex_element_restrict]%}% and %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element xCExB7}
    {%[simplex_element_η]%}%. This connects the
    earlier restriction operation directly to maps between standard domains. *)

(** 在下图中，[α : Δ[n] ⇒ X] 表示一个 n-单形 x，即 %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex generic}
    {%[simplex_generic]%}%
    的像。斜箭头是 [X[θ]Δ x] 所表示的映射。由 %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element restrict}
    {%[simplex_element_restrict]%}%
    和 %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex element xCExB7}
    {%[simplex_element_η]%}%，两条路径作为自然变换相等。它把前面的限制操作
    与标准定义域之间的映射直接联系起来。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
\Delta[m] \arrow[r,"{\Delta[\theta]}"]
  \arrow[dr,"{\langle X[\theta]x\rangle}"'] &
\Delta[n] \arrow[d,"{\alpha=\langle x\rangle}"] \\
& X
\end{tikzcd}
\end{center}%
*)

(** Precomposing with a map of standard simplices corresponds to restriction
    of its generic image, including all faces and degeneracies. *)

(** 与标准单形之间的映射预合成，对应于限制泛单形的像；特别包含全部面和退化。 *)

Lemma simplex_element_restrict@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {m n : nat}
    (θ : (@Hom Δ) m n) (α : Δ[n] ⇒ X)
  : simplex_element_resp (α ∘Nv fmap StandardSimplexF θ) ≈S
      X[θ]Δ (simplex_element_resp α).
Proof.
  exact (presheaf_yoneda_natural_object (C := Δ) (P := X) θ α).
Qed.
