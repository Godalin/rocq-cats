From Cats Require Export
  Instance.Set.Simplicial.Standard
  Instance.Set.Functor.
From Cats Require Import
  Cat.CatCat
  Cat.Diagram.Core
  Cat.Groupoid.Functor.

Local Open Scope nat_scope.

(** * The Diagram Nerve with Natural-Isomorphism Equality

    An n-simplex is a functor from the finite ordinal [Ord n] to C.
    Its specified equality is natural isomorphism. Explicit lifts place
    native functor data and comparison witnesses in the chosen value sizes;
    [lower] recovers the underlying functor. Write [N≅(C)] for this diagram
    nerve and [N≅[F]] for the map induced by a functor. The groupoid boundary
    below records the effect of this equality on distinctions between paths. *)

(** * 按自然同构比较的图式 nerve

    n-单形是从有限序数 [Ord n] 到 C 的函子，指定相等为自然同构。显式提升将
    原生函子数据及比较见证放到所选值大小中；[lower] 取出底层函子。记此图式
    nerve 为 [N≅(C)]，函子诱导的映射为 [N≅[F]]；下方的群胚边界刻画此相等
    对路径区别的影响。 *)

(** ** A Category Seen through Ordered Chains

    The preceding %\coqref{Cats.Instance.Set.Simplicial.Standard.StandardSimplex}
    {%[StandardSimplex]%}% lists monotone maps between shapes.
    A nerve instead lists diagrams of each shape inside a chosen category C:
    - In degree zero, a diagram selects one object.
    - In degree one, it selects an arrow [f : A → B].
    - In degree two, it selects composable arrows [f : A → B] and
      [g : B → D], together with the long edge, equal to [g ∘ f].

    Taking the middle face of that triangle composes its two consecutive
    arrows. Taking either outer face retains one of them. Repeating a vertex
    inserts an identity arrow. These operations assemble into a simplicial
    object because diagrams are functors, so they already preserve identities
    and composition. A triangle in a general simplicial set need not have
    this categorical interpretation. *)

(** ** 用有序箭头链观察范畴

    前面的 %\coqref{Cats.Instance.Set.Simplicial.Standard.StandardSimplex}
    {%[StandardSimplex]%}% 收集形状之间的保序映射。nerve 则在给定范畴 C
    内收集每种形状的图式：
    - 零维图式选取一个对象。
    - 一维图式选取一条箭头 [f : A → B]。
    - 二维图式选取可复合的 [f : A → B]、[g : B → D]，以及等于
      [g ∘ f] 的长边。

    取这个三角形的中间面，就是将两条相邻箭头复合；取两侧的面则分别保留其中
    一条箭头。重复顶点会插入恒等箭头。这些操作组成单纯对象，因为图式本来就是
    保持恒等与复合的函子。一般单纯集合中的三角形不必具有这样的范畴解释。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& B \arrow[dr,"{g}"] & \\
A \arrow[ur,"{f}"] \arrow[rr,"{h \approx g\circ f}"'] && D
\end{tikzcd}
\end{center}%
*)

(** ** Which Equality Does the Nerve Remember?

    %\coqref{Cats.Instance.Set.Simplicial.Nerve.DiagramNerve}
    {%[DiagramNerve]%}% compares diagrams by arbitrary natural isomorphisms.
    Consequently its vertices compare as isomorphic objects of C. In a
    groupoid, this comparison can also identify paths that one might have
    wanted to keep distinct; see the groupoid analysis later in this module.

    The later %\coqref{Cats.Instance.Set.Simplicial.Vertex.Core.VertexNerve}
    {%[VertexNerve]%}% uses
    an additional label setoid and prescribed coherent transports. Its
    vertices compare using that specified label equality. Both constructions
    use the same chain picture, but they answer different equality questions.
    Read the vertex and edge descriptions before reconstruction: they state
    precisely what information that second nerve retains. *)

(** ** nerve 记住哪一种相等？

    %\coqref{Cats.Instance.Set.Simplicial.Nerve.DiagramNerve}
    {%[DiagramNerve]%}% 允许用任意自然同构比较图式，因此它的顶点按 C 中的对象同构
    比较。在群胚里，这种比较还可能识别原本想区分的路径；本章后面的群胚分析
    会具体说明这一点。

    后面的 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Core.VertexNerve}
    {%[VertexNerve]%}% 另外使用
    标签广集及指定的相干运输，顶点按指定的标签相等比较。两种构造使用同样的
    箭头链图像，却回答不同的相等问题。阅读重构定理前，先看顶点与边的描述，
    就能明确第二种 nerve 究竟保留了哪些信息。 *)

Definition DiagramNerve@{u p +} (C : Cat)
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := FctPsh SimplexInclusionF C.

Notation "'N≅(' C ')'" := (DiagramNerve C) : ob_scope.

(** Postcomposition with a functor induces a map of nerves. *)

(** 与函子后复合诱导 nerve 之间的映射。 *)

Definition DiagramNerveN@{u p +} {C D : Cat} (F : Fct C D)
  : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ N≅(D)
  := FctPshN SimplexInclusionF F.

Notation "'N≅[' F ']'" := (DiagramNerveN F) : cat_scope.

(** The nerve is functorial in categories with natural-isomorphism equality.
    All laws are inherited from the general probe-presheaf construction. *)

(** nerve 在以自然同构比较函子的范畴之范畴上构成函子；全部定律继承一般探测
    预层构造。 *)

Definition DiagramNerveF@{u p +}
  : Fct CatCat (FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
  := FctPshF SimplexInclusionF.

(** Embed a finite-ordinal diagram as a nerve simplex. *)

(** 将有限序数图式嵌入为 nerve 的单形。 *)

Definition NerveSimplex@{u p +} {C : Cat} {n : nat}
    (F : Fct [Ord n] C)
  : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n
  :=
  {|lower := F
  |}.

Notation "'⟨' F '⟩N'" := (NerveSimplex F) : hom_scope.

(** Naturally isomorphic diagrams represent equal nerve simplices. *)

(** 自然同构的图式表示相等的 nerve 单形。 *)

Global Instance nerve_simplex_proper@{u p +} {C : Cat} {n : nat}
  : Proper (NatIso ==>
      carrier_equiv ((N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n))
      (@NerveSimplex C n).
Proof. intros F G H. exact {|lower := H
                           |}. Defined.

(** Restriction is precomposition by the simplex operator. *)

(** 限制就是与单纯算子预复合。 *)

Lemma nerve_restrict@{u p +} {C : Cat} {m n : nat}
    (θ : (@Hom Δ) m n)
    (x : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : N≅(C)[θ]Δ x ≈S ⟨lower x ∘F θ⟩N.
Proof. reflexivity. Defined.

(** Faces omit the selected position in an ordinal diagram. *)

(** 面省略序数图式中选定的位置。 *)

Lemma nerve_face@{u p +} {C : Cat} {n : nat}
    (i : Ordinal (S n))
    (x : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (S n))
  : d[N≅(C); n; i] x ≈S ⟨lower x ∘F δ[n; i]⟩N.
Proof. apply nerve_restrict. Defined.

(** Degeneracies repeat the selected position in an ordinal diagram. *)

(** 退化重复序数图式中选定的位置。 *)

Lemma nerve_degeneracy@{u p +} {C : Cat} {n : nat}
    (i : Ordinal n)
    (x : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : s[N≅(C); n; i] x ≈S ⟨lower x ∘F σ[n; i]⟩N.
Proof. apply nerve_restrict. Defined.

(** A nerve map acts on a simplex by postcomposition. *)

(** nerve 映射通过后复合作用于单形。 *)

Lemma nerve_map@{u p +} {C D : Cat} (F : Fct C D) {n : nat}
    (x : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : N≅[F] n x ≈S ⟨F ∘F lower x⟩N.
Proof. reflexivity. Defined.

(** Category equivalences induce natural isomorphisms of nerves, using the
    same quasi-inverse data through functoriality. *)

(** 范畴等价诱导 nerve 的自然同构，通过函子性使用同一组拟逆数据。 *)

Definition nerve_equiv_iso@{u p +} {C D : Cat} (e : C ≃C D)
  : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N N≅(D).
Proof.
  exists N≅[e.1]. apply is_iso_NatIso.
  exact (functor_is_iso DiagramNerveF e.1 e.2).
Defined.

(** * Standard Simplices Are Nerves of Finite Ordinals *)

(** * 标准单形是有限序数的 nerve *)

(** Both sides have the same diagrams and precomposition action. Compare
    them by identity maps without equating their functor-law fields. *)

(** 两侧具有相同的图式及预复合作用；用恒等映射比较，不等同函子定律字段。 *)

Program Definition standard_nerve_iso@{u p +} (n : nat)
  : (Δ[n] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N N≅([Ord n])
  := ({|nt m := id_resp
      |}; _).
Next Obligation. intros [F]. reflexivity. Defined.
Next Obligation.
  intros m. exists id_resp. split; intros [F]; reflexivity.
Defined.

(** The standard-simplex comparison is natural in the ordinal dimension. *)

(** 标准单形的比较在序数维数上自然。 *)

Program Definition StandardNerveN@{u p +}
  : (StandardSimplexF : Fct Δ (FctCat (Δ^op) SetCat@{u p _ _ _ _ _})) ⇒
      (DiagramNerveF ∘F SimplexInclusionF)
  :=
  {|nt n := (standard_nerve_iso n).1
  |}.
Next Obligation. intros m [F]. reflexivity. Defined.

(** The standard-simplex embedding factors through ordinal interpretation
    followed by the nerve, up to a natural isomorphism. *)

(** 标准单形嵌入在自然同构下分解为序数解释后接 nerve。 *)

Definition standard_nerve_nat_iso@{u p +}
  : (StandardSimplexF : Fct Δ (FctCat (Δ^op) SetCat@{u p _ _ _ _ _})) ≅N
      (DiagramNerveF ∘F SimplexInclusionF).
Proof.
  exists StandardNerveN. intros n.
  exact (NatIso_is_iso (standard_nerve_iso n).1 (standard_nerve_iso n).2).
Defined.

(** * Equality Boundary for Groupoids

    Natural-isomorphism equality does not retain distinctions between all
    diagrams. In a groupoid, two n-simplices are equal precisely when their
    first vertices are isomorphic. In particular, for a one-object groupoid
    every two n-simplices are equal in this setoid-valued nerve. *)

(** * 群胚上的相等边界

    自然同构相等不保留所有图式之间的区别。群胚中，两个 n-单形相等当且仅当
    其首顶点同构；特别地，单对象群胚的任意两个 n-单形在此广集值 nerve 中相等。 *)

Lemma nerve_groupoid_eq_iff@{u p +} {C : Cat} `{HC : !IsGroupoid C}
    {n : nat}
    (x y : (N≅(C) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : x ≈S y ↔ lower x fin_first ≅[C] lower y fin_first.
Proof.
  split.
  - intros [[α Hα]]. exact (α fin_first; Hα fin_first).
  - intros e. refine {|lower := _
                      |}.
    transitivity (ConstF [Ord n] (lower x fin_first)).
    + symmetry. exact (groupoid_initial_diagram_iso
        (ordinal_first_initial n) (lower x)).
    + transitivity (ConstF [Ord n] (lower y fin_first)).
      * exists (fmap (DiagF [Ord n] C) e.1).
        apply is_iso_NatIso.
        exact (functor_is_iso (DiagF [Ord n] C) e.1 e.2).
      * exact (groupoid_initial_diagram_iso
          (ordinal_first_initial n) (lower y)).
Defined.
