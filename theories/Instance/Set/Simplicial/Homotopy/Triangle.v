From Cats Require Export
  Instance.Set.Simplicial.Homotopy.Core.
From Cats Require Import
  Instance.Set.Product
  Cat.Functor.FiniteProducts
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Reading Homotopies from a Supplied Parameter Triangle

    A map [A × Δ[2] ⇒ X] has three directed edge restrictions. Its edge
    01, then edge 12, has edge 02 as a possible composite. If edge 02 is
    constant instead, edge 12 reverses edge 01. Both statements require
    the actual triangle map and the indicated edge equations. They do
    not construct a triangle extension from two arbitrary homotopies.

    This is the restriction half of the Kan extension argument. No Kan
    choice is selected here, and the directed homotopy relation is not
    registered as an equivalence. The relative statements keep the whole
    prescribed subdomain fixed in every degree and time simplex. *)

(** * 从给定参数三角形读取同伦

    映射 [A × Δ[2] ⇒ X] 有三条有向边限制。先走边 01，再走边 12，边 02
    给出一种复合。若边 02 为常值，边 12 则反向于边 01。两种陈述都要求实际
    三角映射及所示边方程，不从任意两个同伦构造三角延拓。

    这是 Kan 延拓论证的限制部分；此处不选择 Kan 填充，不将有向同伦注册为
    等价关系。相对陈述在每一维及每个时间单形上固定整个给定子域。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& 1 \arrow[dr,"{12}" ] & \\
0 \arrow[ur,"{01}"] \arrow[rr,"{02}"'] && 2
\end{tikzcd}
\qquad
\begin{tikzcd}[column sep=large,row sep=large]
& g \arrow[dr,dashed,"{\mathrm{reverse}}" ] & \\
f \arrow[ur,"H"] \arrow[rr,"{\mathrm{constant}}"'] && f
\end{tikzcd}
\end{center}%
*)

(** ** Parameters and Their Shape Restrictions

    Fix independent value carrier/equality sizes and a source A. Use the
    existing chosen pointwise product explicitly; no model instance is
    exported. Shape maps change only the parameter coordinate. *)

(** ** 参数及其形状限制

    固定独立取值载体／相等大小及源 A，显式使用已有选定点态积，不导出模型实例。
    形状映射只改变参数坐标。 *)

Section Parameters.
Universes u p.
Context (A : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

(** The parameter object is an actual product presheaf. *)

(** 参数对象是实际的积预层。 *)

Definition SimplicialParameterF (m : nat)
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := PointwiseProductF A (Δ[m]).

(** Postcompose the parameter shape, retaining the source coordinate. *)

(** 后合成参数形状，保留源坐标。 *)

Definition SimplicialParameterMapN {m n : nat} (θ : (@Hom Δ) m n)
  : SimplicialParameterF m ⇒ SimplicialParameterF n
  := PointwisePairN (Δ^op) SetCat (PointwiseFstN (Δ^op) SetCat A (Δ[m]))
      (fmap StandardSimplexF θ ∘Nv PointwiseSndN (Δ^op) SetCat A (Δ[m])).

(** Hold the parameter at a chosen vertex in every degree. *)

(** 在每一维将参数固定于给定顶点。 *)

Program Definition SimplicialParameterPointN {m : nat} (j : Ordinal m)
  : A ⇒ SimplicialParameterF m
  :=
  {|nt n :=
      {|func a := (a, {|lower := ConstF [Ord n] (C := [Ord m]) j|})
      |}
  |}.
Next Obligation.
  intros a a' E. split; [exact E |]. refine {|lower := _|}. reflexivity.
Defined.
Next Obligation.
  intros a. split; [reflexivity |]. refine {|lower := _|}.
  apply (snd (simplex_eq_iff _ _)). intros j0. reflexivity.
Defined.

(** Endpoint restriction of a shape-parameter map uses its actual image
    vertex, without requiring equality of naturality proof fields. *)

(** 形状参数映射在端点处的限制使用实际像顶点，不要求自然性证明字段相等。 *)

Lemma simplicial_parameter_endpoint {m : nat} (θ : (@Hom Δ) 1%nat m)
    (t : bool)
  : (SimplicialParameterMapN θ ∘Nv SimplicialEndpointN A t) ≈N
      SimplicialParameterPointN (θ (simplex_interval_position t)).
Proof.
  intros n a. split; [reflexivity |]. refine {|lower := _|}.
  apply (snd (simplex_eq_iff _ _)). intros j. reflexivity.
Defined.

End Parameters.

(** ** Composites and Reverses from an Actual Extension

    Fix A and X at independent value sizes and supply a triangle map T.
    Its three edge maps are real cylinder maps. Boundary equations below
    compare them to supplied homotopies in specified natural equality. *)

(** ** 从实际延拓得到复合与反向

    固定取值大小独立的 A、X，并给定三角映射 T。三条边映射是实际柱映射；
    下方边界方程按指定自然相等将它们与给定同伦比较。 *)

Section TriangleEdges.
Universes u p.
Context {A X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (T : SimplicialParameterF A 2 ⇒ X).

(** Read the edge opposite vertex i: indices 2,0,1 give 01,12,02. *)

(** 读取顶点 i 的对边：索引 2、0、1 分别给出 01、12、02。 *)

Definition simplicial_triangle_edge (i : Ordinal 2)
  : SimplicialCylinderF A ⇒ X
  := T ∘Nv SimplicialParameterMapN A δ[1; i].

(** The endpoint is the corresponding vertex restriction of T. *)

(** 端点是 T 对应顶点处的限制。 *)

Lemma simplicial_triangle_edge_endpoint (i : Ordinal 2) (t : bool)
  : (simplicial_triangle_edge i ∘Nv SimplicialEndpointN A t) ≈N
      (T ∘Nv SimplicialParameterPointN A (m := 2)
        (δ[1; i] (simplex_interval_position t))).
Proof.
  intros n a. exact (@func_proper _ _ (T n) _ _
    (simplicial_parameter_endpoint A δ[1; i] t n a)).
Defined.

(** An actual triangle edge is a homotopy between its own vertex maps. *)

(** 实际三角边是其两个顶点映射之间的同伦。 *)

Program Definition SimplicialTriangleEdge (i : Ordinal 2)
  : SimplicialHomotopy
      (T ∘Nv SimplicialParameterPointN A (m := 2) (δ[1; i] fin_first))
      (T ∘Nv SimplicialParameterPointN A (m := 2) (δ[1; i] fin_first⁺))
  :=
  {|homotopy_map := simplicial_triangle_edge i
  |}.
Next Obligation.
  destruct b; apply simplicial_triangle_edge_endpoint.
Defined.

(** The missing long edge is a composite when edges 01 and 12 extend
    the supplied homotopies. Existence of T remains an explicit input. *)

(** 当边 01、12 延拓给定同伦时，缺少的长边为复合；T 的存在仍是显式输入。 *)

Program Definition SimplicialTriangleComposite {f g h : A ⇒ X}
    (H : SimplicialHomotopy f g) (K : SimplicialHomotopy g h)
    (E01 : simplicial_triangle_edge fin_first⁺⁺ ≈N homotopy_map H)
    (E12 : simplicial_triangle_edge fin_first ≈N homotopy_map K)
  : SimplicialHomotopy f h
  :=
  {|homotopy_map := simplicial_triangle_edge fin_first⁺
  |}.
Next Obligation.
  destruct b.
  - transitivity (T ∘Nv SimplicialParameterPointN A (fin_first⁺⁺ : Ordinal 2)).
    + exact (simplicial_triangle_edge_endpoint fin_first⁺ true).
    + transitivity (simplicial_triangle_edge fin_first ∘Nv
        SimplicialEndpointN A true).
      * symmetry. exact (simplicial_triangle_edge_endpoint fin_first true).
      * transitivity (homotopy_map K ∘Nv SimplicialEndpointN A true).
        -- intros n a. exact (E12 n (SimplicialEndpointN A true n a)).
        -- apply simplicial_homotopy_1.
  - transitivity (T ∘Nv SimplicialParameterPointN A (fin_first : Ordinal 2)).
    + exact (simplicial_triangle_edge_endpoint fin_first⁺ false).
    + transitivity (simplicial_triangle_edge fin_first⁺⁺ ∘Nv
        SimplicialEndpointN A false).
      * symmetry. exact (simplicial_triangle_edge_endpoint fin_first⁺⁺ false).
      * transitivity (homotopy_map H ∘Nv SimplicialEndpointN A false).
        -- intros n a. exact (E01 n (SimplicialEndpointN A false n a)).
        -- apply simplicial_homotopy_0.
Defined.

(** If 02 is the constant homotopy at f, the remaining edge 12 reverses
    the supplied edge 01. No simplicial time-reversal map is used. *)

(** 若边 02 是 f 处的常同伦，剩余边 12 反向于给定边 01；不使用单纯时间反转映射。 *)

Program Definition SimplicialTriangleReverse {f g : A ⇒ X}
    (H : SimplicialHomotopy f g)
    (E01 : simplicial_triangle_edge fin_first⁺⁺ ≈N homotopy_map H)
    (E02 : simplicial_triangle_edge fin_first⁺ ≈N
      homotopy_map (SimplicialConstantHomotopy f))
  : SimplicialHomotopy g f
  :=
  {|homotopy_map := simplicial_triangle_edge fin_first
  |}.
Next Obligation.
  destruct b.
  - transitivity (T ∘Nv SimplicialParameterPointN A (fin_first⁺⁺ : Ordinal 2)).
    + exact (simplicial_triangle_edge_endpoint fin_first true).
    + transitivity (simplicial_triangle_edge fin_first⁺ ∘Nv
        SimplicialEndpointN A true).
      * symmetry. exact (simplicial_triangle_edge_endpoint fin_first⁺ true).
      * transitivity (homotopy_map (SimplicialConstantHomotopy f) ∘Nv
          SimplicialEndpointN A true).
        -- intros n a. exact (E02 n (SimplicialEndpointN A true n a)).
        -- apply simplicial_homotopy_1.
  - transitivity (T ∘Nv SimplicialParameterPointN A (fin_first⁺ : Ordinal 2)).
    + exact (simplicial_triangle_edge_endpoint fin_first false).
    + transitivity (simplicial_triangle_edge fin_first⁺⁺ ∘Nv
        SimplicialEndpointN A true).
      * symmetry. exact (simplicial_triangle_edge_endpoint fin_first⁺⁺ true).
      * transitivity (homotopy_map H ∘Nv SimplicialEndpointN A true).
        -- intros n a. exact (E01 n (SimplicialEndpointN A true n a)).
        -- apply simplicial_homotopy_1.
Defined.

(** Specified equality of extensions compares their actual edge maps,
    independently of any endpoint or relative-law proof fields. *)

(** 延拓的指定相等比较实际边映射，与任何端点或相对定律证明字段无关。 *)

Lemma simplicial_triangle_edge_proper
    (T' : SimplicialParameterF A 2 ⇒ X) (E : T ≈N T') (i : Ordinal 2)
  : simplicial_triangle_edge i ≈N
      (T' ∘Nv SimplicialParameterMapN A δ[1; i]).
Proof.
  intros n z. exact (E n (SimplicialParameterMapN A δ[1; i] n z)).
Defined.

End TriangleEdges.

(** ** Keeping an Entire Subdomain Fixed

    Fix a map i from B to A and prescribed values c from B to X. Constancy
    in the parameter is imposed for every degree and every parameter
    simplex. Restriction preserves this law even when i is not injective. *)

(** ** 固定整个子域

    固定从 B 到 A 的映射 i 及从 B 到 X 的给定值 c。在每一维、每个参数单形上
    要求参数不变；即使 i 不单射，限制仍保持此定律。 *)

Section RelativeParameters.
Universes u p.
Context {A B X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (i : B ⇒ A) (c : B ⇒ X).

(** All parameter simplices over the prescribed domain have value c. *)

(** 给定域上的全部参数单形均取值 c。 *)

Definition is_simplicial_parameter_relative {m : nat}
    (T : SimplicialParameterF A m ⇒ X)
  : Type
  := ∀ n (b : B n) (t : (Δ[m]) n), T n (i n b, t) ≈S c n b.

(** A restricted actual parameter map retains the same prescribed values. *)

(** 限制后的实际参数映射保留同一给定值。 *)

Lemma simplicial_parameter_restrict_relative {m n : nat}
    (T : SimplicialParameterF A n ⇒ X)
    (R : is_simplicial_parameter_relative T) (θ : (@Hom Δ) m n)
  : is_simplicial_parameter_relative (T ∘Nv SimplicialParameterMapN A θ).
Proof.
  intros k b t. exact (R k b (fmap StandardSimplexF θ k t)).
Defined.

(** Specified natural equality transports relative witnesses without
    comparing the witnesses or requiring equality of functions. *)

(** 指定自然相等运输相对见证，不比较见证，也不要求函数相等。 *)

Lemma simplicial_parameter_relative_proper {m : nat}
    (T T' : SimplicialParameterF A m ⇒ X) (E : T ≈N T')
  : is_simplicial_parameter_relative T ↔
      is_simplicial_parameter_relative T'.
Proof.
  split; intros R n b t.
  - transitivity (T n (i n b, t)); [symmetry; apply E | apply R].
  - transitivity (T' n (i n b, t)); [apply E | apply R].
Defined.

End RelativeParameters.
