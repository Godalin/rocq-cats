From Cats Require Export
  Instance.Set.Simplicial.Vertex.Functor
  Instance.Set.Simplicial.Homotopy.Core
  Instance.Set.Vertex.Prism.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

Local Open Scope nat_scope.

(** * Natural Transformations Give Vertex Nerve Homotopies

    Fix object actions [T], [U] on label setoids [X], [Y],
    transport-preserving functors [F], [G], and independent value sizes
    [u], [p]. For each [α : F ⇒ G], construct the cylinder map and its
    endpoint equations, then prove respect for pointwise equality of [α].
    A time simplex [θ : [n] → [1]] decides when a labelled diagram changes
    from [F] to [G]. The prism reuses the walking-arrow diagram and
    uncurrying. Its comparison uses the prescribed vertex transports,
    rather than arbitrary natural isomorphisms of diagrams. *)

(** * 自然变换给出顶点 nerve 的同伦

    固定标签广集 [X]、[Y] 上的对象作用 [T]、[U]，保运输函子 [F]、[G]
    及独立值大小 [u]、[p]。对每个 [α : F ⇒ G] 构造柱映射及端点方程，
    再证明此构造保持 [α] 的逐点相等。
    时间单形 [θ : [n] → [1]] 决定带标签图式何时从 [F] 切换到 [G]。
    棱柱复用步行箭头图式与去柯里化；其比较使用指定顶点运输，
    而非图式之间的任意自然同构。 *)

(** For an arrow a from A to B, naturality of [α : F ⇒ G] says
    that the square below commutes in the target category's specified
    equality. It is the edge-level picture of the prism. For a whole chain,
    %\coqref{Cats.Cat.Diagram.Prism.PrismDiagramF}
    {%[PrismDiagramF]%}% supplies compatible diagrams in every degree, and
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Homotopy.VertexNerveHomotopy}
    {%[VertexNerveHomotopy]%}% assembles them into the simplicial homotopy whose
    endpoints were explained in %\coqref{Cats.Instance.Set.Simplicial.Homotopy.Core.SimplicialHomotopy}
    {%[SimplicialHomotopy]%}%. No inverse of a
    component of α is required. This chapter constructs the direction from
    natural transformations to homotopies. The converse and both round trips
    follow in
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.HomotopyInv.VertexNerveInvHomotopyN}
    {%[VertexNerveInvHomotopyN]%}%. *)

(** 对从 A 到 B 的箭头 a，[α : F ⇒ G] 的自然性说明下图按目标范畴的指定
    相等交换。这是棱柱在一条边上的图像。对整条箭头链，%\coqref{Cats.Cat.Diagram.Prism.PrismDiagramF}
    {%[PrismDiagramF]%}%
    在各维提供相容图式，%\coqref{Cats.Instance.Set.Simplicial.Vertex.Homotopy.VertexNerveHomotopy}
    {%[VertexNerveHomotopy]%}% 再把它们组装为单纯同伦，
    端点条件就是前面 %\coqref{Cats.Instance.Set.Simplicial.Homotopy.Core.SimplicialHomotopy}
    {%[SimplicialHomotopy]%}% 所说明的条件。构造不要求 α 的
    分量可逆。本章给出从自然变换到同伦的方向，反向恢复及两个往返律接着见
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.HomotopyInv.VertexNerveInvHomotopyN}
    {%[VertexNerveInvHomotopyN]%}%。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
F A \arrow[r,"{F a}"] \arrow[d,"{\alpha_A}"'] &
F B \arrow[d,"{\alpha_B}"] \\
G A \arrow[r,"{G a}"'] & G B
\end{tikzcd}
\end{center}%
*)

Section NerveHomotopies.
Universes u p.
Context {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
    {F G : T →ᵥ U}.

(** The cylinder map sends a labelled simplex and a monotone time simplex
    to the corresponding prism restriction. Both value sizes are shared;
    native source and target sizes remain independent. *)

(** 柱映射将带标签单形及保序时间单形送到相应棱柱限制。两个值大小共同选取，
    源及目标的原生大小仍保持独立。 *)

Program Definition VertexNerveHomotopyN (α : F ⇒ G)
  : SimplicialCylinderF
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U)
  :=
  {|nt n :=
      {|func z := ⟨PrismDiagramF α (lower (fst z)) (lower (snd z))⟩ᵥ
      |}
  |}.
Next Obligation.
  intros [[P] [θ]] [[Q] [φ]] [[e] [d]].
  refine {|lower := _
          |}.
  transitivity (PrismDiagramF α Q θ).
  - exact (vertex_prism_diagram_proper α θ P Q e).
  - apply vertex_prism_time_eq. exact (fst (simplex_eq_iff θ φ) d).
Defined.
Next Obligation.
  intros [[P] [θ]]. refine {|lower := _
                           |}.
  exists (λ i, reflexivity (_ : Y)). intros i j a.
  rewrite !(vertex_transport_id U), comp_id_l, comp_id_r. reflexivity.
Defined.

(** The complete homotopy retains this map and both endpoint equations.
    The transformation's components need not be invertible. *)

(** 完整同伦保留此映射及两个端点方程；自然变换的分量无须可逆。 *)

Program Definition VertexNerveHomotopy (α : F ⇒ G)
  : SimplicialHomotopy
      (VertexNerveN F :
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
      (VertexNerveN G)
  :=
  {|homotopy_map := VertexNerveHomotopyN α
  |}.
Next Obligation.
  destruct b; intros n [P]; refine {|lower := _
                                   |}.
  - exact (@vertex_prism_endpoint X Y C D [Ord n] T U F G α P true).
  - exact (@vertex_prism_endpoint X Y C D [Ord n] T U F G α P false).
Defined.

(** The construction respects pointwise equality of natural
    transformations, comparing the stored cylinder maps. *)

(** 此构造保持自然变换的逐点相等，比较所存柱映射。 *)

Global Instance vertex_nerve_homotopy_proper
  : Proper (NatEq ==> HomotopyEq) VertexNerveHomotopy.
Proof.
  intros α β H n [[P] [θ]]. refine {|lower := _
                                   |}.
  exact (vertex_prism_transformation_eq α β H P θ).
Defined.

(** The initial restriction is the nerve map induced by [F]. *)

(** 起点限制为 [F] 诱导的 nerve 映射。 *)

Lemma vertex_nerve_homotopy_0 (α : F ⇒ G)
  : (VertexNerveHomotopyN α ∘Nv SimplicialEndpointN Nᵥ(T) false) ≈N
      VertexNerveN F.
Proof. exact (homotopy_endpoint (VertexNerveHomotopy α) false). Defined.

(** The final restriction is the nerve map induced by [G]. *)

(** 终点限制为 [G] 诱导的 nerve 映射。 *)

Lemma vertex_nerve_homotopy_1 (α : F ⇒ G)
  : (VertexNerveHomotopyN α ∘Nv SimplicialEndpointN Nᵥ(T) true) ≈N
      VertexNerveN G.
Proof. exact (homotopy_endpoint (VertexNerveHomotopy α) true). Defined.

End NerveHomotopies.

(** The identity transformation yields the constant homotopy in the
    specified equality of cylinder maps; witness records are not equated. *)

(** 恒等自然变换在柱映射的指定相等下给出恒定同伦，不比较见证记录的原生相等。 *)

Lemma vertex_nerve_homotopy_id@{u p +} {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D} (F : T →ᵥ U)
  : HomotopyEq
      (VertexNerveHomotopy (F := F) (G := F)
        (idN : F ⇒ F) : SimplicialHomotopy
          (VertexNerveN F :
            (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
          (VertexNerveN F))
      (SimplicialConstantHomotopy (VertexNerveN F)).
Proof.
  intros n [[P] [θ]]. refine {|lower := _
                             |}.
  exact (@vertex_prism_id X Y C D [Ord n] T U F P θ).
Defined.
