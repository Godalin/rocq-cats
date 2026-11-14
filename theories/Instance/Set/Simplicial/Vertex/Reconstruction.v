From Cats Require Export
  Instance.Set.Simplicial.Vertex.Functor
  Instance.Set.Simplicial.Vertex.Point
  Instance.Set.Simplicial.Vertex.Edge.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Instance.Set.Yoneda
  Instance.Set.Isomorphism.

Local Open Scope nat_scope.

(** * Reconstructing Functors from Simplicial Maps

    Degree zero selects the object map. Degree one supplies arrows, whose
    endpoints are aligned by naturality and specified object transport.
    Triangles recover composition. All witnesses remain transparent and
    no groupoid or native object-equality assumption is required. *)

(** * 从单纯映射重构函子

    零维选取对象映射，一维提供箭头；通过自然性和指定对象运输对齐其端点。
    三角形恢复复合。所有见证保持透明，无需群胚或对象原生相等假设。 *)

(** This reverses the construction %\coqref{Cats.Instance.Set.Simplicial.Vertex.Functor.VertexNerveN}
    {%[VertexNerveN]%}% on maps: instead
    of starting with a functor, start with a simplicial map [α] between two
    vertex nerves. Its degree-zero part chooses images of objects; its
    degree-one part chooses images of arrows. The naturality square
    %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict natural}
    {%[simplex_restrict_natural]%}% aligns their endpoints. Degenerate edges
    force identity preservation, and the nerve's composition triangle forces
    composition preservation. The remaining proof work keeps these
    statements coherent with the specified label transports. *)

(** 这里反过来恢复 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Functor.VertexNerveN}
    {%[VertexNerveN]%}% 的输入：从两个顶点 nerve 之间的单纯映射
    [α] 出发，零维部分选择对象的像，一维部分选择箭头的像。自然性方块
    %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict natural}
    {%[simplex_restrict_natural]%}% 对齐端点；退化边保证保持恒等，nerve 的复合
    三角形保证保持复合。其余证明负责使这些结论与指定的标签运输保持相干。 *)

Section Reconstruction.
Universes u p.
Context {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
    (α : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U)).

(** Extract the respectful object map from degree zero. *)

(** 从零维提取保相等对象映射。 *)

Definition nerve_map_ob_resp
  : X →r Y
  := vertex_zero_resp U ∘r α 0 ∘r △₀[T].

(** Naturality aligns every occurrence of a vertex with its chosen image. *)

(** 自然性将顶点的每个出现对齐到其选定像。 *)

Definition nerve_map_vertex {n : nat}
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
    (i : Ordinal n)
  : nerve_map_ob_resp (lower x i) ≈S lower (α n x) i.
Proof.
  pose (Q := ConstF [Ord 0] (C := [Ord n]) i).
  assert (H : α 0 (△₀[T] (lower x i)) ≈S Nᵥ(U)[Q]Δ (α n x)).
  { transitivity (α 0 (Nᵥ(T)[Q]Δ x)).
    - apply func_proper. exact (vertex_zero_η (Nᵥ(T)[Q]Δ x)).
    - exact (nt_naturality α Q x). }
  exact (@func_proper _ _ (vertex_zero_resp U) _ _ H).
Defined.

(** Rebase the image edge to the objects chosen in degree zero. *)

(** 将像边的端点调整到零维选取的对象。 *)

Definition nerve_map_arrow {A B : X} (f : (@Hom (VertexCat T)) A B)
  : (@Hom (VertexCat U)) (nerve_map_ob_resp A) (nerve_map_ob_resp B)
  := let e := △₁[T; A; B] f in
    U⟦nerve_map_vertex e fin_first;
      fmap (lower (α 1 e)) (ordinal_step fin_first);
      nerve_map_vertex e (fin_next fin_first)⟧Ar.

(** The normalized edge equals its original image in the nerve. *)

(** 归一化边在 nerve 中等于原来的像。 *)

Lemma nerve_map_edge {A B : X} (f : (@Hom (VertexCat T)) A B)
  : △₁[U; nerve_map_ob_resp A; nerve_map_ob_resp B] (nerve_map_arrow f) ≈S
      α 1 (△₁[T; A; B] f).
Proof.
  apply (vertex_edge_comparison
    (△₁[U; nerve_map_ob_resp A; nerve_map_ob_resp B] (nerve_map_arrow f))
    (α 1 (△₁[T; A; B] f))
    (nerve_map_vertex (△₁[T; A; B] f) fin_first)
    (nerve_map_vertex (△₁[T; A; B] f) (fin_next fin_first))).
  rewrite edge_simplex_arrow. apply vertex_rebase_square.
Defined.

(** Image arrows preserve every specified transport square, with arbitrary
    parallel endpoint witnesses supplied by the respectful object map. *)

(** 像箭头保持每个指定运输方块，其平行端点见证由保相等对象映射提供。 *)

Lemma nerve_map_arrow_square {A B A' B' : X}
    (a : A ≈S A') (b : B ≈S B')
    (f : (@Hom (VertexCat T)) A B) (g : (@Hom (VertexCat T)) A' B')
    (H : T⟦b⟧Ob ∘ f ≈ g ∘ T⟦a⟧Ob)
  : U⟦@func_proper _ _ nerve_map_ob_resp B B' b⟧Ob ∘ nerve_map_arrow f ≈
      nerve_map_arrow g ∘ U⟦@func_proper _ _ nerve_map_ob_resp A A' a⟧Ob.
Proof.
  assert (K : △₁[T; A; B] f ≈S △₁[T; A'; B'] g).
  { apply (vertex_edge_comparison
      (△₁[T; A; B] f) (△₁[T; A'; B'] g) a b).
    rewrite !edge_simplex_arrow. exact H. }
  assert (L : △₁[U; nerve_map_ob_resp A; nerve_map_ob_resp B]
      (nerve_map_arrow f) ≈S
    △₁[U; nerve_map_ob_resp A'; nerve_map_ob_resp B'] (nerve_map_arrow g)).
  { transitivity (α 1 (△₁[T; A; B] f)); [apply nerve_map_edge |].
    transitivity (α 1 (△₁[T; A'; B'] g)).
    - apply func_proper. exact K.
    - symmetry. apply nerve_map_edge. }
  pose (E := vertex_edge_square
    (△₁[U; nerve_map_ob_resp A; nerve_map_ob_resp B] (nerve_map_arrow f))
    (△₁[U; nerve_map_ob_resp A'; nerve_map_ob_resp B'] (nerve_map_arrow g))
    (@func_proper _ _ nerve_map_ob_resp A A' a)
    (@func_proper _ _ nerve_map_ob_resp B B' b) L).
  rewrite !edge_simplex_arrow in E. exact E.
Defined.

(** Parallel equal arrows have equal normalized images. *)

(** 平行相等箭头具有相等的归一化像。 *)

Global Instance nerve_map_arrow_proper {A B : X}
  : Proper (@HomEq (VertexCat T) A B ==>
      @HomEq (VertexCat U) (nerve_map_ob_resp A) (nerve_map_ob_resp B))
      (@nerve_map_arrow A B).
Proof.
  intros f g H.
  assert (K : T⟦reflexivity (B : X)⟧Ob ∘ f ≈
      g ∘ T⟦reflexivity (A : X)⟧Ob).
  { rewrite !vertex_transport_id, comp_id_l, comp_id_r. exact H. }
  pose (L := nerve_map_arrow_square _ _ f g K).
  rewrite !vertex_transport_id, comp_id_l, comp_id_r in L. exact L.
Defined.

(** An arrow in any source simplex computes its normalized global image. *)

(** 任意源单形中的箭头计算其归一化全局像。 *)

Lemma nerve_map_arrow_simplex {n : nat}
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
    (i j : Ordinal n) (h : (@Hom [Ord n]) i j)
  : nerve_map_arrow (fmap (lower x) h) ≈
      U⟦nerve_map_vertex x i; fmap (lower (α n x)) h; nerve_map_vertex x j⟧Ar.
Proof.
  pose (Q := ⟦ArrowChain h⟧Ch).
  pose (f := fmap (lower x) h).
  assert (L : α 1 (△₁[T; lower x i; lower x j] f) ≈S
      Nᵥ(U)[Q]Δ (α n x)).
  { transitivity (α 1 (Nᵥ(T)[Q]Δ x)).
    - apply func_proper. exact (vertex_edge_restrict x i j h).
    - exact (nt_naturality α Q x). }
  destruct L as [[e L]]. unfold nerve_map_arrow.
  transitivity (U⟦nerve_map_vertex x i;
      fmap (lower (α n x)) (fmap Q (ordinal_step fin_first));
      nerve_map_vertex x j⟧Ar).
  - exact (vertex_rebase_eq U _ _ _ _ (e fin_first)
      (e (fin_next fin_first)) _ _ (L _ _ (ordinal_step fin_first))).
  - apply func_proper. apply functor_fmap_proper. exact tt.
Defined.

(** Degenerate edges give the identity law. *)

(** 退化边给出恒等律。 *)

Lemma nerve_map_arrow_id (A : X)
  : nerve_map_arrow (@Cats.Cat.Core.id (VertexCat T) A) ≈ id.
Proof.
  pose (x := △₀[T] A).
  transitivity (U⟦nerve_map_vertex x fin_first;
      fmap (lower (α 0 x)) (@Cats.Cat.Core.id [Ord 0] fin_first);
      nerve_map_vertex x fin_first⟧Ar).
  - exact (nerve_map_arrow_simplex x _ _ id).
  - change (U⟦symmetry (nerve_map_vertex x fin_first)⟧Ob ∘
      fmap (lower (α 0 x)) id ∘ U⟦nerve_map_vertex x fin_first⟧Ob ≈ id).
    rewrite functor_id, comp_id_r. apply vertex_transport_inv.
Defined.

(** Composition inside any simplex is preserved after endpoint alignment. *)

(** 端点对齐后保持任意单形内部的复合。 *)

Lemma nerve_map_simplex_comp {n : nat}
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
    (i j k : Ordinal n) (f : (@Hom [Ord n]) i j)
    (g : (@Hom [Ord n]) j k)
  : nerve_map_arrow (fmap (lower x) (g ∘ f)) ≈
      nerve_map_arrow (fmap (lower x) g) ∘
      nerve_map_arrow (fmap (lower x) f).
Proof.
  transitivity (U⟦nerve_map_vertex x i;
      fmap (lower (α n x)) (g ∘ f); nerve_map_vertex x k⟧Ar).
  - exact (nerve_map_arrow_simplex x i k (g ∘ f)).
  - transitivity (U⟦nerve_map_vertex x i;
        fmap (lower (α n x)) g ∘ fmap (lower (α n x)) f;
        nerve_map_vertex x k⟧Ar).
    + apply func_proper. apply functor_comp.
    + etransitivity; [apply vertex_rebase_comp |].
      apply comp_proper; symmetry; apply nerve_map_arrow_simplex.
Defined.

(** The triangle on two arbitrary arrows supplies the global functor law. *)

(** 任意两条箭头构成的三角形提供全局函子律。 *)

Lemma nerve_map_arrow_comp {A B E : X}
    (f : (@Hom (VertexCat T)) A B) (g : (@Hom (VertexCat T)) B E)
  : nerve_map_arrow (g ∘ f) ≈ nerve_map_arrow g ∘ nerve_map_arrow f.
Proof.
  pose (x := ⟨⟦⟨f, g⟩Ch⟧Ch⟩ᵥ :
    (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) 2).
  pose (a := ordinal_step (@fin_first 1)).
  pose (b := ordinal_step (fin_next (@fin_first 0))).
  assert (Ha : fmap (lower x) a ≈ f).
  { exact (chain_diagram_β ⟨f, g⟩Ch (@fin_first 1)). }
  assert (Hb : fmap (lower x) b ≈ g).
  { exact (chain_diagram_β ⟨f, g⟩Ch (fin_next (@fin_first 0))). }
  transitivity (nerve_map_arrow (fmap (lower x) (b ∘ a))).
  - apply nerve_map_arrow_proper. symmetry.
    etransitivity; [exact (@functor_comp _ _ (lower x) _ _ _ b a) |].
    apply comp_proper; assumption.
  - etransitivity; [exact (nerve_map_simplex_comp x _ _ _ a b) |].
    apply comp_proper; apply nerve_map_arrow_proper; assumption.
Defined.

(** Equality of transport edges forces preservation of the specified
    object transport, rather than an arbitrary natural-isomorphism choice. *)

(** 运输边的相等迫使重构保持指定对象运输，而非任意选择的自然同构。 *)

Lemma nerve_map_transport {A B : X} (p : A ≈S B)
  : nerve_map_arrow T⟦p⟧Ob ≈
      U⟦@func_proper _ _ nerve_map_ob_resp A B p⟧Ob.
Proof.
  assert (H : T⟦p⟧Ob ∘ id ≈ T⟦p⟧Ob ∘ T⟦reflexivity A⟧Ob).
  { rewrite vertex_transport_id. reflexivity. }
  pose (K := nerve_map_arrow_square (reflexivity A) p id T⟦p⟧Ob H).
  rewrite nerve_map_arrow_id, vertex_transport_id, !comp_id_r in K.
  symmetry. exact K.
Defined.

(** The reconstructed ordinary functor has no groupoid dependency. *)

(** 重构的普通函子不依赖群胚结构。 *)

Program Definition NerveMapF
  : Functor (VertexCat T) (VertexCat U)
  :=
  {|F0 := nerve_map_ob_resp
  ; F1 A B f := nerve_map_arrow f
  |}.
Next Obligation. exact (nerve_map_arrow_id X0). Defined.
Next Obligation. exact (nerve_map_arrow_comp g f). Defined.

(** Bundle the reconstructed functor with its object respectfulness and
    specified transport law. *)

(** 将重构函子、对象保相等性及指定运输律捆绑起来。 *)

Program Definition VertexNerveInvF
  : T →ᵥ U
  :=
  {|vertex_functor := NerveMapF
  ; vertex_functor_ob_proper := @func_proper _ _ nerve_map_ob_resp
  |}.
Next Obligation. exact (nerve_map_transport p). Defined.

(** Reconstructing a simplicial map recovers its action in every degree. *)

(** 重构单纯映射后，在每个维度恢复其作用。 *)

Lemma vertex_nerve_β
  : VertexNerveN VertexNerveInvF ≈N α.
Proof.
  intros n x. refine {|lower := _
                    |}.
  exists (nerve_map_vertex x). intros i j f.
  change (U⟦nerve_map_vertex x j⟧Ob ∘
      nerve_map_arrow (fmap (lower x) f) ≈
    fmap (lower (α n x)) f ∘ U⟦nerve_map_vertex x i⟧Ob).
  rewrite (nerve_map_arrow_simplex x i j f). apply vertex_rebase_square.
Defined.

End Reconstruction.

(** Equal simplicial maps reconstruct equal transport-preserving functors.
    Endpoint witnesses come from degree zero; degree one supplies squares. *)

(** 相等单纯映射重构为相等的保运输函子。端点见证来自零维，一维提供方块。 *)

Global Instance vertex_nerve_inv_proper@{u p +}
    {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
  : Proper (NatEq ==> VertexFunctorEq)
      (@VertexNerveInvF _ _ _ _ T U :
        ((Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U)) → _).
Proof.
  intros α β H.
  pose (e := λ A : X, (lower (H 0 (△₀[T] A))).1 fin_first).
  exists e. intros A B f.
  assert (L : △₁[U; nerve_map_ob_resp α A; nerve_map_ob_resp α B]
      (nerve_map_arrow α f) ≈S
    △₁[U; nerve_map_ob_resp β A; nerve_map_ob_resp β B]
      (nerve_map_arrow β f)).
  { transitivity (α 1 (△₁[T; A; B] f)); [apply nerve_map_edge |].
    transitivity (β 1 (△₁[T; A; B] f)).
    - exact (H 1 (△₁[T; A; B] f)).
    - symmetry. apply nerve_map_edge. }
  pose (K := vertex_edge_square
    (△₁[U; nerve_map_ob_resp α A; nerve_map_ob_resp α B] (nerve_map_arrow α f))
    (△₁[U; nerve_map_ob_resp β A; nerve_map_ob_resp β B] (nerve_map_arrow β f))
    (e A) (e B) L).
  rewrite !edge_simplex_arrow in K. exact K.
Defined.

(** The inverse is a respectful map between the native hom-setoids. *)

(** 逆构造是原生态射广集之间的保相等映射。 *)

Program Definition vertex_nerve_inv_resp@{u p +}
    {X Y : SetC} {C D : Cat}
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D)
  : Nat_SetS (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(U)) →r
      VertexFunctorS T U
  :=
  {|func := VertexNerveInvF
  |}.

(** Reconstructing the nerve of a vertex functor recovers it up to its
    specified transport comparison, without equality of functor records. *)

(** 重构顶点函子的 nerve 后，在指定运输比较下恢复原函子，不要求函子记录相等。 *)

Lemma vertex_nerve_η@{u p +} {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D} (F : T →ᵥ U)
  : VertexFunctorEq
      (VertexNerveInvF (VertexNerveN F :
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))) F.
Proof.
  exists (λ A, reflexivity (F A : Y)). intros A B f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  change (U⟦nerve_map_vertex (VertexNerveN F) (△₁[T; A; B] f) fin_first;
      fmap F (fmap (lower (△₁[T; A; B] f)) (ordinal_step fin_first));
      nerve_map_vertex (VertexNerveN F) (△₁[T; A; B] f)
        (fin_next fin_first)⟧Ar ≈ fmap F f).
  etransitivity; [apply vertex_rebase_id |].
  exact (@functor_fmap_proper _ _ F _ _ _ _ (edge_simplex_arrow f)).
Defined.

(** Full faithfulness is a hom-setoid isomorphism for labelled object
    presentations. The ordinary size inclusions merely place the two
    native hom-setoids in common, independent carrier/equality universes. *)

(** 全忠实性是带标签对象呈现之间的态射广集同构。通常的大小嵌入仅将两个原生
    态射广集放入共同且相互独立的载体／相等宇宙。 *)

Definition vertex_nerve_hom_iso@{v q u p +}
    {X Y : SetC} {C D : Cat}
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D)
  : LiftS@{_ _ v q} (VertexFunctorS T U) ≅[SetCat]
      LiftS@{_ _ v q} (Nat_SetS
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(U))).
Proof.
  exists ((vertex_nerve_resp T U)^↑S), ((vertex_nerve_inv_resp T U)^↑S).
  split.
  - intros [F]. exact {|lower := vertex_nerve_η F
                       |}.
  - intros [α]. exact {|lower := vertex_nerve_β α
                       |}.
Defined.
