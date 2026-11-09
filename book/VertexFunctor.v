(** * Which Functors Act on the Vertex Nerve?

    The vertex nerve retains object labels and their specified transports.
    A functor between presentations must preserve both. Its comparison is a
    natural isomorphism whose components are the prescribed transports.
    Arbitrary natural isomorphisms can forget distinctions still visible in
    degree zero, as the following checked example shows. *)

(** * 哪些函子作用于顶点 nerve？

    顶点 nerve 保留对象标签及其指定运输。呈现之间的函子须保持这两者，其比较为
    分量等于指定运输的自然同构。任意自然同构可能忘却零维中仍可见的区别，以下
    经过检查的例子说明了这一点。 *)

From Cats Require Import
  Instance.Set.Simplicial.Vertex.Reconstruction
  Instance.Bool.Group
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Preorder
  Cat.Diagram.Core.

(** ** 1. Isomorphic objects with different specified labels

    The codiscrete category on booleans has a unique arrow between any
    two objects. Its object presentation uses [BoolS], whose equality is
    native boolean equality. Thus the two objects are isomorphic, while
    their specified labels remain distinct. *)

(** ** 1. 同构对象具有不同的指定标签

    布尔值上的余离散范畴在任意两个对象之间均有唯一箭头。对象呈现使用 [BoolS]，
    其相等为布尔值的原生相等。因此两个对象同构，但其指定标签仍保持区别。 *)

Program Definition BooleanLabels
  : Functor (EqGpd BoolS) (CodiscreteCat bool)
  :=
  {|F0 b := b
  ; F1 x y p := tt
  |}.
Next Obligation. intros p q H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** A constant functor respects the object setoid and all transports. *)

(** 常值函子保持对象广集及全部运输。 *)

Program Definition ConstantVertexF (b : bool)
  : BooleanLabels →ᵥ BooleanLabels
  :=
  {|vertex_functor := ConstF (VertexCat BooleanLabels)
      (C := VertexCat BooleanLabels) b
  |}.
Next Obligation. intros; reflexivity. Defined.

(** ** 2. Ordinary natural isomorphism forgets the label difference

    Unique codiscrete arrows give a natural isomorphism between the two
    underlying constant functors, even though their labels disagree. *)

(** ** 2. 普通自然同构忘却标签区别

    唯一的余离散箭头给出两个底层常值函子之间的自然同构，尽管其标签不同。 *)

Program Definition constants_nat_iso
  : ConstantVertexF false ≅N ConstantVertexF true
  := ({|nt x := tt
       |}; _).
Next Obligation. exact tt. Defined.
Next Obligation. intros x. exists tt. split; exact tt. Defined.

(** A prescribed-transport comparison would equate false and true. *)

(** 指定运输比较将迫使 false 和 true 相等。 *)

Example constants_not_vertex_equal
  : ¬ VertexFunctorEq (ConstantVertexF false) (ConstantVertexF true).
Proof. intros [e H]. discriminate (e false). Defined.

(** ** 3. Degree zero detects exactly the retained distinction

    Postcomposition by the two functors produces different simplicial
    maps. This prevents using arbitrary natural-isomorphism equality on
    the source hom-setoid of the full-faithfulness theorem. *)

(** ** 3. 零维检测所保留的区别

    两个函子的后复合产生不同的单纯映射。因此全忠实定理不能在源态射广集
    上使用任意自然同构相等。 *)

Example constant_nerve_maps_distinct
  : ¬ ((VertexNerveN (ConstantVertexF false) :
      (Nᵥ(BooleanLabels) : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) ⇒ _)
        ≈N VertexNerveN (ConstantVertexF true)).
Proof.
  intros H.
  pose (x := ⟨ConstF [Ord 0] (C := VertexCat BooleanLabels) false⟩ᵥ).
  pose (e := (lower (H 0%nat x)).1 fin_first).
  discriminate e.
Defined.

(** ** 4. Every simplicial map reconstructs a transport-preserving functor

    [VertexNerveInvF] extracts objects in degree zero and arrows in degree
    one. Naturality aligns endpoints by specified transport; degeneracies
    give identities and triangles give composition. The following result
    applies to any simplicial map, rather than only one built from a functor. *)

(** ** 4. 每个单纯映射重构为保运输函子

    [VertexNerveInvF] 从零维提取对象、从一维提取箭头。自然性通过指定运输对齐
    端点，退化给出恒等，三角形给出复合。以下结论适用于任意单纯映射，而不只
    适用于已经由函子构造的映射。 *)

Example every_boolean_nerve_map_reconstructs
    (α : (Nᵥ(BooleanLabels) :
      Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) ⇒ Nᵥ(BooleanLabels))
  : VertexNerveN (VertexNerveInvF α) ≈N α.
Proof. exact (vertex_nerve_β α). Defined.

(** The other round trip uses [VertexFunctorEq]. It does not identify the
    distinct constant functors above. *)

(** 另一侧往返使用 [VertexFunctorEq]，不会识别上面两个不同的常值函子。 *)

Example boolean_vertex_functor_round_trip (F : BooleanLabels →ᵥ BooleanLabels)
  : VertexFunctorEq (VertexNerveInvF (VertexNerveN F :
      (Nᵥ(BooleanLabels) : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) ⇒ _)) F.
Proof. exact (vertex_nerve_η F). Defined.

(** [vertex_nerve_hom_iso] bundles both respectful maps and round trips as
    a setoid isomorphism after ordinary common size lifts. This is full
    faithfulness for specified object presentations and their prescribed
    transport comparisons; arbitrary natural isomorphisms remain coarser. *)

(** [vertex_nerve_hom_iso] 在通常的共同大小提升后，将两个保相等映射及往返律
    捆绑为广集同构。这是指定对象呈现及其指定运输比较的全忠实性；任意自然
    同构仍然更粗。 *)
