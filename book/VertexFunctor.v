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
  Instance.Set.Simplicial.Vertex.Functor
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
    the source hom-setoid of a proposed full-faithfulness theorem. *)

(** ** 3. 零维检测所保留的区别

    两个函子的后复合产生不同的单纯映射。因此拟议的全忠实定理不能在源态射广集
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

(** The accepted source comparison is [VertexFunctorEq], and
    [vertex_nerve_resp] is its respectful forward map to simplicial maps.
    A full-faithfulness theorem still needs the inverse reconstruction
    and both round-trip laws in their specified equalities. *)

(** 所选源比较为 [VertexFunctorEq]，[vertex_nerve_resp] 是它到单纯映射的保相等
    前向映射。全忠实定理仍须反向重构，以及两侧指定相等下的往返律。 *)
