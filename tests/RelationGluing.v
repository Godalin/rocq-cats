From Cats.Cat.Functor Require Import RelationGluing.
From Cats Require Import
  Cat.Preorder
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Nat.

(** * Relation Gluing Interface Regressions

    Relation witnesses can be larger than setoid equality, or smaller
    than both carriers and equality. A concrete identity action changes
    the retained witness while preserving the glued setoid value. *)

(** * 关系粘合接口回归

    关系见证可以大于广集相等，也可以同时小于载体与相等。具体的恒等作用会
    改变保留的见证，同时保持粘合广集中的值。 *)

(** ** Witnesses above Equality

    Fix [q < w < u]. Both diagrams share the ambient bounds [u] and [q];
    their constant relation retains arbitrary [Type@{w}] data. *)

(** ** 高于相等的见证

    固定 [q < w < u]。两个图式共用环境界 [u] 和 [q]；常值关系保留任意
    [Type@{w}] 数据。 *)

Section LargeWitnesses.
Universes q w u.
Constraint q < w, w < u.
Context {J : Cat} (F G : Functor J SetCat@{u q _ _ _ _ _}).
Context (W : Type@{w}).

(** No equation between the retained witnesses is required. *)

(** 不要求保留见证之间的方程。 *)

Program Definition LargeRelation
  : DiagramRelation F G
  :=
  {|diagram_relation X x y := W
  ; diagram_relation_map X Y f x y h := h
  |}.
Next Obligation. intros x x' hx y y' hy. exact ((λ h, h), (λ h, h)). Defined.

(** Gluing does not raise the specified equality bound to [w]. *)

(** 粘合不将指定相等界提升到 [w]。 *)

Definition large_witness_gluing
  : Functor J SetCat@{u q _ _ _ _ _}
  := RelationGluingF F G LargeRelation.

End LargeWitnesses.

(** ** Equality above Carriers

    Fix [w < u < q], reversing the witness/equality order and permitting
    equality above the common carrier bound. *)

(** ** 高于载体的相等

    固定 [w < u < q]，反转见证与相等的次序，并允许相等高于共同载体界。 *)

Section LargeEquality.
Universes w u q.
Constraint w < u, u < q.
Context {J : Cat} (F G : Functor J SetCat@{u q _ _ _ _ _}).
Context (W : Type@{w}).

(** Membership stays at the smaller witness bound. *)

(** 隶属保留在较小的见证界。 *)

Program Definition SmallRelation
  : DiagramRelation F G
  :=
  {|diagram_relation X x y := W
  ; diagram_relation_map X Y f x y h := h
  |}.
Next Obligation. intros x x' hx y y' hy. exact ((λ h, h), (λ h, h)). Defined.

(** Large equality does not enlarge the glued carrier. *)

(** 大相等不增大粘合载体。 *)

Definition large_equality_gluing
  : Functor J SetCat@{u q _ _ _ _ _}
  := RelationGluingF F G SmallRelation.

End LargeEquality.

(** ** Computational Witnesses and Setoid Laws

    Use a one-object world and two constant natural-number diagrams.
    Every pair is related by a natural-number tag. Arrow transport
    increments the tag, so witness transport is deliberately not strict
    on identities. The glued functor laws compare only the two values. *)

(** ** 计算性见证与广集定律

    使用单对象世界及两个常值自然数图式。每个配对由一个自然数标签关联。
    箭头运输递增标签，故见证运输在恒等上有意不是严格的；粘合函子律只比较
    两个值。 *)

Section Tags.

(** The same constant diagram on either side. *)

(** 两边使用同一个常值图式。 *)

Definition NumbersF
  : Functor (CodiscreteCat unit) SetCat
  := ConstF (CodiscreteCat unit) (C := SetCat) NatS.

(** Tags remain data, with arbitrary maps between the membership types. *)

(** 标签保留为数据，隶属类型之间使用选定映射。 *)

Program Definition TaggedRelation
  : DiagramRelation NumbersF NumbersF
  :=
  {|diagram_relation X x y := nat
  ; diagram_relation_map X Y f x y h := S h
  |}.

(** A displayed related pair with tag seven. *)

(** 标签为七的显式相关配对。 *)

Definition tagged_pair
  : RelationGluingF NumbersF NumbersF TaggedRelation tt
  := ((2, 3); 7).

(** Identity transport computes the changed tag, while preserving values. *)

(** 恒等运输计算出改变后的标签，同时保持值。 *)

Example identity_tag_computes
  : let p := fmap (RelationGluingF NumbersF NumbersF TaggedRelation)
      (@Cats.Cat.Core.id (CodiscreteCat unit) tt) tagged_pair in
    (p.1, p.2) = ((2, 3), 8).
Proof. reflexivity. Defined.

(** The functor identity still holds in the specified setoid equality. *)

(** 函子恒等仍按指定广集相等成立。 *)

Example identity_values_agree
  : fmap (RelationGluingF NumbersF NumbersF TaggedRelation)
      (@Cats.Cat.Core.id (CodiscreteCat unit) tt) tagged_pair ≈S tagged_pair.
Proof. exact (eq_refl, eq_refl). Defined.

End Tags.
