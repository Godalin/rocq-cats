From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Product.
From Cats.Set Require Import Subset.

(** * Witness-Preserving Relation Gluing of Diagrams

    Given two setoid-valued diagrams and a relation between their values
    at each object, retain triples consisting of two values and a relation
    witness. An arrow acts on both values and transports the witness.
    Equality compares the values, not their stored membership evidence.

    This is a pointwise subset of the product diagram, reusing [SubsetS].
    The relation respects both input equalities and has an arrow action.
    These are separate laws: the action does not imply respectfulness.
    Equations between witness actions are unnecessary because equality
    forgets only those witnesses.

    Both diagrams use a common ambient carrier bound [u] and equality
    bound [q]. Stored relation evidence has its own bound [w <= u];
    there is no ordering requirement between [w] and [q]. Smaller input
    diagrams may first be raised by the existing explicit lifts. *)

(** * 保留见证的图式关系粘合

    给定两个广集值图式及每个对象处其值之间的关系，保留由两个值和一个关系
    见证组成的三元组。箭头作用于两个值并传递见证；相等比较值，不比较保存的
    隶属证据。

    这是积图式的逐点子集，复用 [SubsetS]。关系保持两边的输入相等，并有箭头
    作用；这是两条独立定律，不能从箭头作用推断保相等性。见证作用之间无需
    方程，因为相等只忘却这些见证。

    两个图式使用共同的环境载体界 [u] 和相等界 [q]。保存的关系证据另有界
    [w <= u]，不要求 [w] 与 [q] 的大小次序。较小的输入图式可先用既有显式
    提升扩大。 *)

(** A respectful relation between two diagrams, with chosen transport
    along their arrows. Transport witnesses need not be equal. *)

(** 两个图式之间的保相等关系，带选定的沿箭头运输；不要求运输见证相等。 *)

Class DiagramRelation@{w +} {J : Cat} (F G : Fct J SetCat)
  :=
  {
  (** The unique function view exposes the pointwise relation. *)

  (** 唯一的函数视图暴露逐点关系。 *)

    diagram_relation :> ∀ X, F X → G X → Type@{w}

  (** Changing either value by its specified equality preserves membership. *)

  (** 按指定相等改变任一值，保持隶属。 *)

  ; diagram_relation_proper X
      :: Proper ([≈S] ==> [≈S] ==> iffT) (diagram_relation X)

  (** Map a related pair along one diagram arrow, retaining its witness. *)

  (** 沿图式箭头映射相关配对，并保留其见证。 *)

  ; diagram_relation_map : ∀ X Y (f : Hom X Y) x y,
      diagram_relation X x y →
        diagram_relation Y (fmap F f x) (fmap G f y)
  }.

Arguments diagram_relation {_ _ _} _ _ _ _.
Arguments diagram_relation_proper {_ _ _} _ _.
Arguments diagram_relation_map {_ _ _} _ {_ _} _ {_ _} _.

(** ** Related Pairs and Their Projections

    Fix an indexing category, two diagrams, a relation and its arrow
    action. Construct the glued diagram and its two natural projections.
    All subset and transport witnesses remain computational data. *)

(** ** 相关配对及其投影

    固定索引范畴、两个图式、关系及其箭头作用。构造粘合图式及两个自然投影，
    所有子集和运输见证均保留为可计算数据。 *)

Section RelationGluing.
Universes u q.
Context {J : Cat} (F G : Fct J SetCat@{u q _ _ _ _ _}).
Context (R : DiagramRelation F G).

(** The subset inherits componentwise setoid equality. Membership
    evidence can be larger than that equality. *)

(** 子集继承逐分量广集相等；隶属证据可以大于该相等。 *)

Definition RelationGluingS (X : @Ob J)
  : SetC@{u q}
  := SubsetS (F X ×S G X) (λ p, R X (fst p) (snd p)).

(** Map both values and retain the supplied transport of membership. *)

(** 映射两个值，并保留给定的隶属运输。 *)

Program Definition relation_gluing_map {X Y : @Ob J} (f : Hom X Y)
  : RelationGluingS X →r RelationGluingS Y
  :=
  {|func p := ((fmap F f (fst p.1), fmap G f (snd p.1));
      diagram_relation_map R f p.2)
  |}.
Next Obligation.
  intros [[x y] h] [[x' y'] h'] [hx hy]. split;
    apply func_proper; assumption.
Defined.

(** The two original functor laws prove all laws of the glued diagram;
    no equation between membership witnesses is asserted. *)

(** 两个原函子的定律证明粘合图式的全部函子律，不断言隶属见证之间的方程。 *)

Program Definition RelationGluingF
  : Fct J SetCat@{u q _ _ _ _ _}
  :=
  {|F0 := RelationGluingS
  ; F1 X Y := relation_gluing_map
  |}.
Next Obligation.
  intros f g h [[x y] r]. split.
  - exact (@functor_fmap_proper J SetCat F X Y f g h x).
  - exact (@functor_fmap_proper J SetCat G X Y f g h y).
Defined.
Next Obligation.
  intros [[x y] h]. split.
  - exact (@functor_id J SetCat F X x).
  - exact (@functor_id J SetCat G X y).
Defined.
Next Obligation.
  intros [[x y] h]. split.
  - exact (@functor_comp J SetCat F X Y Z f g x).
  - exact (@functor_comp J SetCat G X Y Z f g y).
Defined.

(** Forget the semantic/right value and the relation witness. *)

(** 忘却右侧值及关系见证。 *)

Program Definition RelationGluingLeftN
  : RelationGluingF ⇒ F
  :=
  {|nt X :=
     {|func p := fst p.1
     |}
  |}.
Next Obligation. intros [[x y] h] [[x' y'] h'] [hx hy]. exact hx. Defined.
Next Obligation. intros [[x y] h]. reflexivity. Defined.

(** Forget the syntactic/left value and the relation witness. *)

(** 忘却左侧值及关系见证。 *)

Program Definition RelationGluingRightN
  : RelationGluingF ⇒ G
  :=
  {|nt X :=
     {|func p := snd p.1
     |}
  |}.
Next Obligation. intros [[x y] h] [[x' y'] h'] [hx hy]. exact hy. Defined.
Next Obligation. intros [[x y] h]. reflexivity. Defined.

(** ** Lifting Related Natural Maps

    Fix a third diagram and two natural maps into the original diagrams.
    A pointwise relation witness lifts them to the glued diagram. The
    projections characterize this lift by natural equality; the witness
    fields need no additional coherence or uniqueness assumptions. *)

(** ** 提升相关的自然映射

    固定第三个图式及到原两个图式的自然映射。逐点关系见证将它们提升到粘合
    图式。两个投影按自然相等刻画此提升；见证字段不需要额外相干性或唯一性
    假设。 *)

Section RelatedMaps.
Context {H : Fct J SetCat@{u q _ _ _ _ _}} (α : H ⇒ F) (β : H ⇒ G).
Context (related : ∀ X x, R X (α X x) (β X x)).

(** Retain the two component images with their chosen relatedness. *)

(** 将两个分量的像与其选定关联见证一起保留。 *)

Program Definition RelationGluingPairN
  : H ⇒ RelationGluingF
  :=
  {|nt X :=
     {|func x := ((α X x, β X x); related X x)
     |}
  |}.
Next Obligation. intros x y h. split; apply func_proper; exact h. Defined.
Next Obligation.
  intros x. split; [exact (nt_naturality α f x) |
    exact (nt_naturality β f x)].
Defined.

(** The left projection recovers the first natural map. *)

(** 左投影恢复第一个自然映射。 *)

Definition relation_gluing_pair_β1
  : (RelationGluingLeftN ∘Nv RelationGluingPairN) ≈N α.
Proof. intros X x. reflexivity. Defined.

(** The right projection recovers the second natural map. *)

(** 右投影恢复第二个自然映射。 *)

Definition relation_gluing_pair_β2
  : (RelationGluingRightN ∘Nv RelationGluingPairN) ≈N β.
Proof. intros X x. reflexivity. Defined.

(** Both projection equations suffice for mediator uniqueness. This
    compares the stored values, never the relation witnesses. *)

(** 两个投影方程足以保证中介唯一；比较保存的值，不比较关系见证。 *)

Definition relation_gluing_pair_unique (k : H ⇒ RelationGluingF)
    (left : (RelationGluingLeftN ∘Nv k) ≈N α)
    (right : (RelationGluingRightN ∘Nv k) ≈N β)
  : k ≈N RelationGluingPairN.
Proof.
  intros X x.
  assert (joint : ∀ p : RelationGluingS X,
    fst p.1 ≈S α X x → snd p.1 ≈S β X x →
    p ≈S RelationGluingPairN X x).
  { intros [[y z] h] hl hr. exact (hl, hr). }
  exact (joint (k X x) (left X x) (right X x)).
Defined.

(** The full lifting property chooses a mediator with both projection
    equations and its uniqueness. Chosen relatedness is retained by the
    mediator; no uniqueness of that evidence is part of the property. *)

(** 完整提升性质选取具有两个投影方程及唯一性的中介。选定关联见证由中介
    保留；该性质不要求这些证据唯一。 *)

Definition relation_gluing_universal
  : ∃ k : H ⇒ RelationGluingF, is_unique (R := NatEq)
      (λ k, (RelationGluingLeftN ∘Nv k) ≈N α ∧
        (RelationGluingRightN ∘Nv k) ≈N β) k.
Proof.
  exists RelationGluingPairN.
  refine {|this := (relation_gluing_pair_β1, relation_gluing_pair_β2)
          ; that := _
          |}.
  intros k [hl hr]. exact (relation_gluing_pair_unique k hl hr).
Defined.

End RelatedMaps.
End RelationGluing.
