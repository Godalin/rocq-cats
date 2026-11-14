From Cats Require Export
  Cat.Profunctor.Core
  Cat.Coend.Core.
From Cats Require Import
  Cat.Core
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope profunctor_scope.

(** * Composition through Specified Coends

    Compose [P] from [C] to [D] followed by [Q] from [D] to [E]. A
    representative consists of a [P] value followed by a [Q] value, sharing
    an intermediate object of [D]. Only coends of that particular kernel
    family are required. No strength or size-based existence is implicit. *)

(** * 通过指定 coend 复合

    先用从 [C] 到 [D] 的 [P]，再用从 [D] 到 [E] 的 [Q]。代表由一个 [P] 值及
    随后的 [Q] 值组成，共用 [D] 的中间对象。只要求这一特定核族的 coend，
    不隐含强度或由大小得到的存在性。 *)

(** Separate the contravariant [Q] index from the covariant [P] index.
    One-sided restrictions and pointwise products supply all functor laws. *)

(** 分离 [Q] 的逆变指标与 [P] 的协变指标；单侧限制及逐点积提供全部函子律。 *)

Definition ProfunctorCompKernel@{u p +} {C D E : Cat}
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
    (X : @Ob C) (Z : @Ob E)
  : Fct ((D^op) ×C D) (SetCat@{u p _ _ _ _ _})
  := @PointwiseProductF _ SetCat SetCat_HasProduct
      (π2F P X ∘F SndF (D^op) D) (π1F Q Z ∘F FstF (D^op) D).

(** ** Changing the Outer Boundaries

    Fix two composable profunctors. Input preprocessing acts on [P]; output
    postprocessing acts on [Q]. Their natural transformations are inherited
    from the existing single-coordinate comparisons and pointwise product. *)

(** ** 改变外部边界

    固定两个可复合 profunctor，输入预处理作用于 [P]，输出后处理作用于 [Q]。
    相应自然变换继承自已有单坐标比较及逐点积。 *)

Section Boundaries.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).

(** Reindex the two outer ends without changing the intermediate index. *)

(** 重索引外部两端，保持中间指标不变。 *)

Definition ProfunctorCompBoundaryN {X X' : @Ob C} {Z Z' : @Ob E}
    (f : Hom X' X) (g : Hom Z Z')
  : ProfunctorCompKernel Q P X Z ⇒ ProfunctorCompKernel Q P X' Z'
  := @PointwiseProductN _ SetCat SetCat_HasProduct _ _ _ _
      (ProfunctorLmapN P f ∘Nr SndF (D^op) D)
      (ProfunctorRmapN Q g ∘Nr FstF (D^op) D).

(** Boundary changes respect the two categories' specified arrow equality. *)

(** 边界改变保持两个范畴指定的箭头相等。 *)

Global Instance profunctor_comp_boundary_proper
    {X X' : @Ob C} {Z Z' : @Ob E}
  : Proper (@HomEq C X' X ==> @HomEq E Z Z' ==> NatEq)
      (@ProfunctorCompBoundaryN X X' Z Z').
Proof.
  intros f f' H g g' K [A B] [x y]. split.
  - exact (@profunctor_lmap_proper C D P B X X' f f' H x).
  - exact (@profunctor_rmap_proper D E Q A Z Z' g g' K y).
Defined.

(** Identity changes are the original one-sided identity maps. *)

(** 恒等改变就是原单侧恒等映射。 *)

Lemma profunctor_comp_boundary_id (X : @Ob C) (Z : @Ob E)
  : ProfunctorCompBoundaryN (@id X) (@id Z) ≈N idN.
Proof.
  intros [A B] [x y]. split.
  - exact (profunctor_lmap_id P X B x).
  - exact (profunctor_rmap_id Q A Z y).
Defined.

(** Outer composition reverses the input action and preserves output order. *)

(** 外部复合反转输入作用顺序，保持输出顺序。 *)

Lemma profunctor_comp_boundary_comp
    {X X' X'' : @Ob C} {Z Z' Z'' : @Ob E}
    (f : Hom X' X) (f' : Hom X'' X')
    (g : Hom Z Z') (g' : Hom Z' Z'')
  : ProfunctorCompBoundaryN (f ∘ f') (g' ∘ g) ≈N
      (ProfunctorCompBoundaryN f' g' ∘Nv ProfunctorCompBoundaryN f g).
Proof.
  intros [A B] [x y]. split.
  - exact (profunctor_lmap_comp P B f f' x).
  - exact (profunctor_rmap_comp Q A g g' y).
Defined.

End Boundaries.

(** Select only coends indexed by these outer boundaries. This is additional
    chosen data, not a global completeness or full self-indexing assumption. *)

(** 只选择由这些外部边界索引的 coend；这是额外选定数据，不是全局余完备或完整自索引假设。 *)

Class HasProfunctorComp@{u p +} (C D E : Cat)
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
  :=
  { hasProfunctorCompCoend (X : @Ob C) (Z : @Ob E)
      :: HasCoend (SetCat@{u p _ _ _ _ _}) (ProfunctorCompKernel Q P X Z)
  }.

(** ** The Composite Profunctor

    Assume just the indicated family of coends. The existing coend-map
    identity, composition and equality laws assemble the mixed-variance
    functor on the outer categories. *)

(** ** 复合 Profunctor

    只假设所指核族的 coend，利用已有 coend 映射的恒等、复合及相等定律，
    组装外部范畴上的混合变元函子。 *)

Section ChosenComposition.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HC : !HasProfunctorComp C D E Q P}.

(** The composite is written [Q] after [P]; representatives run [P] then [Q]. *)

(** 复合写作 [Q] 在 [P] 之后；代表的执行顺序为先 [P] 再 [Q]。 *)

Program Definition ProfunctorComp
  : Fct ((C^op) ×C E) (SetCat@{u p _ _ _ _ _})
  :=
  {|F0 XZ := coend[ProfunctorCompKernel Q P (fst XZ) (snd XZ)]
  ; F1 XZ XZ' fg := coend_map (ProfunctorCompBoundaryN Q P
      (fst fg) (snd fg))
  |}.
Next Obligation.
  intros [f g] [f' g'] [H K].
  apply (@coend_map_proper D SetCat).
  exact (@profunctor_comp_boundary_proper C D E Q P _ _ _ _ f f' H g g' K).
Defined.
Next Obligation.
  transitivity (coend_map (idN
    (F := ProfunctorCompKernel Q P (fst X) (snd X)))).
  - apply (@coend_map_proper D SetCat). apply profunctor_comp_boundary_id.
  - apply (@coend_map_id D SetCat).
Defined.
Next Obligation.
  transitivity (coend_map (ProfunctorCompBoundaryN Q P (fst f) (snd f)
    ∘Nv ProfunctorCompBoundaryN Q P (fst g) (snd g))).
  - apply (@coend_map_proper D SetCat). apply profunctor_comp_boundary_comp.
  - apply (@coend_map_comp D SetCat).
Defined.

End ChosenComposition.

Infix "∘Pr" := ProfunctorComp (at level 40, left associativity)
  : profunctor_scope.
