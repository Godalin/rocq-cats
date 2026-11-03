From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Diagram.Reindex
  Cat.Shape.Finite
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift.

(** * Cone Presheaves and Shape Restriction *)

(** * 锥预层与形状限制 *)

(** Cones at a fixed apex are the existing hom-setoid of transformations
    from the constant diagram. Equality is [NatEq]. *)

(** 固定顶点的锥就是从常图式出发的自然变换 Hom 广集；相等为 [NatEq]。 *)

Definition ConeS {J C : Cat} (D : Functor J C) (X : @Ob C)
  : SetC
  := @HomSet (Fct J C) (ConstF J X) D.

(** Precomposition in the apex is the contravariant hom functor restricted
    along the diagonal. Independent ambient bounds allow different shape
    sizes in the same set category; functor laws are inherited. *)

(** 顶点预合成就是反变 Hom 函子沿对角函子的限制。独立环境上界允许不同大小的
    形状取值于同一集合范畴；函子律直接继承。 *)

Definition ConeF@{u p +} {J C : Cat} (D : Functor J C)
  : Functor (C^op) SetCat@{u p _ _ _ _ _}
  := LiftF ∘F (@ℎ2F (Fct J C) D ∘F (Δ[J,C])^opF).

Notation "'Cone(-,' D ')'" := (ConeF D) : cat_scope.

(** Restriction is a respectful map between native cone sets, even when
    their carrier and equality levels differ. *)

(** 即使两侧载体及相等层级不同，限制也是原生锥广集间的保相等映射。 *)

Program Definition cone_restrict_resp {I J C : Cat} (Q : Functor I J)
    {D : Functor J C} {X}
  : ConeS D X →r ConeS (D ∘F Q) X
  :=
  {|func κ := κ ∘Δ Q
  ; func_proper := @cone_restrict_proper I J C Q D X
  |}.

(** Extension reuses the original representative-based cone extension. *)

(** 延拓复用原来基于代表的锥延拓。 *)

Program Definition cone_extend_resp {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Functor J C} {X}
  : ConeS (D ∘F Q) X →r ConeS D X
  :=
  {|func := ExtendCone HF HQ
  ; func_proper := @cone_extend_proper I J C Q HF HQ D X
  |}.

(** Apex naturality is exactly the existing restriction/precomposition law;
    restriction itself requires no fullness or essential surjectivity. *)

(** 顶点自然性恰为已有的限制与预合成相容律；限制本身不要求满性或本质满性。 *)

Program Definition ConeRestrictN {I J C : Cat}
    (Q : Functor I J) (D : Functor J C)
  : Cone(-,D) ⇒ Cone(-,D ∘F Q)
  :=
  {|nt X := (cone_restrict_resp Q)^↑S
  |}.
Next Obligation.
  intros [κ]. refine {|lower := _
                      |}. apply cone_restrict_comp.
Qed.

(** Full, essentially surjective restriction is a natural setoid isomorphism.
    Its inverse components are the original extension maps and both inverse
    equations are the existing [NatEq] round-trip laws. *)

(** 满且本质满的限制是自然广集同构；逆分量为原延拓映射，两条互逆方程就是已有的
    [NatEq] 往返定律。 *)

Definition cone_reindex_nat_iso {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q) (D : Functor J C)
  : Cone(-,D) ≅N Cone(-,D ∘F Q).
Proof.
  exists (ConeRestrictN Q D). intros X.
  exists ((cone_extend_resp HF HQ)^↑S). split.
  - intros [κ]. refine {|lower := _
                        |}. apply cone_extend_restrict.
  - intros [κ]. refine {|lower := _
                        |}. apply cone_restrict_extend.
Defined.

(** The fixed-apex isomorphism is a component of the natural isomorphism.
    The lifts only place both native cone sets at common size bounds. *)

(** 固定顶点同构就是自然同构的分量；提升仅将两侧原生锥广集放到共同大小上界。 *)

Definition cone_reindex_iso@{u p +} {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    (D : Functor J C) (X : @Ob C)
  : LiftS@{_ _ u p} (ConeS D X) ≅[SetCat]
      LiftS@{_ _ u p} (ConeS (D ∘F Q) X)
  := ((ConeRestrictN Q D) X; (cone_reindex_nat_iso HF HQ D).2 X).

(** Inverse naturality follows from the general inverse-transformation
    theorem, using the selected extension maps as components. *)

(** 逆方向自然性由一般逆自然变换定理导出，分量使用选定延拓映射。 *)

Definition ConeExtendN {I J C : Cat} {Q : Functor I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q) (D : Functor J C)
  : Cone(-,D ∘F Q) ⇒ Cone(-,D)
  := (ConeRestrictN Q D)^-1N (cone_reindex_nat_iso HF HQ D).2.

(** Every finitely generated shape has the same cone presheaf as its chosen
    generating graph interpretation. No faithfulness or list of relations
    is required. *)

(** 有限生成形状与其选定生成图解释具有自然同构的锥预层；不要求忠实性或关系列表。 *)

Definition generated_cone_nat_iso {J C : Cat}
    `{HG : !HasFiniteGenerators J} (D : Functor J C)
  : Cone(-,D) ≅N Cone(-,D ∘F generator_functor)
  := cone_reindex_nat_iso generator_full generator_essentially_surjective D.
