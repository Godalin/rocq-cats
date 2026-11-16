From Cats Require Export
  Instance.Set.PresheafRegion.
From Cats Require Import
  Cat.Core.

(** * A Union is the Pushout of its Overlap

    Two equality-invariant regions have an actual union presheaf. Maps
    from the two regions glue when they agree on their intersection.
    The mediator below is the existing representable-generator descent,
    applied to all elements of both regions. No choice of representatives,
    quotient axioms or selected pushout model is required.

    This proves a categorical pushout in the existing opposite-pullback
    interface. The triangle-horn stages will be a later specialization;
    no horn attachment or cylinder extension is asserted by this module. *)

(** * 并是沿交叠的推出

    两个保持指定相等的区域有实际的并预层。来自两个区域的映射在交上一致时
    可以粘合。下述中介就是已有可表生成元下降，应用于两个区域的全部元素。
    不要求代表选择、商公理或选定推出模型。

    此处按已有反拉回接口证明范畴推出。三角 horn 阶段是后续特化，本模块
    不声称已构造 horn 附着或柱延拓。 *)

(** All arrows in this square are actual natural transformations.
    The square commutes in specified natural equality, and compatible
    maps out of its two sides have the transparent descended mediator. *)

(** 图中箭头都是实际自然变换；方形按指定自然相等交换。来自两边的相容映射
    具有透明的下降中介。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
R\cap S \arrow[r] \arrow[d] & R \arrow[d]
  \arrow[ddr,bend left=25,"a"] & \\
S \arrow[r] \arrow[drr,bend right=20,"b"'] & R\cup S
  \arrow[dr,dashed,"{\mathrm{descend}}"] & \\
&& P
\end{tikzcd}
\end{center}%
*)

(** ** Generators of the Union

    Fix an arbitrary index category, independent value bounds, an ambient
    presheaf and two regions whose membership data fit the value carrier.
    The generator index may be larger than that carrier. *)

(** ** 并的生成元

    固定任意指标范畴、独立取值界、环境预层及隶属数据可容纳于载体的两个区域。
    生成元指标本身可以大于该载体。 *)

Section UnionPushout.
Universes u p.
Context {C : Cat} {Q : Fct (C^op) SetCat@{u p _ _ _ _ _}}.
Context (R : PresheafRegion Q).
Context (S : PresheafRegion Q).

Let I
  : Type
  := ((∃ X : @Ob C, RegionPsh R X) +
      (∃ X : @Ob C, RegionPsh S X))%type.

Let D (i : I)
  : @Ob C
  := match i with inl x => x.1 | inr x => x.1 end.

(** Each element of either side is a representable generator of the union. *)

(** 任一侧的每个元素都是并的可表生成元。 *)

Definition region_union_generator (i : I)
  : RegionPsh (RegionUnion R S) (D i).
Proof.
  destruct i as [[X x] | [X x]].
  - exact (RegionUnionLeftN R S X x).
  - exact (RegionUnionRightN R S X x).
Defined.

(** The retained union alternative computes an actual cover at identity. *)

(** 保留的并分支在恒等算子处计算实际覆盖。 *)

Definition region_union_cover
  : is_presheaf_cover region_union_generator.
Proof.
  intros X [x [H | H]].
  - exists (inl (X; (x; H))), (id : (@Hom C) X X).
    change (fmap Q (id : (@Hom C) X X) x ≈S x). exact (functor_id _ _ Q x).
  - exists (inr (X; (x; H))), (id : (@Hom C) X X).
    change (fmap Q (id : (@Hom C) X X) x ≈S x). exact (functor_id _ _ Q x).
Defined.

Context {P : Fct (C^op) SetCat@{u p _ _ _ _ _}}.

(** The values are exactly the given maps, with no extra new values. *)

(** 取值恰是给定映射，不引入额外新值。 *)

Definition region_union_values (a : RegionPsh R ⇒ P) (b : RegionPsh S ⇒ P)
    (i : I)
  : P (D i).
Proof. destruct i as [[X x] | [X x]]; [exact (a X x) | exact (b X x)]. Defined.

(** Agreement on the actual intersection gives compatibility on all
    common representable factors. Membership is transported by specified
    equality; no equality of the transported witnesses is needed. *)

(** 在实际交上一致给出全部共同可表因子上的相容性。隶属按指定相等运输，
    无需比较运输见证相等。 *)

Definition region_union_compatible (a : RegionPsh R ⇒ P) (b : RegionPsh S ⇒ P)
    (H : (a ∘Nv RegionInterLeftN R S) ≈N (b ∘Nv RegionInterRightN R S))
  : presheaf_values_compatible region_union_generator (region_union_values a b).
Proof.
  intros X [[Y x] | [Y x]] [[Z y] | [Z y]] f g E.
  - transitivity (a X (fmap (RegionPsh R) f x)).
    + symmetry. exact (nat_naturality a f x).
    + transitivity (a X (fmap (RegionPsh R) g y)).
      * apply func_proper. exact E.
      * exact (nat_naturality a g y).
  - pose (K := snd (region_member_proper S _ _ E)
      (region_precomp S g y.1 y.2)).
    pose (z := (fmap Q f x.1; (region_precomp R f x.1 x.2, K))
      : RegionPsh (RegionIntersection R S) X).
    transitivity (a X (fmap (RegionPsh R) f x)).
    + symmetry. exact (nat_naturality a f x).
    + transitivity (a X (RegionInterLeftN R S X z)).
      * apply func_proper. reflexivity.
      * transitivity (b X (RegionInterRightN R S X z)).
        -- exact (H X z).
        -- transitivity (b X (fmap (RegionPsh S) g y)).
           ++ apply func_proper. exact E.
           ++ exact (nat_naturality b g y).
  - pose (K := snd (region_member_proper R _ _ E)
      (region_precomp R g y.1 y.2)).
    pose (z := (fmap Q f x.1; (K, region_precomp S f x.1 x.2))
      : RegionPsh (RegionIntersection R S) X).
    transitivity (b X (fmap (RegionPsh S) f x)).
    + symmetry. exact (nat_naturality b f x).
    + transitivity (b X (RegionInterRightN R S X z)).
      * apply func_proper. reflexivity.
      * transitivity (a X (RegionInterLeftN R S X z)).
        -- symmetry. exact (H X z).
        -- transitivity (a X (fmap (RegionPsh R) g y)).
           ++ apply func_proper. exact E.
           ++ exact (nat_naturality a g y).
  - transitivity (b X (fmap (RegionPsh S) f x)).
    + symmetry. exact (nat_naturality b f x).
    + transitivity (b X (fmap (RegionPsh S) g y)).
      * apply func_proper. exact E.
      * exact (nat_naturality b g y).
Defined.

(** Reuse descent for the actual cover and overlap compatibility. *)

(** 对实际覆盖及交叠相容性复用下降。 *)

Definition RegionUnionGluingN (a : RegionPsh R ⇒ P) (b : RegionPsh S ⇒ P)
    (H : (a ∘Nv RegionInterLeftN R S) ≈N (b ∘Nv RegionInterRightN R S))
  : RegionPsh (RegionUnion R S) ⇒ P
  := PresheafDescendN region_union_generator region_union_cover
      (region_union_values a b) (region_union_compatible a b H).

(** Restriction to the left side recovers its prescribed map. *)

(** 限制到左侧恢复其给定映射。 *)

Definition region_union_gluing_β1 (a : RegionPsh R ⇒ P) (b : RegionPsh S ⇒ P)
    (H : (a ∘Nv RegionInterLeftN R S) ≈N (b ∘Nv RegionInterRightN R S))
  : (RegionUnionGluingN a b H ∘Nv RegionUnionLeftN R S) ≈N a.
Proof.
  intros X x.
  exact (presheaf_descend_β region_union_generator region_union_cover
    (region_union_values a b) (region_union_compatible a b H) (inl (X; x))).
Defined.

(** Restriction to the right side recovers its prescribed map. *)

(** 限制到右侧恢复其给定映射。 *)

Definition region_union_gluing_β2 (a : RegionPsh R ⇒ P) (b : RegionPsh S ⇒ P)
    (H : (a ∘Nv RegionInterLeftN R S) ≈N (b ∘Nv RegionInterRightN R S))
  : (RegionUnionGluingN a b H ∘Nv RegionUnionRightN R S) ≈N b.
Proof.
  intros X x.
  exact (presheaf_descend_β region_union_generator region_union_cover
    (region_union_values a b) (region_union_compatible a b H) (inr (X; x))).
Defined.

(** Equal side maps give equal mediators with independently supplied
    agreement witnesses. Reuse descent's respectfulness on generator values. *)

(** 两侧映射相等就给出相等中介，允许独立的相容见证；复用下降对生成元取值
    的保相等性质。 *)

Definition region_union_gluing_proper
    (a a' : RegionPsh R ⇒ P) (b b' : RegionPsh S ⇒ P)
    (H : (a ∘Nv RegionInterLeftN R S) ≈N (b ∘Nv RegionInterRightN R S))
    (K : (a' ∘Nv RegionInterLeftN R S) ≈N (b' ∘Nv RegionInterRightN R S))
    (E : a ≈N a') (F : b ≈N b')
  : RegionUnionGluingN a b H ≈N RegionUnionGluingN a' b' K.
Proof.
  apply presheaf_descend_proper.
  intros [[X x] | [X x]]; [exact (E X x) | exact (F X x)].
Defined.

End UnionPushout.

(** The existing pushout predicate is instantiated by the descended
    mediator and its original generator uniqueness. All targets at the
    same ambient value sizes are allowed. *)

(** 以原下降中介及生成元唯一性实例化已有推出谓词；允许同一环境取值大小下的
    任意目标。 *)

Definition region_union_pushout@{u p +} {C : Cat}
    {Q : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    (R : PresheafRegion Q) (S : PresheafRegion Q)
  : is_pushout (C := FctCat (C^op) SetCat@{u p _ _ _ _ _})
      (RegionInterLeftN R S) (RegionInterRightN R S)
      (RegionPsh (RegionUnion R S)) (RegionUnionLeftN R S) (RegionUnionRightN R S).
Proof.
  split.
  - intros X x. change (x.1 ≈S x.1). reflexivity.
  - intros P a b H. exists (RegionUnionGluingN R S a b H).
    refine {|this := (region_union_gluing_β1 R S a b H,
                      region_union_gluing_β2 R S a b H)
            ; that := _
            |}.
    intros k [E F].
    apply (snd (presheaf_cover_map_eq (region_union_generator R S)
      (region_union_cover R S) k (RegionUnionGluingN R S a b H))).
    intros [[X x] | [X x]].
    + transitivity (a X x); [exact (E X x) |].
      symmetry. exact (region_union_gluing_β1 R S a b H X x).
    + transitivity (b X x); [exact (F X x) |].
      symmetry. exact (region_union_gluing_β2 R S a b H X x).
Defined.
