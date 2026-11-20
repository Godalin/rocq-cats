From Cats Require Export
  Cat.Gluing.Fibration
  Cat.Slice.Core
  Cat.Slice.Reindex.
From Cats Require Import
  Cat.Pullback.

(** * Slice Presentations and Reindexing of Gluing

    At a fixed base object [A], use the existing slice [D /C F A] as the
    category of structure arrows. Its inclusion into gluing keeps the base
    map equal to identity. Conversely, a gluing square whose base is
    specified-equal to identity gives a slice map.

    Chosen target pullbacks provide reindexing along [fmap F f]. The
    identity and composition laws of [F] are explicit boundaries: they
    induce comparison isomorphisms, not equality of chosen pullback
    objects. All slice mediators and inverse witnesses are reused. This
    convenience layer does not strengthen the weaker supplied-family lift
    theorem, and introduces no general split-fibration interface. Sizes
    follow the existing [Slice] interface: its hom carrier uses the target
    law bound, without identifying native target hom/equality levels. *)

(** * 粘合的切片表示与重索引

    在固定基对象 [A] 处，以既有切片 [D /C F A] 表示结构箭头范畴。其到粘合
    的包含把基映射保持为恒等；反之，基边指定等于恒等的粘合方形给出切片映射。

    目标选定拉回给出沿 [fmap F f] 的重索引。[F] 的恒等与复合律是显式边界，
    诱导比较同构，而非选定拉回对象的相等。切片中介及逆见证均予复用。此便捷
    层不加强较弱的给定族提升定理，也不引入一般分裂纤维化接口。大小沿用
    既有 [Slice] 接口：其 Hom 载体使用目标律界，不合并原生目标 Hom／相等界。 *)

(** The fixed-base presentation is exactly the existing slice category. *)

(** 固定基对象的表示恰为既有切片范畴。 *)

Definition GluingFiber {C D : Cat} (F : Fct C D) (A : C)
  : Cat
  := D /C F A.

(** ** Inclusion and Identity-Base Squares

    Fix a functor and a base object. No limit or lifting choices are used
    to include the slice, recover vertical maps or compare their values. *)

(** ** 包含与恒等基边方形

    固定函子及基对象。不使用极限或提升选择，即可包含切片、恢复竖直映射并
    比较它们的值。 *)

Section FiberInclusion.
Context {C D : Cat} (F : Fct C D) (A : C).

(** Regard an arrow into [F A] as a gluing object over [A]. *)

(** 将指向 [F A] 的箭头看作 [A] 上的粘合对象。 *)

Definition GluingFiberInclusionOb (R : GluingFiber F A)
  : Gluing F
  := GluingPullbackOb F (slice_dom R) (slice_arrow R).

(** A slice triangle gives a square with an identity base side. *)

(** 切片三角形给出基边为恒等的方形。 *)

Program Definition gluing_fiber_inclusion_map {R S : GluingFiber F A}
    (h : Hom R S)
  : (@Hom (Gluing F)) (GluingFiberInclusionOb R)
      (GluingFiberInclusionOb S)
  :=
  {|comma_left := slice_map h
  ; comma_right := id
  |}.
Next Obligation.
  rewrite fmap_id, comp_id_l. symmetry. exact (slice_comm h).
Defined.

(** The inclusion keeps the original slice arrow action and equality. *)

(** 包含保留原有切片箭头作用与相等。 *)

Program Definition GluingFiberInclusionF
  : Fct (GluingFiber F A) (Gluing F)
  :=
  {|fobj := GluingFiberInclusionOb
  ; fmap R S := gluing_fiber_inclusion_map
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros h k H. exact (H, reflexivity _). Qed.
Next Obligation. split; reflexivity. Qed.
Next Obligation. split; [reflexivity | symmetry; apply comp_id_l]. Qed.

(** Equality of included squares reflects the original slice equality. *)

(** 包含方形的相等反映原切片相等。 *)

Definition gluing_fiber_inclusion_faithful
  : is_faithful GluingFiberInclusionF.
Proof. intros R S h k H. exact (fst H). Defined.

(** Recover the triangle from a square with specified identity base.
    This requires no equality between the commutativity witnesses. *)

(** 从基边指定等于恒等的方形恢复三角形，不要求交换性见证相等。 *)

Program Definition gluing_fiber_vertical_map {R S : GluingFiber F A}
    (h : (@Hom (Gluing F)) (GluingFiberInclusionOb R)
      (GluingFiberInclusionOb S)) (H : comma_right h ≈ id)
  : (@Hom (GluingFiber F A)) R S
  :=
  {|slice_map := comma_left h
  |}.
Next Obligation.
  transitivity (fmap F (comma_right h) ∘ slice_arrow R).
  - symmetry. exact (comma_comm h).
  - rewrite H, fmap_id, comp_id_l. reflexivity.
Defined.

(** Recovering a vertical square preserves both sides up to their specified
    equality; the base side need only be equal to identity. *)

(** 恢复竖直方形后，两边均按指定相等保持；基边只需等于恒等。 *)

Definition gluing_fiber_vertical_roundtrip {R S : GluingFiber F A}
    (h : (@Hom (Gluing F)) (GluingFiberInclusionOb R)
      (GluingFiberInclusionOb S)) (H : comma_right h ≈ id)
  : gluing_fiber_inclusion_map (gluing_fiber_vertical_map h H) ≈ h.
Proof. split; [reflexivity | symmetry; exact H]. Defined.

(** The other round trip retains the original underlying slice arrow. *)

(** 另一往返保留原切片底层箭头。 *)

Definition gluing_fiber_slice_roundtrip {R S : GluingFiber F A}
    (h : Hom R S)
    (H : comma_right (gluing_fiber_inclusion_map h) ≈ id)
  : slice_map (gluing_fiber_vertical_map (gluing_fiber_inclusion_map h) H)
      ≈ slice_map h.
Proof. reflexivity. Defined.

End FiberInclusion.

(** Read any gluing object in the slice over its own base. *)

(** 将任意粘合对象读取为其自身基对象之上的切片对象。 *)

Program Definition GluingFiberOb {C D : Cat} (F : Fct C D) (Y : Gluing F)
  : GluingFiber F (comma_right_ob Y)
  :=
  {|slice_dom := comma_left_ob Y
  ; slice_arrow := comma_arrow Y
  |}.

(** ** Reindexing through Target Pullbacks

    Fix chosen pullbacks only in [D]. All reindexing functors and their
    comparison mediators are the existing slice constructions. The
    gluing lift uses precisely the same pullback vertex and projections. *)

(** ** 经目标拉回重索引

    只在 [D] 中固定选定拉回。全部重索引函子及比较中介使用既有切片构造；
    粘合提升使用恰好同一拉回顶点及投影。 *)

Section Reindexing.
Context {C D : Cat} (F : Fct C D) `{HP : !HasPullback D}.

(** Reindex a fixed-base presentation along the image of a base map. *)

(** 沿基映射的像重索引固定基对象表示。 *)

Definition GluingFiberReindexF {A B : C} (f : Hom A B)
  : Fct (GluingFiber F B) (GluingFiber F A)
  := SliceReindexF (fmap F f).

(** The original gluing candidate supplies the cartesian lifting square. *)

(** 原粘合候选给出笛卡尔提升方形。 *)

Definition gluing_fiber_lift {A B : C} (f : Hom A B)
    (R : GluingFiber F B)
  : (@Hom (Gluing F))
      (GluingFiberInclusionF F A (GluingFiberReindexF f R))
      (GluingFiberInclusionF F B R)
  := gluing_pullback_lift F (GluingFiberInclusionF F B R) f
      (Pb (fmap F f) (slice_arrow R)) (pb1 _ _) (pb2 _ _)
      pullback_universal.

(** The lift is cartesian for the base projection, without preservation
    assumptions on [F]. *)

(** 提升对基投影笛卡尔，不要求 [F] 保持任何构造。 *)

Definition gluing_fiber_lift_cartesian {A B : C} (f : Hom A B)
    (R : GluingFiber F B)
  : (gluing_fiber_lift f R) ⦂ Cart(GluingRightF F)
  := gluing_pullback_lift_cartesian F (GluingFiberInclusionF F B R) f
      (Pb (fmap F f) (slice_arrow R)) (pb1 _ _) (pb2 _ _)
      pullback_universal.

(** The lifting squares are natural in fixed-base slice maps. *)

(** 提升方形在固定基对象切片映射上自然。 *)

Program Definition GluingFiberLiftN {A B : C} (f : Hom A B)
  : (GluingFiberInclusionF F A ∘F GluingFiberReindexF f)
      ⇒ GluingFiberInclusionF F B
  :=
  {|nt R := gluing_fiber_lift f R
  |}.
Next Obligation.
  split.
  - apply slice_reindex_map_β2.
  - change (f ∘ id ≈ id ∘ f).
    rewrite comp_id_l, comp_id_r. reflexivity.
Qed.

(** Equivalent base maps induce the old slice-equivalence comparison. *)

(** 等价基映射诱导原有切片相等比较。 *)

Definition GluingFiberReindexEqN {A B : C} {f g : Hom A B} (H : f ≈ g)
  : GluingFiberReindexF f ⇒ GluingFiberReindexF g
  := SliceReindexEqN (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ H).

(** This comparison is a natural isomorphism, not equality of functors. *)

(** 此比较为自然同构，而非函子相等。 *)

Definition gluing_fiber_reindex_equiv_iso {A B : C} {f g : Hom A B}
    (H : f ≈ g)
  : GluingFiberReindexF f ≅N GluingFiberReindexF g
  := (GluingFiberReindexEqN H;
      slice_reindex_equiv_iso (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ H)).

(** First compare identity reindexing in [D], then change its base arrow
    along the inverse identity law of [F]. *)

(** 先比较 [D] 中的恒等重索引，再沿 [F] 恒等律的逆方向改变基箭头。 *)

Definition GluingFiberReindexIdN (A : C)
  : (@IdF (GluingFiber F A)) ⇒ GluingFiberReindexF (id[A])
  := SliceReindexEqN (symmetry (@fmap_id _ _ _ _ (@isFct C D F) A)) ∘Nv
      SliceReindexIdN (F A).

(** The identity comparison retains the existing transparent inverse. *)

(** 恒等比较保留既有透明逆映射。 *)

Definition gluing_fiber_reindex_id_iso (A : C)
  : (@IdF (GluingFiber F A)) ≅N GluingFiberReindexF (id[A]).
Proof.
  exists (GluingFiberReindexIdN A). apply nat_comp_iso.
  - intro R. apply slice_reindex_equiv_iso.
  - intro R. apply slice_reindex_id_iso.
Defined.

(** The composite comparison includes the functor-composition boundary
    [fmap F f ∘ fmap F g ≈ fmap F (f ∘ g)]. *)

(** 复合比较包含函子复合边界
    [fmap F f ∘ fmap F g ≈ fmap F (f ∘ g)]。 *)

Definition GluingFiberReindexCompN {A B E : C} (f : Hom B E)
    (g : Hom A B)
  : (GluingFiberReindexF g ∘F GluingFiberReindexF f)
      ⇒ GluingFiberReindexF (f ∘ g)
  := SliceReindexEqN (symmetry (@fmap_comp _ _ _ _ (@isFct C D F) _ _ _ f g)) ∘Nv
      SliceReindexCompN (fmap F f) (fmap F g).

(** Its two factors are the existing slice isomorphisms. *)

(** 其两个因子均为既有切片同构。 *)

Definition gluing_fiber_reindex_comp_iso {A B E : C} (f : Hom B E)
    (g : Hom A B)
  : (GluingFiberReindexF g ∘F GluingFiberReindexF f)
      ≅N GluingFiberReindexF (f ∘ g).
Proof.
  exists (GluingFiberReindexCompN f g). apply nat_comp_iso.
  - intro R. apply slice_reindex_equiv_iso.
  - intro R. apply slice_reindex_comp_iso.
Defined.

(** ** Projection Equations of the Comparisons

    The second pullback projection characterizes each slice map. These
    equations reuse the original mediator laws, including independence
    from equality witnesses. They will also determine coherence. *)

(** ** 比较的投影方程

    第二拉回投影刻画每个切片映射。这些方程复用原中介律，包括对相等见证的
    独立性；它们也将确定相干性。 *)

(** The equality comparison preserves the second projection. *)

(** 相等比较保持第二投影。 *)

Definition gluing_fiber_reindex_equiv_β2 {A B : C} {f g : Hom A B}
    (H : f ≈ g) (R : GluingFiber F B)
  : pb2 (fmap F g) (slice_arrow R) ∘
      slice_map (GluingFiberReindexEqN H R) ≈
    pb2 (fmap F f) (slice_arrow R)
  := slice_reindex_equiv_β2 (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ H) R.

(** Identity comparison followed by its lifting projection is identity. *)

(** 恒等比较后接其提升投影得到恒等。 *)

Definition gluing_fiber_reindex_id_β2 (A : C) (R : GluingFiber F A)
  : pb2 (fmap F (id[A])) (slice_arrow R) ∘
      slice_map (GluingFiberReindexIdN A R) ≈ id.
Proof.
  change (pb2 (fmap F (id[A])) (slice_arrow R) ∘
    (slice_map (slice_reindex_equiv (symmetry (@fmap_id _ _ _ _ (@isFct C D F) A)) R)
      ∘ slice_map (slice_reindex_id R)) ≈ id).
  rewrite <- comp_assoc, slice_reindex_equiv_β2.
  apply slice_reindex_lift_β2.
Defined.

(** The composite comparison is characterized by the two original lifting
    projections, with no identification of their pullback objects. *)

(** 复合比较由两个原提升投影刻画，不等同它们的拉回对象。 *)

Definition gluing_fiber_reindex_comp_β2 {A B E : C} (f : Hom B E)
    (g : Hom A B) (R : GluingFiber F E)
  : pb2 (fmap F (f ∘ g)) (slice_arrow R) ∘
      slice_map (GluingFiberReindexCompN f g R) ≈
    pb2 (fmap F f) (slice_arrow R) ∘
      pb2 (fmap F g) (slice_arrow (GluingFiberReindexF f R)).
Proof.
  change (pb2 (fmap F (f ∘ g)) (slice_arrow R) ∘
    (slice_map (slice_reindex_equiv
      (symmetry (@fmap_comp _ _ _ _ (@isFct C D F) _ _ _ f g)) R) ∘
      slice_map (slice_reindex_comp (fmap F f) (fmap F g) R)) ≈
    pb2 (fmap F f) (slice_arrow R) ∘
      pb2 (fmap F g) (slice_arrow (GluingFiberReindexF f R))).
  rewrite <- comp_assoc, slice_reindex_equiv_β2.
  apply slice_reindex_lift_β2.
Defined.

(** Reindexing respects base hom equality by the specified natural
    isomorphism; it selects no additional pullbacks. *)

(** 重索引通过指定自然同构保持基底 Hom 相等，不另行选择拉回。 *)

Global Instance GluingFiberReindexF_proper {A B : C}
  : Proper (HomEq ==> NatIso) (@GluingFiberReindexF A B).
Proof. intros f g H. exact (gluing_fiber_reindex_equiv_iso H). Defined.

(** Different base-equivalence witnesses give equal transformations. *)

(** 不同基底相等见证给出相等的自然变换。 *)

Definition gluing_fiber_reindex_equiv_witness_independent {A B : C}
    {f g : Hom A B} (H K : f ≈ g)
  : GluingFiberReindexEqN H ≈N GluingFiberReindexEqN K
  := slice_reindex_equiv_witness_independent
      (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ H)
      (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ K).

(** A reflexive base comparison acts as identity in natural equality. *)

(** 自反基底比较在自然相等下作用为恒等。 *)

Definition gluing_fiber_reindex_equiv_id {A B : C} {f : Hom A B}
    (H : f ≈ f)
  : GluingFiberReindexEqN H ≈N IdN
  := slice_reindex_equiv_id (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ H).

(** Base-comparison composition is coherent without equating witnesses. *)

(** 基底比较的复合相干，不要求见证相等。 *)

Definition gluing_fiber_reindex_equiv_comp {A B : C}
    {f g h : Hom A B} (H : f ≈ g) (K : g ≈ h) (L : f ≈ h)
  : GluingFiberReindexEqN L ≈N
      (GluingFiberReindexEqN K ∘Nv GluingFiberReindexEqN H)
  := slice_reindex_equiv_comp
      (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ H)
      (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ K)
      (@fmap_proper _ _ _ _ (@isFct C D F) _ _ _ _ L).

(** Composition comparison respects specified equality of both base maps.
    The supplied composite boundary may be any witness of the same equation. *)

(** 复合比较保持两条基映射的指定相等；给定复合边界可为该方程的任意见证。 *)

Definition gluing_fiber_reindex_comp_equiv {A B E : C}
    {f f' : Hom B E} {g g' : Hom A B}
    (Hf : f ≈ f') (Hg : g ≈ g') (Hfg : f ∘ g ≈ f' ∘ g')
    (R : GluingFiber F E)
  : slice_map (GluingFiberReindexEqN Hfg R ∘/C
      GluingFiberReindexCompN f g R) ≈
    slice_map (GluingFiberReindexCompN f' g' R ∘/C
      GluingFiberReindexEqN Hg (GluingFiberReindexF f' R) ∘/C
      slice_reindex_map (fmap F g) (GluingFiberReindexEqN Hf R)).
Proof.
  apply (slice_reindex_hom_ext (fmap F (f' ∘ g')) R).
  change (pb2 (fmap F (f' ∘ g')) (slice_arrow R) ∘
    (slice_map (GluingFiberReindexEqN Hfg R) ∘
      slice_map (GluingFiberReindexCompN f g R)) ≈
    pb2 (fmap F (f' ∘ g')) (slice_arrow R) ∘
    ((slice_map (GluingFiberReindexCompN f' g' R) ∘
      slice_map (GluingFiberReindexEqN Hg (GluingFiberReindexF f' R))) ∘
      slice_map (slice_reindex_map (fmap F g)
        (GluingFiberReindexEqN Hf R)))).
  rewrite <- !(@comp_assoc D), gluing_fiber_reindex_equiv_β2,
    !gluing_fiber_reindex_comp_β2.
  symmetry.
  rewrite (comp_assoc (pb2 (fmap F f') (slice_arrow R))).
  rewrite (gluing_fiber_reindex_equiv_β2 Hg (GluingFiberReindexF f' R)).
  rewrite (comp_assoc (pb2 (fmap F f') (slice_arrow R))).
  rewrite (slice_reindex_map_β2 (fmap F g) (GluingFiberReindexEqN Hf R)).
  rewrite <- (@comp_assoc D).
  rewrite (gluing_fiber_reindex_equiv_β2 Hf R).
  reflexivity.
Defined.

(** ** Compatibility with Cartesian Lifts

    Include the comparison maps into gluing. Their projection equations
    show that they compare the original cartesian lifting arrows, not
    just unrelated slice objects. *)

(** ** 与笛卡尔提升的相容性

    将比较映射包含进粘合。其投影方程说明它们比较原来的笛卡尔提升箭头，而
    非只比较无关的切片对象。 *)

(** Identity reindexing followed by its comparison recovers identity. *)

(** 恒等重索引后接其比较，恢复恒等。 *)

Definition gluing_fiber_lift_id (A : C) (R : GluingFiber F A)
  : gluing_fiber_lift (id[A]) R ∘
      fmap (GluingFiberInclusionF F A) (GluingFiberReindexIdN A R) ≈ id.
Proof.
  split.
  - exact (gluing_fiber_reindex_id_β2 A R).
  - apply comp_id_l.
Defined.

(** The composite comparison identifies the two composite lifting paths. *)

(** 复合比较使两条复合提升路径相等。 *)

Definition gluing_fiber_lift_comp {A B E : C} (f : Hom B E)
    (g : Hom A B) (R : GluingFiber F E)
  : gluing_fiber_lift (f ∘ g) R ∘
      fmap (GluingFiberInclusionF F A) (GluingFiberReindexCompN f g R) ≈
    gluing_fiber_lift f R ∘
      gluing_fiber_lift g (GluingFiberReindexF f R).
Proof.
  split.
  - exact (gluing_fiber_reindex_comp_β2 f g R).
  - apply comp_id_r.
Defined.

(** ** Unit and Associativity Coherence

    Work pointwise in a fixed-base slice. Its original hom-extensionality
    theorem reduces each diagram to its second projection. The equations
    below include the source-category law boundary as supplied data; no
    equality of law witnesses or strict splitness is asserted. *)

(** ** 单位与结合相干性

    在固定基对象切片中逐点工作。原有 Hom 外延性定理将每个图约化为第二投影。
    下述方程保留源范畴定律边界作为给定数据；不声称定律见证相等或严格分裂。 *)

(** The left unit diagram includes both the functor identity comparison
    and the image of the supplied source left-unit equation. *)

(** 左单位图同时包含函子恒等比较及给定源左单位方程的像。 *)

Definition gluing_fiber_reindex_unit_l {A B : C} (f : Hom A B)
    (H : id ∘ f ≈ f) (R : GluingFiber F B)
  : slice_map (GluingFiberReindexEqN H R ∘/C
      GluingFiberReindexCompN id f R ∘/C
      slice_reindex_map (fmap F f) (GluingFiberReindexIdN B R)) ≈
    slice_map (slice_id (GluingFiberReindexF f R)).
Proof.
  apply (slice_reindex_hom_ext (fmap F f) R).
  change (pb2 (fmap F f) (slice_arrow R) ∘
    ((slice_map (GluingFiberReindexEqN H R) ∘
      slice_map (GluingFiberReindexCompN id f R)) ∘
      slice_map (slice_reindex_map (fmap F f)
        (GluingFiberReindexIdN B R))) ≈
    pb2 (fmap F f) (slice_arrow R) ∘ id).
  rewrite <- !(@comp_assoc D), gluing_fiber_reindex_equiv_β2,
    gluing_fiber_reindex_comp_β2.
  rewrite (comp_assoc (pb2 (fmap F (id[B])) (slice_arrow R))),
    (slice_reindex_map_β2 (fmap F f) (GluingFiberReindexIdN B R)),
    <- comp_assoc,
    gluing_fiber_reindex_id_β2, comp_id_l, comp_id_r. reflexivity.
Defined.

(** The right unit diagram retains the corresponding source boundary. *)

(** 右单位图保留相应源边界。 *)

Definition gluing_fiber_reindex_unit_r {A B : C} (f : Hom A B)
    (H : f ∘ id ≈ f) (R : GluingFiber F B)
  : slice_map (GluingFiberReindexEqN H R ∘/C
      GluingFiberReindexCompN f id R ∘/C
      GluingFiberReindexIdN A (GluingFiberReindexF f R)) ≈
    slice_map (slice_id (GluingFiberReindexF f R)).
Proof.
  apply (slice_reindex_hom_ext (fmap F f) R).
  change (pb2 (fmap F f) (slice_arrow R) ∘
    ((slice_map (GluingFiberReindexEqN H R) ∘
      slice_map (GluingFiberReindexCompN f id R)) ∘
      slice_map (GluingFiberReindexIdN A (GluingFiberReindexF f R))) ≈
    pb2 (fmap F f) (slice_arrow R) ∘ id).
  rewrite <- !(@comp_assoc D), gluing_fiber_reindex_equiv_β2,
    gluing_fiber_reindex_comp_β2.
  rewrite (comp_assoc (pb2 (fmap F f) (slice_arrow R))),
    gluing_fiber_reindex_id_β2. reflexivity.
Defined.

(** The associativity diagram includes the image of the source associator
    boundary. Both paths have the same three lifting projections. *)

(** 结合图包含源结合律边界的像；两条路径具有相同的三个提升投影。 *)

Definition gluing_fiber_reindex_assoc {A B E L : C} (f : Hom E L)
    (g : Hom B E) (h : Hom A B)
    (H : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)) (R : GluingFiber F L)
  : slice_map (GluingFiberReindexEqN H R ∘/C
      GluingFiberReindexCompN (f ∘ g) h R ∘/C
      slice_reindex_map (fmap F h) (GluingFiberReindexCompN f g R)) ≈
    slice_map (GluingFiberReindexCompN f (g ∘ h) R ∘/C
      GluingFiberReindexCompN g h (GluingFiberReindexF f R)).
Proof.
  apply (slice_reindex_hom_ext (fmap F (f ∘ (g ∘ h))) R).
  change (pb2 (fmap F (f ∘ (g ∘ h))) (slice_arrow R) ∘
    ((slice_map (GluingFiberReindexEqN H R) ∘
      slice_map (GluingFiberReindexCompN (f ∘ g) h R)) ∘
      slice_map (slice_reindex_map (fmap F h)
        (GluingFiberReindexCompN f g R))) ≈
    pb2 (fmap F (f ∘ (g ∘ h))) (slice_arrow R) ∘
      (slice_map (GluingFiberReindexCompN f (g ∘ h) R) ∘
        slice_map (GluingFiberReindexCompN g h (GluingFiberReindexF f R)))).
  transitivity ((pb2 (fmap F f) (slice_arrow R) ∘
    pb2 (fmap F g) (slice_arrow (GluingFiberReindexF f R))) ∘
    pb2 (fmap F h)
      (slice_arrow (GluingFiberReindexF g (GluingFiberReindexF f R)))).
  - rewrite <- !(@comp_assoc D), gluing_fiber_reindex_equiv_β2,
      gluing_fiber_reindex_comp_β2.
    rewrite (comp_assoc (pb2 (fmap F (f ∘ g)) (slice_arrow R))),
      (slice_reindex_map_β2 (fmap F h) (GluingFiberReindexCompN f g R)),
      <- (@comp_assoc D), gluing_fiber_reindex_comp_β2. reflexivity.
  - symmetry. rewrite <- (@comp_assoc D), gluing_fiber_reindex_comp_β2.
    transitivity (pb2 (fmap F f) (slice_arrow R) ∘
      (pb2 (fmap F g) (slice_arrow (GluingFiberReindexF f R)) ∘
        pb2 (fmap F h)
          (slice_arrow (GluingFiberReindexF g (GluingFiberReindexF f R))))).
    + etransitivity; [exact (@comp_assoc D _ _ _ _ _ _ _) |].
      apply comp_l.
      exact (gluing_fiber_reindex_comp_β2 g h (GluingFiberReindexF f R)).
    + symmetry. exact (@comp_assoc D _ _ _ _ _ _ _).
Defined.

End Reindexing.
