From Cats Require Export
  Cat.Gluing.Core
  Cat.Fibration.
From Cats Require Import
  Cat.Arrow.Core
  Cat.Arrow.Fibration
  Cat.Pullback.

(** * Fibred Gluing

    The base projection of gluing has cartesian arrows exactly when the
    underlying squares are pullbacks. The forward construction reuses the
    cartesian factorization of the arrow category. The converse tests a
    cone by making it a gluing object over the source base.

    No product, terminal object, CCC or preservation condition is needed.
    Choosing the required pullbacks then supplies explicit cartesian lifts;
    neither those choices nor arbitrary target pullbacks are automatic. *)

(** * 纤维化的粘合

    粘合基投影的笛卡尔箭头恰好对应底层拉回方形。正向构造复用箭头范畴的
    笛卡尔分解；反向把待测锥作为源基对象上的粘合对象。

    不需要积、终对象、CCC 或保持性条件。选定所需拉回后得到显式笛卡尔
    提升；这些选择及目标的任意拉回均不会自动启用。 *)

(** The original natural structure arrow already defines the diagram
    functor into the arrow category. No square representation is rebuilt. *)

(** 原有自然结构箭头已经确定取值于箭头范畴的图式函子，不重建方形表示。 *)

Definition GluingDiagramF {C D : Cat} (F : Fct C D)
  : Fct (Gluing F) (Arr D)
  := NatArrowF (GluingArrowN F).

(** ** Candidate Cartesian Squares

    Fix an arbitrary functor and a gluing square. All hom equalities use
    their native setoids. Pullback and cartesian witnesses retain their
    mediators, without identifying their law or commutativity proofs. *)

(** ** 候选笛卡尔方形

    固定任意函子及粘合方形。全部 Hom 相等使用各自原生广集；拉回与笛卡尔
    见证保留其中介，不等同定律或交换性的证明。 *)

Section CartesianSquares.
Context {C D : Cat} (F : Fct C D).
Context {X Y : Gluing F} (f : Hom X Y).

(** A target pullback factors gluing squares through the original
    arrow-category cartesian mediator. Only its top side is extracted;
    the base side is the prescribed arrow in [C]. *)

(** 目标拉回通过原箭头范畴笛卡尔中介分解粘合方形。只提取中介顶边；基边
    使用 [C] 中给定的箭头。 *)

Definition gluing_pullback_cartesian
    (HP : is_pullback (fmap F (comma_right f)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left f))
  : f ⦂ Cart(GluingRightF F).
Proof.
  pose (Af := fmap (GluingDiagramF F) f).
  pose (HA := arrow_pullback_cartesian Af HP).
  intros Z g u H.
  assert (Himage : fmap (ArrowCodF D) Af ∘ fmap F u ≈
      fmap (ArrowCodF D) (fmap (GluingDiagramF F) g)).
  { change (fmap F (comma_right f) ∘ fmap F u ≈
      fmap F (comma_right g)).
    rewrite <- functor_comp. apply functor_fmap_proper. exact H. }
  pose (a := cartesian_factor HA (fmap (GluingDiagramF F) g)
    (fmap F u) Himage).
  assert (square : fmap F u ∘ comma_arrow Z ≈
      comma_arrow X ∘ arrow_top a).
  { rewrite <- (cartesian_factor_base HA
      (fmap (GluingDiagramF F) g) (fmap F u) Himage).
    symmetry. exact (arrow_comm a). }
  pose (h := ({|comma_left := arrow_top a
              ; comma_right := u
              ; comma_comm := square
              |} : (@Hom (Gluing F)) Z X)).
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - split; [reflexivity |]. split.
    + exact (fst (cartesian_factor_comp HA
        (fmap (GluingDiagramF F) g) (fmap F u) Himage)).
    + exact H.
  - intros k [Hbase Hcomp].
    assert (Hk : fmap (GluingDiagramF F) k ≈ a).
    { apply (that _ _ (cartesian_factor_unique HA
        (fmap (GluingDiagramF F) g) (fmap F u) Himage)).
      split.
      - change (fmap F (comma_right k) ≈ fmap F u).
        exact (@functor_fmap_proper C D F _ _ _ _ Hbase).
      - change (fmap (GluingDiagramF F) f ∘
          fmap (GluingDiagramF F) k ≈ fmap (GluingDiagramF F) g).
        rewrite <- functor_comp.
        exact (@functor_fmap_proper _ _ (GluingDiagramF F) _ _ _ _ Hcomp). }
    exact (fst Hk, Hbase).
Defined.

(** Every target cone can be regarded as a gluing object over the source
    base. Its cartesian factor over identity supplies the pullback mediator;
    no fullness or faithfulness of [F] is required. *)

(** 每个目标锥都可视为源基对象上的粘合对象。其恒等基边之上的笛卡尔分解
    给出拉回中介；不要求 [F] 满或忠实。 *)

Definition gluing_cartesian_pullback (Hf : f ⦂ Cart(GluingRightF F))
  : is_pullback (fmap F (comma_right f)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left f).
Proof.
  split; [exact (comma_comm f) |].
  intros Q q1 q2 Hq.
  pose (Z := (ltac:(refine
    {|comma_left_ob := Q
    ; comma_right_ob := comma_right_ob X
    ; comma_arrow := _
    |}; exact q1) : Gluing F)).
  pose (g := (ltac:(unshelve refine
    {|comma_left := _
    ; comma_right := _
    ; comma_comm := _
    |}; [exact q2 | exact (comma_right f) | exact Hq])
      : (@Hom (Gluing F)) Z Y)).
  assert (Hbase : fmap (GluingRightF F) f ∘ id ≈
      fmap (GluingRightF F) g) by (apply comp_id_r).
  pose (h := cartesian_factor Hf g id Hbase).
  pose proof (cartesian_factor_base Hf g id Hbase) as Hb.
  change (comma_right h ≈ id) in Hb.
  exists (comma_left h). refine {|this := _
                                ; that := _
                                |}.
  - split.
    + transitivity (fmap F (comma_right h) ∘ q1).
      * symmetry. exact (comma_comm h).
      * transitivity (fmap F id ∘ q1).
        -- apply comp_proper.
           ++ exact (@functor_fmap_proper C D F _ _ _ _ Hb).
           ++ reflexivity.
        -- transitivity (id ∘ q1).
           ++ apply comp_proper; [apply functor_id | reflexivity].
           ++ apply comp_id_l.
    + exact (fst (cartesian_factor_comp Hf g id Hbase)).
  - intros k [H1 H2].
    assert (square : fmap F id ∘ q1 ≈ comma_arrow X ∘ k).
    { rewrite functor_id, comp_id_l. symmetry. exact H1. }
    pose (l := (ltac:(unshelve refine
      {|comma_left := _
      ; comma_right := _
      ; comma_comm := _
      |}; [exact k | exact id | exact square]) : (@Hom (Gluing F)) Z X)).
    assert (Hl : fmap (GluingRightF F) l ≈ id ∧ f ∘ l ≈ g).
    { split; [reflexivity |]. split; [exact H2 | apply comp_id_r]. }
    exact (fst (that _ _ (cartesian_factor_unique Hf g id Hbase) l Hl)).
Defined.

(** This equivalence is candidate-level and needs no chosen pullbacks. *)

(** 此等价位于候选层，不需要选定拉回。 *)

Definition gluing_cartesian_iff_pullback
  : f ⦂ Cart(GluingRightF F) ↔
    is_pullback (fmap F (comma_right f)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left f)
  := (gluing_cartesian_pullback, gluing_pullback_cartesian).

End CartesianSquares.

(** ** One Supplied Pullback Cone

    Fix a gluing object [Y], a base arrow into its base, and a candidate
    pullback cone in [D]. This construction needs only that cone's universal
    property; there is no global choice of pullbacks. *)

(** ** 一个给定的拉回锥

    固定粘合对象 [Y]、指向其基对象的箭头及 [D] 中的候选拉回锥。构造只需要
    此锥的泛性质，不需要全局选定拉回。 *)

Section CandidateLift.
Context {C D : Cat} (F : Fct C D) (Y : Gluing F).
Context {A : C} (σ : Hom A (comma_right_ob Y)).
Context (R : D) (r : Hom R (F A)) (v : Hom R (comma_left_ob Y)).
Context (HP : is_pullback (fmap F σ) (comma_arrow Y) R r v).

(** The first projection is the new structure arrow over [A]. *)

(** 第一个投影是 [A] 上的新结构箭头。 *)

Program Definition GluingPullbackOb
  : Gluing F
  :=
  {|comma_left_ob := R
  ; comma_right_ob := A
  ; comma_arrow := _
  |}.
Next Obligation. exact r. Defined.

(** The second projection and original base arrow form the lifting square. *)

(** 第二个投影与原基箭头组成提升方形。 *)

Program Definition gluing_pullback_lift
  : (@Hom (Gluing F)) GluingPullbackOb Y
  :=
  {|comma_left := v
  ; comma_right := σ
  |}.
Next Obligation. exact (fst HP). Defined.

(** Its cartesianness is the candidate theorem just proved. *)

(** 其笛卡尔性就是上述候选定理。 *)

Definition gluing_pullback_lift_cartesian
  : gluing_pullback_lift ⦂ Cart(GluingRightF F)
  := gluing_pullback_cartesian F gluing_pullback_lift HP.

End CandidateLift.

(** ** Explicitly Chosen Lifts

    Supply only the pullbacks along images of base arrows into structure
    arrows. Each witness includes the vertex, projections and universal
    mediator. The chosen-lift interface keeps the new base definitionally
    equal to the supplied base object. *)

(** ** 显式选定提升

    只给出沿基箭头像拉回结构箭头所需的拉回。每个见证包含顶点、投影及泛
    中介；选定提升接口使新基对象与给定基对象定义相等。 *)

Section ChosenLifts.
Context {C D : Cat} (F : Fct C D).
Context (pullbacks : ∀ (Y : Gluing F) (A : C)
    (σ : Hom A (comma_right_ob Y)),
    ∃ R : D, ∃ r : Hom R (F A), ∃ v : Hom R (comma_left_ob Y),
      is_pullback (fmap F σ) (comma_arrow Y) R r v).

(** Only this supplied family is used. Importing the module enables no
    choice or fibration instance. *)

(** 只使用这个给定族；导入模块不启用任何选择或纤维化实例。 *)

Program Definition GluingRightF_HasCartLift
  : HasCartLift (GluingRightF F)
  :=
  {|CartLift Y A σ := GluingPullbackOb F
      (pullbacks Y A σ).1 (pullbacks Y A σ).2.1
  ; cartesian_lift_base Y A σ := eq_refl
  ; cartesian_lift Y A σ := gluing_pullback_lift F Y σ
      (pullbacks Y A σ).1 (pullbacks Y A σ).2.1
      (pullbacks Y A σ).2.2.1 (pullbacks Y A σ).2.2.2
  |}.
Next Obligation. symmetry. apply comp_id_r. Defined.
Next Obligation. apply gluing_pullback_lift_cartesian. Defined.

End ChosenLifts.

(** All chosen target pullbacks give the required family as a convenience.
    This stronger input is not required by the candidate theorem. *)

(** 目标的全部选定拉回可便捷地提供所需族；候选定理不要求这个更强输入。 *)

Definition GluingRightF_PullbackHasCartLift {C D : Cat}
    (F : Fct C D) `{HP : !HasPullback D}
  : HasCartLift (GluingRightF F)
  := GluingRightF_HasCartLift F (λ Y A σ,
      (Pb (fmap F σ) (comma_arrow Y);
        (pb1 _ _; (pb2 _ _; pullback_universal)))).
