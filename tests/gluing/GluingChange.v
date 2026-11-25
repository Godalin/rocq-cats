From Cats Require Import
  Cat.Gluing.Change
  Cat.Pullback
  Cat.Morphism
  Cat.Diagram.Arrow
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Bool.Group.
From CatsTests.gluing Require Import
  Gluing
  GluingFibration.

(** * Model Change and Cartesian Gluing Images

    Strict category profiles check independent base/target levels through
    consecutive changes. Concrete arrow diagrams distinguish an incoming
    isomorphism from an outgoing monomorphism and test failure without the
    needed incoming inverse. No model choice is enabled globally. *)

(** * 模型变化与笛卡尔粘合像

    严格范畴配置检查连续变化中独立的基／目标层级。具体箭头图式区分入边界
    同构与出边界单态射，并检查缺少必要入边界逆时的失败。不全局启用模型选择。 *)

(** ** Independent Category Levels

    Fix six separate base/target categories and compatible changes.
    The candidate preservation theorem uses only the supplied image square. *)

(** ** 独立范畴层级

    固定六个分离的基／目标范畴及相容变化；候选保持定理只使用给定像方形。 *)

Section IndependentChange.
Universes
  o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5.
Constraint h0 < e0, e0 < o0, o0 < l0.
Constraint e1 < h1, h1 < o1, o1 < l1.
Constraint h2 < e2, e2 < o2, o2 < l2.
Constraint e3 < h3, h3 < o3, o3 < l3.
Constraint h4 < e4, e4 < o4, o4 < l4.
Constraint e5 < h5, h5 < o5, o5 < l5.
Constraint l0 < o1, l1 < o2, l2 < o3, l3 < o4, l4 < o5.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {C'' : Cat@{o4 h4 e4 l4 l4}}.
Context {D'' : Cat@{o5 h5 e5 l5 l5}}.
Context {F : Fct C D} {F' : Fct C' D'} {F'' : Fct C'' D''}.
Context (H : Fct C C') (K : Fct D D').
Context (H' : Fct C' C'') (K' : Fct D' D'').
Context (α : (K ∘F F) ⇒ (F' ∘F H))
    (β : (K' ∘F F') ⇒ (F'' ∘F H')).

(** The actual change functor accepts these strict boundaries. *)

(** 实际变化函子接受这些严格边界。 *)

Definition independent_gluing_change
  : Fct (Gluing F) (Gluing F')
  := GluingChangeF H K α.

(** Both projections retain their separate ambient categories. *)

(** 两个投影保持各自独立的环境范畴。 *)

Definition independent_gluing_projection
  : (GluingRightF F' ∘F GluingChangeF H K α) ≅N (H ∘F GluingRightF F)
  := gluing_change_base_iso H K α.

(** Composite compatibility uses all six category boundaries. *)

(** 复合相容性使用全部六个范畴边界。 *)

Definition independent_gluing_composite
  : (GluingChangeF H' K' β ∘F GluingChangeF H K α) ≅N
      GluingChangeF (H' ∘F H) (K' ∘F K)
        (GluingChangeCompBoundaryN H K H' K' α β)
  := gluing_change_comp_iso H K H' K' α β.

(** The cartesian image criterion retains only its local hypotheses. *)

(** 笛卡尔像判据只保留其局部假设。 *)

Definition independent_gluing_cartesian {X Y : Gluing F} (h : Hom X Y)
    (HP : is_pullback (fmap K (fmap F (comma_right h)))
      (fmap K (comma_arrow Y)) (K (comma_left_ob X))
      (fmap K (comma_arrow X)) (fmap K (comma_left h)))
    (Hi : is_iso (α (comma_right_ob X)))
    (Hj : is_mono (α (comma_right_ob Y)))
  : (fmap (GluingChangeF H K α) h) ⦂ Cart(GluingRightF F')
  := gluing_change_pullback_cartesian H K α h HP Hi Hj.

End IndependentChange.

(** ** Reversed Category Levels

    Fix six separate base/target categories and compatible changes.
    The candidate preservation theorem uses only the supplied image square. *)

(** ** 反向范畴层级

    固定六个分离的基／目标范畴及相容变化；候选保持定理只使用给定像方形。 *)

Section ReversedChange.
Universes
  o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5.
Constraint e0 < h0, h0 < o0, o0 < l0.
Constraint h1 < e1, e1 < o1, o1 < l1.
Constraint e2 < h2, h2 < o2, o2 < l2.
Constraint h3 < e3, e3 < o3, o3 < l3.
Constraint e4 < h4, h4 < o4, o4 < l4.
Constraint h5 < e5, e5 < o5, o5 < l5.
Constraint l5 < o4, l4 < o3, l3 < o2, l2 < o1, l1 < o0.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {C'' : Cat@{o4 h4 e4 l4 l4}}.
Context {D'' : Cat@{o5 h5 e5 l5 l5}}.
Context {F : Fct C D} {F' : Fct C' D'} {F'' : Fct C'' D''}.
Context (H : Fct C C') (K : Fct D D').
Context (H' : Fct C' C'') (K' : Fct D' D'').
Context (α : (K ∘F F) ⇒ (F' ∘F H))
    (β : (K' ∘F F') ⇒ (F'' ∘F H')).

(** The actual change functor accepts these strict boundaries. *)

(** 实际变化函子接受这些严格边界。 *)

Definition reversed_gluing_change
  : Fct (Gluing F) (Gluing F')
  := GluingChangeF H K α.

(** Both projections retain their separate ambient categories. *)

(** 两个投影保持各自独立的环境范畴。 *)

Definition reversed_gluing_projection
  : (GluingRightF F' ∘F GluingChangeF H K α) ≅N (H ∘F GluingRightF F)
  := gluing_change_base_iso H K α.

(** Composite compatibility uses all six category boundaries. *)

(** 复合相容性使用全部六个范畴边界。 *)

Definition reversed_gluing_composite
  : (GluingChangeF H' K' β ∘F GluingChangeF H K α) ≅N
      GluingChangeF (H' ∘F H) (K' ∘F K)
        (GluingChangeCompBoundaryN H K H' K' α β)
  := gluing_change_comp_iso H K H' K' α β.

(** The cartesian image criterion retains only its local hypotheses. *)

(** 笛卡尔像判据只保留其局部假设。 *)

Definition reversed_gluing_cartesian {X Y : Gluing F} (h : Hom X Y)
    (HP : is_pullback (fmap K (fmap F (comma_right h)))
      (fmap K (comma_arrow Y)) (K (comma_left_ob X))
      (fmap K (comma_arrow X)) (fmap K (comma_left h)))
    (Hi : is_iso (α (comma_right_ob X)))
    (Hj : is_mono (α (comma_right_ob Y)))
  : (fmap (GluingChangeF H K α) h) ⦂ Cart(GluingRightF F')
  := gluing_change_pullback_cartesian H K α h HP Hi Hj.

End ReversedChange.

(** ** A Genuinely Monic Outgoing Boundary

    Start with the constant unit model on the walking arrow. Change it to
    the diagram selecting false from unit to booleans. The incoming
    boundary is identity; the outgoing boundary is monic but not invertible.
    Its image square is nevertheless cartesian by the weaker criterion. *)

(** ** 真正仅为单态射的出边界

    从步行箭头上的常单位模型出发，变化为从单位到布尔选择假的图式。入边界
    为恒等，出边界为单态射但不可逆；较弱判据仍使其像方形笛卡尔。 *)

Section MonicBoundary.

(** A chosen Boolean determines a respectful map from unit. *)

(** 给定布尔值确定一个从单位出发的尊重相等映射。 *)

Program Definition unit_bool (b : bool)
  : UnitS →r BoolS
  :=
  {|func x := b
  |}.
Next Obligation. intros x y H. reflexivity. Defined.

(** Every such map is monic because maps into unit are specified-equal. *)

(** 因为指向单位的映射都指定相等，每个这样的映射都是单态射。 *)

Definition unit_bool_mono (b : bool)
  : @is_mono SetCat UnitS BoolS (unit_bool b).
Proof. intros Q f g H x. exact tt. Defined.

(** Selecting false misses true, so this boundary has no inverse. *)

(** 选择假遗漏了真，因此此边界没有逆。 *)

Example unit_false_not_iso
  : ¬ @is_iso SetCat UnitS BoolS (unit_bool false).
Proof. intros [g [Hl Hr]]. pose proof (Hr true) as Ht. discriminate Ht. Defined.

(** The original model is constant and introduces no pullback choices. *)

(** 原模型为常值，不引入拉回选择。 *)

Definition UnitModelF
  : Fct ArrowShape SetCat
  := ConstF ArrowShape (C := SetCat) UnitS.

(** The changed model has distinct unit/Boolean endpoint carriers. *)

(** 变化后模型在两端具有不同的单位／布尔载体。 *)

Definition MonoModelF
  : Fct ArrowShape SetCat
  := ArrowDiagram (C := SetCat) (unit_bool false).

(** The boundary is the supplied arrow-diagram transformation. *)

(** 边界为给定的箭头图式自然变换。 *)

Program Definition MonoBoundaryN
  : (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF) ⇒
      (MonoModelF ∘F (@IdF ArrowShape))
  := @ArrowN SetCat
      (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF)
      (MonoModelF ∘F (@IdF ArrowShape)) id (unit_bool false) _.
Next Obligation. intros x. reflexivity. Defined.

(** Each base has the original identity structure arrow. *)

(** 每个基对象上都有原恒等结构箭头。 *)

Program Definition UnitGluingOb (b : bool)
  : Gluing UnitModelF
  :=
  {|comma_left_ob := UnitS
  ; comma_right_ob := b
  ; comma_arrow := id
  |}.

(** The walking step and identity top give the source square. *)

(** 步行边与恒等顶边给出源方形。 *)

Program Definition unit_gluing_step
  : Hom (UnitGluingOb false) (UnitGluingOb true)
  :=
  {|comma_left := id
  ; comma_right := arrow_step
  |}.
Next Obligation. intros x. exact tt. Defined.

(** The identity pullback is its complete cartesian witness. *)

(** 恒等拉回给出其完整笛卡尔见证。 *)

Definition unit_gluing_step_cartesian
  : unit_gluing_step ⦂ Cart(GluingRightF UnitModelF)
  := gluing_pullback_cartesian UnitModelF unit_gluing_step pullback_id.

(** The incoming boundary has the transparent identity inverse. *)

(** 入边界具有透明恒等逆。 *)

Definition mono_boundary_source_iso
  : is_iso (MonoBoundaryN false).
Proof. exists id. split; apply comp_id_l. Defined.

(** The outgoing component is monic without being invertible. *)

(** 出分量为单态射而不可逆。 *)

Example mono_boundary_target_not_iso
  : ¬ is_iso (MonoBoundaryN true)
  := unit_false_not_iso.

(** The actual mapped arrow is cartesian using only these local inputs. *)

(** 实际像箭头只用这些局部输入即为笛卡尔。 *)

Definition monic_changed_cartesian
  : (fmap (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN)
      unit_gluing_step) ⦂ Cart(GluingRightF MonoModelF)
  := gluing_change_pullback_cartesian IdF IdF MonoBoundaryN
      unit_gluing_step
      (gluing_cartesian_pullback UnitModelF unit_gluing_step
        unit_gluing_step_cartesian)
      mono_boundary_source_iso (unit_bool_mono false).

(** The changed structure at the target actually computes false. *)

(** 目标处变化后的结构箭头实际计算出假。 *)

Example monic_changed_arrow_computes
  : comma_arrow (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN
      (UnitGluingOb true)) tt = false.
Proof. reflexivity. Defined.

(** The nonidentity walking base edge is retained by computation. *)

(** 非恒等步行基边通过计算保留。 *)

Example monic_changed_base_computes
  : comma_right (fmap
      (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN)
      unit_gluing_step) = arrow_step.
Proof. reflexivity. Defined.

End MonicBoundary.

(** ** Failure without the Incoming Inverse

    Reverse the unit/Boolean diagram: the source boundary selects false
    and the target boundary is identity. The target functor is still
    identity, but the mapped source square is not cartesian. This guards
    against treating an arbitrary compatible change as cartesian. *)

(** ** 缺少入边界逆时的失败

    反转单位／布尔图式：源边界选择假，目标边界为恒等。目标函子仍为恒等，
    但源方形的像并非笛卡尔，防止将任意相容变化都视为保持笛卡尔。 *)

Section MissingIncomingInverse.

(** The collapsing map supplies the opposite directed model diagram. *)

(** 塌缩映射给出相反方向的模型图式。 *)

Program Definition bool_unit
  : BoolS →r UnitS
  :=
  {|func x := tt
  |}.

(** The alternative model sends the walking step from Boolean to unit. *)

(** 另一模型把步行边从布尔送到单位。 *)

Definition CollapseModelF
  : Fct ArrowShape SetCat
  := ArrowDiagram (C := SetCat) bool_unit.

(** Its compatible boundary has the noninvertible map at the source. *)

(** 其相容边界在源处具有不可逆映射。 *)

Program Definition CollapseBoundaryN
  : (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF) ⇒
      (CollapseModelF ∘F (@IdF ArrowShape))
  := @ArrowN SetCat
      (CompF (C := ArrowShape) (@IdF SetCat) UnitModelF)
      (CollapseModelF ∘F (@IdF ArrowShape)) (unit_bool false) id _.
Next Obligation. intros x. exact tt. Defined.

(** A cone selecting true has no mediator through the constant false leg. *)

(** 选择真的锥无法经常假边分解。 *)

Example arbitrary_change_not_cartesian
  : ¬ ((fmap (GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      CollapseBoundaryN) unit_gluing_step) ⦂ Cart(GluingRightF CollapseModelF)).
Proof.
  intro Hc.
  pose (HP := gluing_cartesian_pullback CollapseModelF
    (fmap (GluingChangeF (@IdF ArrowShape) (@IdF SetCat) CollapseBoundaryN)
      unit_gluing_step) Hc).
  assert (Hcone : fmap CollapseModelF arrow_step ∘ unit_bool true ≈
    comma_arrow (GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      CollapseBoundaryN (UnitGluingOb true)) ∘ id).
  { intros x. exact tt. }
  destruct (snd HP UnitS (unit_bool true) id Hcone) as [m [[H1 H2] Hu]].
  pose proof (H1 tt) as Ht. discriminate Ht.
Defined.

End MissingIncomingInverse.

(** ** Recovered Data through the Natural-Isomorphism Corollary

    Return to the original tagged lifting square. Identity model change
    preserves its pullback candidate. The newly transported cartesian
    witness computes a factor retaining both tagged coordinates. *)

(** ** 经过自然同构推论恢复数据

    回到原标签提升方形。恒等模型变化保持其候选拉回；新运输的笛卡尔见证
    计算出的分解保留两个标签坐标。 *)

Section TaggedTransport.

(** Identity compatibility is supplied as explicit natural data. *)

(** 恒等相容性作为显式自然数据给出。 *)

Definition TaggedBoundaryN
  : ((@IdF SetCat) ∘F IdF) ⇒ ((@IdF SetCat) ∘F IdF)
  := CommaChangeIdRightN IdF.

(** Retain a component inverse, without selecting any model limits. *)

(** 保留分量逆，不选择模型极限。 *)

Definition tagged_boundary_iso
  : TaggedBoundaryN ⦂ ((@IdF SetCat) ∘F IdF) ≅N ((@IdF SetCat) ∘F IdF).
Proof. intro X. exists id. split; apply comp_id_l. Defined.

(** The actual image is the original general change, not a second action. *)

(** 实际像使用原一般变化，而非第二套作用。 *)

Definition TaggedChangeF
  : Fct (Gluing (@IdF SetCat)) (Gluing (@IdF SetCat))
  := GluingChangeF IdF IdF TaggedBoundaryN.

(** Apply the isomorphism corollary with identity preservation of this cone. *)

(** 对此锥的恒等保持性应用同构推论。 *)

Definition tagged_changed_cartesian
  : (fmap TaggedChangeF tagged_reindex_lift) ⦂ Cart(GluingRightF (@IdF SetCat))
  := gluing_change_cartesian_iso IdF IdF TaggedBoundaryN tagged_reindex_lift
      tagged_boundary_iso (λ HP, HP) tagged_reindex_cartesian.

(** The generic factor uses the transported cartesian witness. *)

(** 一般分解使用运输后的笛卡尔见证。 *)

Definition tagged_changed_factor
  : (@Hom (Gluing (@IdF SetCat))) (TaggedChangeF TaggedGluingObj)
      (TaggedChangeF TaggedReindexedOb)
  := cartesian_factor tagged_changed_cartesian
      (fmap TaggedChangeF tagged_gluing_toggle) id
      (@comp_id_r SetCat TaggedGluingS TaggedGluingS gluing_toggle).

(** Both original tagged coordinates survive the boundary transport. *)

(** 两个原标签坐标都经边界运输保留。 *)

Example tagged_changed_factor_computes
  : ((comma_left tagged_changed_factor (3, false)).1,
      (comma_left tagged_changed_factor (3, false)).2.1) =
      ((3, false), (3, true)).
Proof. reflexivity. Defined.

(** The prescribed base factor stays the original identity function. *)

(** 给定基分解保持为原恒等函数。 *)

Example tagged_changed_factor_base_computes
  : comma_right tagged_changed_factor (3, false) = (3, false).
Proof. reflexivity. Defined.

(** The map action respects the original nontrivial square equality. *)

(** 映射作用保持原非平凡方形相等。 *)

Example tagged_change_respects
  : fmap TaggedChangeF tagged_gluing_toggle ≈ fmap TaggedChangeF id.
Proof. apply fmap_proper. exact tagged_gluing_toggle_equal. Defined.

(** The change still retains the native tag-changing side function. *)

(** 变化仍保留原生改变标签的侧边函数。 *)

Example tagged_changed_map_computes
  : comma_left (fmap TaggedChangeF tagged_gluing_toggle) (3, false)
      = (3, true).
Proof. reflexivity. Defined.

End TaggedTransport.

(** ** Computation of the Model-Change Comparisons

    Use the same unit and monic-boundary models. Identity and composite
    comparisons reuse the general comma inverses, followed only by
    specified-equal left-boundary transport. *)

(** ** 模型变化比较的计算

    使用同一单位及单态边界模型。恒等与复合比较复用一般逗号逆，之后只进行
    指定相等的左边界运输。 *)

Section ComparisonComputation.

(** The identity-model comparison retains its inverse as data. *)

(** 恒等模型比较将逆保留为数据。 *)

Definition UnitChangeIdIso
  : GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      (CommaChangeIdRightN UnitModelF) ≅N IdF
  := gluing_change_id_iso UnitModelF.

(** The identity comparison keeps the base object and its identity map. *)

(** 恒等比较保留基对象及其恒等映射。 *)

Example unit_change_identity_computes
  : comma_right (UnitChangeIdIso.1 (UnitGluingOb false)) = tt.
Proof. reflexivity. Defined.

(** Its saved inverse computes the original unit element. *)

(** 其保存的逆计算出原单位元素。 *)

Example unit_change_identity_inverse_computes
  : comma_left ((UnitChangeIdIso.2 (UnitGluingOb false)).1) tt = tt.
Proof. reflexivity. Defined.

(** Compose the monic-boundary change with identity of its target model. *)

(** 将单态边界变化与其目标模型上的恒等复合。 *)

Definition MonoChangeCompIso
  : (GluingChangeF (@IdF ArrowShape) (@IdF SetCat)
      (CommaChangeIdRightN MonoModelF) ∘F
      GluingChangeF (@IdF ArrowShape) (@IdF SetCat) MonoBoundaryN) ≅N
      GluingChangeF ((@IdF ArrowShape) ∘F IdF) ((@IdF SetCat) ∘F IdF)
        (GluingChangeCompBoundaryN IdF IdF IdF IdF MonoBoundaryN
          (CommaChangeIdRightN MonoModelF))
  := gluing_change_comp_iso IdF IdF IdF IdF MonoBoundaryN
      (CommaChangeIdRightN MonoModelF).

(** The composite comparison inverse preserves the endpoint base value. *)

(** 复合比较逆保持端点基值。 *)

Example monic_composite_inverse_computes
  : comma_right ((MonoChangeCompIso.2 (UnitGluingOb true)).1) = tt.
Proof. reflexivity. Defined.

(** A transported pullback token remains a Type-valued pair with its
    original Boolean equality witness. *)

(** 运输后的拉回元素仍为 Type 值有序对，带有原布尔相等见证。 *)

Definition tagged_changed_token
  : comma_left_ob (TaggedChangeF TaggedReindexedOb)
  := tagged_pullback_token.

(** Inspecting the unchanged witness needs no proof irrelevance. *)

(** 检查未变见证不需要证明无关性。 *)

Example tagged_changed_token_computes
  : snd tagged_changed_token.2.2 = true.
Proof. reflexivity. Defined.

End ComparisonComputation.
