From Cats Require Export
  Cat.Gluing.Fibration
  Cat.Comma.Change.
From Cats Require Import
  Cat.Pullback
  Cat.Morphism.

(** * Change of Gluing Models

    A compatible change [H] of base models, [K] of target categories and
    [α : K F ⇒ F' H] maps a structure arrow [r] to [α ∘ K r]. Reuse
    the general comma change, including its identity-component left
    boundary; no second gluing category or square action is introduced.

    The functor needs no invertibility or preservation. Cartesian-arrow
    preservation is a separate candidate theorem: the image square must
    be a pullback, the incoming boundary invertible and the outgoing one
    monic. The natural-isomorphism corollary retains explicit preservation
    of the relevant image squares. No limit choices or CCC assumptions
    are implicit. *)

(** * 粘合模型的变化

    相容的基模型变化 [H]、目标范畴变化 [K] 及 [α : K F ⇒ F' H] 将结构
    箭头 [r] 送为 [α ∘ K r]。复用一般逗号变化及其恒等分量左边界，不引入
    第二套粘合范畴或方形作用。

    函子不要求可逆性或保持性。笛卡尔箭头保持是独立候选定理：像方形须为
    拉回，入边界可逆而出边界为单态射。自然同构推论显式保留相关像方形的
    拉回保持性；不隐含极限选择或 CCC 假设。 *)

(** The left comma boundary changes only the identity-functor presentation. *)

(** 左逗号边界只改变恒等函子的表示。 *)

Program Definition GluingChangeLeftBoundaryN {D D' : Cat} (K : Fct D D')
  : (IdF ∘F K) ⇒ (K ∘F IdF)
  :=
  {|nt X := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** ** The Induced Functor and Projections

    Fix the four categories and a compatible natural boundary. All data
    come from the accepted comma construction. Equal boundaries compare
    the resulting functors by natural isomorphism. *)

(** ** 诱导函子及投影

    固定四个范畴及相容自然边界。全部数据来自已接收的逗号构造；相等边界
    通过自然同构比较所得函子。 *)

Section ModelChange.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).

(** Map gluing through the original comma-change functor. *)

(** 通过原逗号变化函子映射粘合。 *)

Definition GluingChangeF
  : Fct (Gluing F) (Gluing F')
  := CommaChangeF K H K (GluingChangeLeftBoundaryN K) α.

(** The target-domain projection comparison keeps identity components. *)

(** 目标定义域投影比较保留恒等分量。 *)

Definition GluingChangeLeftN
  : (GluingLeftF F' ∘F GluingChangeF) ⇒ (K ∘F GluingLeftF F)
  := CommaChangeLeftN K H K (GluingChangeLeftBoundaryN K) α.

(** The left projection comparison is the original comma isomorphism. *)

(** 左投影比较为原逗号同构。 *)

Definition gluing_change_left_iso
  : (GluingLeftF F' ∘F GluingChangeF) ≅N (K ∘F GluingLeftF F)
  := comma_change_left_iso K H K (GluingChangeLeftBoundaryN K) α.

(** The base projection is compatible with [H] by identity components. *)

(** 基投影通过恒等分量与 [H] 相容。 *)

Definition GluingChangeBaseN
  : (GluingRightF F' ∘F GluingChangeF) ⇒ (H ∘F GluingRightF F)
  := CommaChangeRightN K H K (GluingChangeLeftBoundaryN K) α.

(** The base comparison also retains its transparent inverse. *)

(** 基比较也保留其透明逆。 *)

Definition gluing_change_base_iso
  : (GluingRightF F' ∘F GluingChangeF) ≅N (H ∘F GluingRightF F)
  := comma_change_right_iso K H K (GluingChangeLeftBoundaryN K) α.

(** A gluing object has the expected mapped structure arrow in specified
    hom equality; the stored comma presentation includes an identity. *)

(** 粘合对象的结构箭头按指定 Hom 相等为预期的像；所存逗号表示含一个恒等。 *)

Definition gluing_change_arrow (X : Gluing F)
  : comma_arrow (GluingChangeF X) ≈
      α (comma_right_ob X) ∘ fmap K (comma_arrow X).
Proof. apply comp_id_r. Defined.

End ModelChange.

(** Equivalent natural boundaries give naturally isomorphic changes. *)

(** 等价自然边界给出自然同构的变化。 *)

Definition gluing_change_equiv_iso {C D C' D' : Cat}
    {F : Fct C D} {F' : Fct C' D'} (H : Fct C C') (K : Fct D D')
    {α β : (K ∘F F) ⇒ (F' ∘F H)} (Hα : α ≈N β)
  : GluingChangeF H K α ≅N GluingChangeF H K β
  := comma_change_equiv_iso K H K (λ X, reflexivity _) Hα.

(** Identity model change compares with the unchanged gluing functor.
    The only extra comparison reconciles the two identity-boundary
    presentations by their equal components. *)

(** 恒等模型变化与未改变的粘合函子比较；额外比较只以相等分量协调两个恒等
    边界表示。 *)

Definition gluing_change_id_iso {C D : Cat} (F : Fct C D)
  : GluingChangeF IdF IdF (CommaChangeIdRightN F) ≅N IdF.
Proof.
  transitivity (CommaChangeF IdF IdF IdF (CommaChangeIdLeftN (@IdF D))
    (CommaChangeIdRightN F)).
  - apply comma_change_equiv_iso; intro X; reflexivity.
  - apply comma_change_id_iso.
Defined.

(** ** Consecutive Model Changes

    Fix three interpretations and two natural compatibility boundaries.
    Pasting the right boundaries is the accepted comma construction;
    its left boundary is compared with the identity-component gluing
    boundary using the second target functor's identity law. *)

(** ** 连续模型变化

    固定三个解释及两条自然相容边界。右边界的粘合为已接收逗号构造；以第二个
    目标函子的恒等律，将其左边界与粘合的恒等分量边界比较。 *)

Section CompositeModelChange.
Context {C D C' D' C'' D'' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'} {F'' : Fct C'' D''}.
Context (H : Fct C C') (K : Fct D D').
Context (H' : Fct C' C'') (K' : Fct D' D'').
Context (α : (K ∘F F) ⇒ (F' ∘F H))
    (β : (K' ∘F F') ⇒ (F'' ∘F H')).

(** The composite boundary keeps the existing mapped-inner/outer data. *)

(** 复合边界保留既有的映射内边界／外边界数据。 *)

Definition GluingChangeCompBoundaryN
  : ((K' ∘F K) ∘F F) ⇒ (F'' ∘F (H' ∘F H))
  := CommaChangeCompRightN H K H' K' α β.

(** The comparison is the general composite isomorphism followed by
    equivalent-boundary comparison; all inverse witnesses are retained. *)

(** 比较由一般复合同构后接等价边界比较组成，保留全部逆见证。 *)

Definition gluing_change_comp_iso
  : (GluingChangeF H' K' β ∘F GluingChangeF H K α) ≅N
      GluingChangeF (H' ∘F H) (K' ∘F K) GluingChangeCompBoundaryN.
Proof.
  transitivity (CommaChangeF (K' ∘F K) (H' ∘F H) (K' ∘F K)
    (CommaChangeCompLeftN K K K' K'
      (GluingChangeLeftBoundaryN K) (GluingChangeLeftBoundaryN K'))
    GluingChangeCompBoundaryN).
  - apply comma_change_comp_iso.
  - apply comma_change_equiv_iso.
    + intro X. change (fmap K' (id[K X]) ∘ id ≈ id).
      rewrite fct_id, comp_id_l. reflexivity.
    + intro X. reflexivity.
Defined.

End CompositeModelChange.

(** ** Cartesian Images across a Supplied Boundary

    Fix one gluing square and its image under the target functor. Only
    the supplied image cone must be a pullback. At the source base object
    the boundary is invertible; at the target it only needs cancellation.
    Reuse the existing pullback boundary transport and candidate gluing
    theorem, retaining their transparent mediators. *)

(** ** 穿过给定边界的笛卡尔像

    固定一个粘合方形及其目标函子像；只要求给定像锥为拉回。在源基对象处，
    边界可逆；在目标处只需消去性。复用已有拉回边界运输及粘合候选定理，
    保留其透明中介。 *)

Section CartesianImage.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context {X Y : Gluing F} (h : Hom X Y).

(** The mapped square is supplied directly; no source cartesianness or
    global preservation assumption is necessary for this candidate. *)

(** 直接给出像方形；此候选不需要源笛卡尔性或全局保持性假设。 *)

Definition gluing_change_pullback_cartesian
    (HP : is_pullback (fmap K (fmap F (comma_right h)))
      (fmap K (comma_arrow Y)) (K (comma_left_ob X))
      (fmap K (comma_arrow X)) (fmap K (comma_left h)))
    (Hi : is_iso (α (comma_right_ob X)))
    (Hj : is_mono (α (comma_right_ob Y)))
  : fmap (GluingChangeF H K α) h ⦂ Cart(GluingRightF F').
Proof.
  apply (gluing_pullback_cartesian F').
  pose (P := pullback_base_boundary (α (comma_right_ob X)) Hi
    (α (comma_right_ob Y)) Hj (nat_naturality α (comma_right h)) HP).
  eapply pullback_congr; [reflexivity | | | reflexivity | exact P].
  - symmetry. apply gluing_change_arrow.
  - symmetry. apply gluing_change_arrow.
Defined.

(** Local preservation need only apply to this source square. The source
    candidate theorem supplies its pullback witness. *)

(** 局部保持性只需作用于此源方形；源候选定理给出其拉回见证。 *)

Definition gluing_change_cartesian
    (preserves : is_pullback (fmap F (comma_right h)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left h) →
      is_pullback (fmap K (fmap F (comma_right h)))
        (fmap K (comma_arrow Y)) (K (comma_left_ob X))
        (fmap K (comma_arrow X)) (fmap K (comma_left h)))
    (Hi : is_iso (α (comma_right_ob X)))
    (Hj : is_mono (α (comma_right_ob Y)))
    (Hh : h ⦂ Cart(GluingRightF F))
  : fmap (GluingChangeF H K α) h ⦂ Cart(GluingRightF F')
  := gluing_change_pullback_cartesian
      (preserves (gluing_cartesian_pullback F h Hh)) Hi Hj.

(** A natural-isomorphism boundary supplies the local inverse and monicity.
    Preservation of the relevant square remains explicit. *)

(** 自然同构边界提供局部逆及单态射性；相关方形的保持性仍显式给出。 *)

Definition gluing_change_cartesian_iso
    (Hα : α ⦂ (K ∘F F) ≅N (F' ∘F H))
    (preserves : is_pullback (fmap F (comma_right h)) (comma_arrow Y)
      (comma_left_ob X) (comma_arrow X) (comma_left h) →
      is_pullback (fmap K (fmap F (comma_right h)))
        (fmap K (comma_arrow Y)) (K (comma_left_ob X))
        (fmap K (comma_arrow X)) (fmap K (comma_left h)))
    (Hh : h ⦂ Cart(GluingRightF F))
  : fmap (GluingChangeF H K α) h ⦂ Cart(GluingRightF F')
  := gluing_change_cartesian preserves (Hα (comma_right_ob X))
      (iso_mono (α (comma_right_ob Y)) (Hα (comma_right_ob Y))) Hh.

End CartesianImage.
