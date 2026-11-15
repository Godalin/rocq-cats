From Cats Require Export
  Cat.Profunctor.ComposeMap
  Cat.Profunctor.Hom.
From Cats Require Import
  Cat.Core
  Cat.End.Core
  Cat.Isomorphism
  Cat.Coend.Yoneda
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope profunctor_scope.

(** * Hom as a Left Unit for Profunctor Composition

    After [P] from [C] to [D], use the Hom profunctor of [D]. Co-Yoneda
    supplies its kernel's universal value directly. Only [D]'s actual Hom
    carrier and equality bounds must fit the corresponding value bounds;
    object sizes and the order between value bounds remain unrestricted. *)

(** * Hom 作为 Profunctor 复合的左单位

    在从 [C] 到 [D] 的 [P] 之后使用 [D] 的 Hom profunctor。co-Yoneda 直接给出
    其核的泛值。只需 [D] 的真实 Hom 载体和相等界分别容纳于对应值界，不限制
    对象大小或两个值界间的次序。 *)

(** ** Comparing the Two Kernel Presentations

    Fix [P] and the outer objects. Preserve the value and represented arrow,
    rewrapping the Hom lift at the kernel's own bounds. The arrow maps differ
    by Hom's identity postcomposition; no functor records are identified. *)

(** ** 比较两种核表示

    固定 [P] 和外部对象，保留值及所表示箭头，并按核自身的界重新包装 Hom 提升。
    箭头映射只差 Hom 的恒等后合成，不等同函子记录。 *)

Section Kernels.
Universes u p.
Context {C D : Cat}.
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context (X : @Ob C) (Z : @Ob D).

(** Keep the same value and represented arrow in the co-Yoneda kernel. *)

(** 在 co-Yoneda 核中保留同一个值及所表示箭头。 *)

Program Definition ProfunctorLeftUnitKernelN
  : ProfunctorCompKernel (HomProfunctor D) P X Z ⇒
      CoyonedaKernel (π2F P X) Z
  :=
  {|nt AB :=
      {|func w := (fst w,{|lower := lower (snd w)|})
      |}
  |}.
Next Obligation.
  intros [x h] [y k] [Hx Hh]. split; [exact Hx |].
  exact {|lower := lower Hh|}.
Defined.
Next Obligation.
  intros [x [h]]. split; [reflexivity |].
  refine {|lower := _|}. apply comp_proper; [apply comp_id_l | reflexivity].
Defined.

(** Rewrapping in reverse gives a transparent inverse in specified equality. *)

(** 反向重包装给出指定相等下的透明逆。 *)

Program Definition profunctor_left_unit_kernel_iso
  : ProfunctorLeftUnitKernelN ⦂
      ProfunctorCompKernel (HomProfunctor D) P X Z ≅N
      CoyonedaKernel (π2F P X) Z
  := λ AB,
      ({|func w := (fst w,{|lower := lower (snd w)|})|}; _).
Next Obligation.
  intros [x h] [y k] [Hx Hh]. split; [exact Hx |].
  exact {|lower := lower Hh|}.
Defined.
Next Obligation.
  split; intros [x [h]]; split; [reflexivity | exact {|lower := reflexivity h|} |
    reflexivity | exact {|lower := reflexivity h|}].
Defined.

(** Reverse the comparison using the general inverse natural transformation. *)

(** 用一般逆自然变换反转该比较。 *)

Definition ProfunctorLeftUnitKernelInvN
  : CoyonedaKernel (π2F P X) Z ⇒
      ProfunctorCompKernel (HomProfunctor D) P X Z
  := ProfunctorLeftUnitKernelN ^-1N profunctor_left_unit_kernel_iso.

(** Transfer the co-Yoneda evaluation cowedge along the same comparison. *)

(** 沿同一个比较运输 co-Yoneda 求值余楔。 *)

Definition ProfunctorLeftUnitCowedge
  : Cowedge (ProfunctorCompKernel (HomProfunctor D) P X Z) (P (X,Z))
  := cowedge_precompose (CoyonedaCowedge (π2F P X) Z)
      ProfunctorLeftUnitKernelN.

(** Every cowedge uses co-Yoneda's identity-component factorization. *)

(** 每个余楔使用 co-Yoneda 的恒等分量分解。 *)

Lemma profunctor_left_unit_factor {W : SetC}
    (κ : Cowedge (ProfunctorCompKernel (HomProfunctor D) P X Z) W)
    (Y : @Ob D) (x : P (X,Y)) (h : Hom Y Z)
  : κ Z (rmap[P; h] x,{|lower := @id Z|}) ≈S
      κ Y (x,{|lower := h|}).
Proof.
  exact (coyoneda_cowedge_factor (π2F P X) Z
    (cowedge_precompose κ ProfunctorLeftUnitKernelInvN) Y x h).
Defined.

(** The general co-Yoneda universal witness applies to these identity legs.
    No new mediator or uniqueness argument is required. *)

(** 一般 co-Yoneda 泛见证适用于这些恒等腿，不需要新的中介或唯一性论证。 *)

Definition profunctor_left_unit_universal
  : is_coend ProfunctorLeftUnitCowedge.
Proof.
  apply (snd (coend_universal_iff ProfunctorLeftUnitCowedge)).
  intros W κ.
  exists (coyoneda_desc (π2F P X) Z
    (cowedge_precompose κ ProfunctorLeftUnitKernelInvN)).
  pose (U := coyoneda_desc_unique (π2F P X) Z
    (cowedge_precompose κ ProfunctorLeftUnitKernelInvN)).
  refine {|this := _; that := _|}.
  - intros Y [x [h]]. exact (@this _ _ _ _ _ U Y (x,{|lower := h|})).
  - intros f H. apply (@that _ _ _ _ _ U f).
    intros Y [x [h]]. exact (H Y (x,{|lower := h|})).
Defined.

End Kernels.

(** Explicitly choose this particular composite on the original [P] values.
    Importing the module does not select a composition model globally. *)

(** 在原 [P] 值上显式选择这一特殊复合；导入模块不全局选择复合模型。 *)

Program Definition ProfunctorLeftUnitComp@{u p +} {C D : Cat}
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
  : HasProfunctorComp C D D (HomProfunctor D) P
  :=
  {|hasProfunctorCompCoend X Z :=
      {|hasOpEnd :=
          {|EndObj := P (X,Z)
          ; end_wedge := op_wedge (ProfunctorLeftUnitCowedge P X Z)
          ; end_universal := profunctor_left_unit_universal P X Z
          |}
      |}
  |}.

(** ** Comparison for One Supplied Kernel Coend

    Select only one Hom-composition coend at fixed outer objects. Evaluate
    using its original mediator and insert the identity using its original
    injection; the co-Yoneda factorization proves the full inverse laws. *)

(** ** 一个给定核 Coend 的比较

    固定外部对象，只选择一个 Hom 复合 coend。以原泛中介求值，以原注入插入恒等，
    co-Yoneda 分解证明完整互逆律。 *)

Section FixedCoend.
Universes u p.
Context {C D : Cat}.
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context (X : @Ob C) (Z : @Ob D).
Context `{HC : !HasCoend SetCat
    (ProfunctorCompKernel (HomProfunctor D) P X Z)}.

(** Evaluate this selected coend by the inherited cowedge mediator. *)

(** 以继承的余楔中介求值此选定 coend。 *)

Definition profunctor_left_unit_out
  : coend[ProfunctorCompKernel (HomProfunctor D) P X Z] →r P (X,Z)
  := coend⟨ProfunctorLeftUnitCowedge P X Z⟩.

(** The unitor evaluates the represented output arrow on its value. *)

(** 单位子将所表示的输出箭头作用于其值。 *)

Lemma profunctor_left_unit_β (Y : @Ob D) (x : P (X,Y)) (h : Hom Y Z)
  : profunctor_left_unit_out (ιPr[HomProfunctor D; P; Y]
      (x,{|lower := h|})) ≈S rmap[P; h] x.
Proof.
  exact (coend_β (ProfunctorLeftUnitCowedge P X Z) Y (x,{|lower := h|})).
Defined.

(** Reinsert the value paired with the identity output arrow. *)

(** 将值与恒等输出箭头配对后重新插入。 *)

Definition profunctor_left_unit_in
  : P (X,Z) →r coend[ProfunctorCompKernel (HomProfunctor D) P X Z]
  := ιPr[HomProfunctor D; P; Z] ∘r
      (ProfunctorLeftUnitKernelInvN P X Z (Z,Z) ∘r
        coyoneda_seed (π2F P X) Z).

(** Insertion and evaluation recover the value in its specified equality. *)

(** 插入后求值在指定相等下恢复值。 *)

Lemma profunctor_left_unit_out_in
  : (profunctor_left_unit_out ∘r profunctor_left_unit_in) ≈f id_resp.
Proof.
  intros x. transitivity (rmap[P; @id Z] x).
  - exact (profunctor_left_unit_β Z x (@id Z)).
  - exact (profunctor_rmap_id P X Z x).
Defined.

(** The other inverse fixes the complete coend, by generator extensionality. *)

(** 另一条逆律由生成元外延性固定整个 coend。 *)

Lemma profunctor_left_unit_in_out
  : (profunctor_left_unit_in ∘r profunctor_left_unit_out) ≈f id_resp.
Proof.
  apply (@coend_hom_ext D SetCat
    (ProfunctorCompKernel (HomProfunctor D) P X Z) HC
    (coend[ProfunctorCompKernel (HomProfunctor D) P X Z])).
  intros Y [x [h]].
  transitivity (profunctor_left_unit_in (rmap[P; h] x)).
  - exact (@func_proper _ _ profunctor_left_unit_in _ _
      (profunctor_left_unit_β Y x h)).
  - exact (profunctor_left_unit_factor P X Z
      ιcoend[ProfunctorCompKernel (HomProfunctor D) P X Z] Y x h).
Defined.

(** The fixed-boundary isomorphism retains these same computed maps. *)

(** 固定边界同构保留同一计算映射。 *)

Definition ProfunctorLeftUnitIso
  : coend[ProfunctorCompKernel (HomProfunctor D) P X Z] ≅[SetCat] P (X,Z)
  := (profunctor_left_unit_out;
      (profunctor_left_unit_in;
        (profunctor_left_unit_in_out,profunctor_left_unit_out_in))).

End FixedCoend.

(** ** Outer-Boundary Naturality

    Keep [P] fixed. Evaluation commutes with preprocessing the input and
    postprocessing the output by the one-sided action laws. Selecting the
    composition family then assembles these evaluations into one natural
    unitor, with its inverse inherited from the fixed-boundary comparisons. *)

(** ** 外部边界自然性

    固定 [P]，求值由单侧作用定律与输入预处理及输出后处理交换。选择复合族后，
    这些求值组成一个自然单位子，其逆继承自固定边界比较。 *)

Section OuterNaturality.
Universes u p.
Context {C D : Cat}.
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).

(** The evaluation cowedges commute with the original boundary maps. *)

(** 求值余楔与原边界映射交换。 *)

Lemma profunctor_left_unit_eval_boundary
    {X X' : @Ob C} {Z Z' : @Ob D} (f : Hom X' X) (g : Hom Z Z')
    (Y : @Ob D)
  : (ProfunctorLeftUnitCowedge P X' Z' Y ∘r
      ProfunctorCompBoundaryN (HomProfunctor D) P f g (Y,Y)) ≈f
      (dimap[P; f; g] ∘r ProfunctorLeftUnitCowedge P X Z Y).
Proof.
  intros [x [h]].
  transitivity (rmap[P; g ∘ h] (lmap[P; f] x)).
  - exact (@profunctor_rmap_proper C D P X' Y Z' _ _
      (hom_profunctor_rmap D g {|lower := h|}) (lmap[P; f] x)).
  - transitivity (rmap[P; g] (rmap[P; h] (lmap[P; f] x))).
    + exact (profunctor_rmap_comp P X' h g (lmap[P; f] x)).
    + transitivity (rmap[P; g] (lmap[P; f] (rmap[P; h] x))).
      * apply (@func_proper _ _ (rmap[P; g])). symmetry.
        exact (profunctor_interchange P f h x).
      * symmetry. exact (profunctor_dimap_r_l P f g (rmap[P; h] x)).
Defined.

(** Assume only this Hom-composition family to form the natural evaluation. *)

(** 只假设此 Hom 复合族即可形成自然求值。 *)

Program Definition ProfunctorLeftUnitorN
    `{HC : !HasProfunctorComp C D D (HomProfunctor D) P}
  : HomProfunctor D ∘Pr P ⇒ P
  :=
  {|nt '(X,Z) := profunctor_left_unit_out P X Z
  |}.
Next Obligation.
  destruct X as [X Z], Y as [X' Z'], f as [f g]. cbn.
  refine (@coend_hom_ext D (SetCat@{u p _ _ _ _ _})
    (ProfunctorCompKernel (HomProfunctor D) P X Z)
    (@hasProfunctorCompCoend C D D (HomProfunctor D) P HC X Z) (P (X',Z'))
    (profunctor_left_unit_out P X' Z' ∘r
      coend_map (ProfunctorCompBoundaryN (HomProfunctor D) P f g))
    (dimap[P; f; g] ∘r profunctor_left_unit_out P X Z) _).
  intros Y0 v.
  transitivity (profunctor_left_unit_out P X' Z'
    (ιcoend[ProfunctorCompKernel (HomProfunctor D) P X' Z'] Y0
      (ProfunctorCompBoundaryN (HomProfunctor D) P f g (Y0,Y0) v))).
  - apply (@func_proper _ _ (profunctor_left_unit_out P X' Z')).
    exact (coend_map_β
      (ProfunctorCompBoundaryN (HomProfunctor D) P f g) Y0 v).
  - transitivity (ProfunctorLeftUnitCowedge P X' Z' Y0
      (ProfunctorCompBoundaryN (HomProfunctor D) P f g (Y0,Y0) v)).
    + exact (coend_β (ProfunctorLeftUnitCowedge P X' Z') Y0 _).
    + transitivity (dimap[P; f; g]
        (ProfunctorLeftUnitCowedge P X Z Y0 v)).
      * exact (profunctor_left_unit_eval_boundary f g Y0 v).
      * symmetry. apply (@func_proper _ _ (dimap[P; f; g])).
        exact (coend_β (ProfunctorLeftUnitCowedge P X Z) Y0 v).
Defined.

(** Each component has the already computed identity-insertion inverse. *)

(** 每个分量具有已经计算得到的恒等插入逆。 *)

Definition ProfunctorLeftUnitor
    `{HC : !HasProfunctorComp C D D (HomProfunctor D) P}
  : HomProfunctor D ∘Pr P ≅N P.
Proof.
  exists ProfunctorLeftUnitorN. intros [X Z].
  exact (ProfunctorLeftUnitIso P X Z).2.
Defined.

(** The inverse natural transformation uses those same identity insertions;
    its naturality is the general inverse-naturality theorem. *)

(** 逆自然变换使用同一恒等插入，其自然性由一般逆自然性定理得到。 *)

Definition ProfunctorLeftUnitorInvN
    `{HC : !HasProfunctorComp C D D (HomProfunctor D) P}
  : P ⇒ HomProfunctor D ∘Pr P
  := ProfunctorLeftUnitorN ^-1N ProfunctorLeftUnitor.2.

End OuterNaturality.

(** ** Naturality in the Input Profunctor

    Fix a transformation and first choose only the two fixed-boundary
    coends. The original naturality of the transformation proves the
    evaluation square; full composition families specialize that same law. *)

(** ** 关于输入 Profunctor 的自然性

    固定变换，先只选择两个固定边界 coend。变换的原自然性证明求值方块，完整
    复合族再特化同一定律。 *)

Section InputNaturality.
Universes u p.
Context {C D : Cat}.
Context {P Q : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}.
Context (α : P ⇒ Q).

(** At one boundary, just two individual coends suffice for the square. *)

(** 在一个边界处，方块只需两个单独的 coend。 *)

Lemma profunctor_left_unit_out_input (X : @Ob C) (Z : @Ob D)
    `{HP : !HasCoend SetCat (ProfunctorCompKernel (HomProfunctor D) P X Z)}
    `{HQ : !HasCoend SetCat (ProfunctorCompKernel (HomProfunctor D) Q X Z)}
  : (profunctor_left_unit_out Q X Z ∘r
      coend_map (ProfunctorCompInputN (idN (F := HomProfunctor D)) α X Z))
      ≈f (α (X,Z) ∘r profunctor_left_unit_out P X Z).
Proof.
  refine (@coend_hom_ext D (SetCat@{u p _ _ _ _ _})
    (ProfunctorCompKernel (HomProfunctor D) P X Z) HP (Q (X,Z))
    (profunctor_left_unit_out Q X Z ∘r coend_map
      (ProfunctorCompInputN (idN (F := HomProfunctor D)) α X Z))
    (α (X,Z) ∘r profunctor_left_unit_out P X Z) _).
  intros Y [x [h]].
  transitivity (profunctor_left_unit_out Q X Z
    (ιPr[HomProfunctor D; Q; Y] (α (X,Y) x,{|lower := h|}))).
  - apply (@func_proper _ _ (profunctor_left_unit_out Q X Z)).
    exact (coend_map_β (ProfunctorCompInputN (idN (F := HomProfunctor D)) α X Z)
      Y (x,{|lower := h|})).
  - transitivity (rmap[Q; h] (α (X,Y) x)).
    + exact (profunctor_left_unit_β Q X Z Y (α (X,Y) x) h).
    + transitivity (α (X,Z) (rmap[P; h] x)).
      * symmetry. exact (profunctor_natural α (@id X) h x).
      * symmetry. exact (@func_proper _ _ (α (X,Z)) _ _
          (profunctor_left_unit_β P X Z Y x h)).
Defined.

(** The unitors intertwine the existing map of composite profunctors. *)

(** 单位子与已有复合 profunctor 映射交织。 *)

Lemma profunctor_left_unitor_natural
    `{HP : !HasProfunctorComp C D D (HomProfunctor D) P}
    `{HQ : !HasProfunctorComp C D D (HomProfunctor D) Q}
  : (ProfunctorLeftUnitorN Q ∘Nv ProfunctorCompMapN idN α) ≈N
      (α ∘Nv ProfunctorLeftUnitorN P).
Proof. intros [X Z]. exact (profunctor_left_unit_out_input X Z). Defined.

(** Inverse input naturality follows from the general inverse square. *)

(** 逆的输入自然性由一般逆方块得到。 *)

Lemma profunctor_left_unitor_inv_natural
    `{HP : !HasProfunctorComp C D D (HomProfunctor D) P}
    `{HQ : !HasProfunctorComp C D D (HomProfunctor D) Q}
    (X : @Ob C) (Z : @Ob D)
  : (ProfunctorLeftUnitorInvN Q (X,Z) ∘r α (X,Z)) ≈f
      (ProfunctorCompMapN idN α (X,Z) ∘r ProfunctorLeftUnitorInvN P (X,Z)).
Proof.
  exact (@iso_square_inv SetCat _ _ _ _
    (ProfunctorLeftUnitIso P X Z) (ProfunctorLeftUnitIso Q X Z)
    (ProfunctorCompMapN idN α (X,Z)) (α (X,Z))
    (profunctor_left_unitor_natural (X,Z))).
Defined.

End InputNaturality.
