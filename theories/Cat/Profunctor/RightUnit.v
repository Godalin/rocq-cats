From Cats Require Export
  Cat.Profunctor.ComposeMap
  Cat.Profunctor.Hom.
From Cats Require Import
  Cat.Core
  Cat.End.Core
  Cat.Isomorphism
  Cat.Coend.IndexReversal
  Cat.Coend.Yoneda
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope prof_scope.

(** * Hom as a Right Unit for Profunctor Composition

    Before [P] from [C] to [D], use the Hom profunctor of [C]. Reverse its
    composition kernel's index and exchange the factors to apply covariant
    co-Yoneda on [C^op]. The integrated index wrapper then reads that same
    universal witness back on [C]; no dual universal property is rebuilt. *)

(** * Hom 作为 Profunctor 复合的右单位

    在从 [C] 到 [D] 的 [P] 之前使用 [C] 的 Hom profunctor。反转复合核的指标并
    交换因子，以应用 [C^op] 上的协变 co-Yoneda；再用已有指标包装将同一泛见证
    读回 [C]，不重建对偶泛性质。 *)

(** ** Reorienting the Kernel

    Fix [P] and its outer objects. Only [C]'s Hom carrier and equality must
    fit the corresponding independent value bounds. Object sizes, the order
    between value bounds and [D]'s Hom sizes remain unrestricted. The kernel
    comparison preserves values and represented arrows, rewrapping lifts. *)

(** ** 重定向核

    固定 [P] 和外部对象。只需 [C] 的 Hom 载体及相等分别容纳于独立的对应值界，
    不限制对象大小、值界间次序或 [D] 的 Hom 大小。核比较保留值和所表示箭头，
    并重新包装提升。 *)

Section Kernels.
Universes u p.
Context {C D : Cat}.
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context (X : @Ob C) (Z : @Ob D).

(** Exchange the reversed kernel's Hom/value factors into co-Yoneda order. *)

(** 将反转核的 Hom／值因子交换为 co-Yoneda 的次序。 *)

Program Definition ProfRightUnitKernelN
  : BifunctorIndexOpF (ProfCompKernel P (HomProf C) X Z) ⇒
      CoyonedaKernel (π1F P Z) X
  :=
  {|nt AB :=
      {|func w := (snd w,{|lower := lower (fst w)|})
      |}
  |}.
Next Obligation.
  intros [h x] [k y] [Hh Hx]. split; [exact Hx |].
  exact {|lower := lower Hh|}.
Defined.
Next Obligation.
  intros [[h] x]. split; [reflexivity |].
  refine {|lower := _|}. apply comp_id_r.
Defined.

(** Reverse the factor exchange, keeping each represented arrow unchanged. *)

(** 反转因子交换，保持所表示的每条箭头不变。 *)

Program Definition prof_right_unit_kernel_iso
  : ProfRightUnitKernelN ⦂
      BifunctorIndexOpF (ProfCompKernel P (HomProf C) X Z) ≅N
      CoyonedaKernel (π1F P Z) X
  := λ AB,
      ({|func w := ({|lower := lower (snd w)|},fst w)|}; _).
Next Obligation.
  intros [x h] [y k] [Hx Hh]. split;
    [exact {|lower := lower Hh|} | exact Hx].
Defined.
Next Obligation.
  split.
  - intros [[h] x]. split; [exact {|lower := reflexivity h|} | reflexivity].
  - intros [x [h]]. split; [reflexivity | exact {|lower := reflexivity h|}].
Defined.

(** Use the general inverse natural transformation for the backward kernel. *)

(** 反向核使用一般逆自然变换。 *)

Definition ProfRightUnitKernelInvN
  : CoyonedaKernel (π1F P Z) X ⇒
      BifunctorIndexOpF (ProfCompKernel P (HomProf C) X Z)
  := ProfRightUnitKernelN ^-1N prof_right_unit_kernel_iso.

(** Read evaluation back on the original index with the existing wrapper. *)

(** 用已有包装将求值读回原指标。 *)

Definition ProfRightUnitCowedge
  : Cowedge (ProfCompKernel P (HomProf C) X Z) (P (X,Z))
  := cowedge_index_unop
      (cowedge_precompose (CoyonedaCowedge (π1F P Z) X)
        ProfRightUnitKernelN).

(** The identity-component factorization is the original covariant law on
    the opposite category, with the two kernel factors exchanged. *)

(** 恒等分量分解就是反范畴中原来的协变定律，只交换核的两个因子。 *)

Lemma prof_right_unit_factor {W : SetC}
    (κ : Cowedge (ProfCompKernel P (HomProf C) X Z) W)
    (Y : @Ob C) (h : Hom X Y) (x : P (Y,Z))
  : κ X ({|lower := @id X|},lmap[P; h] x) ≈S
      κ Y ({|lower := h|},x).
Proof.
  exact (coyoneda_cowedge_factor (π1F P Z) X
    (cowedge_precompose (cowedge_index_op κ) ProfRightUnitKernelInvN)
    Y x h).
Defined.

(** Reuse co-Yoneda's mediator and uniqueness witness on the reversed
    kernel, then transfer them back through index reversal. *)

(** 在反转核上复用 co-Yoneda 中介及唯一性见证，再经指标反转读回。 *)

Definition prof_right_unit_universal
  : is_coend ProfRightUnitCowedge.
Proof.
  apply coend_index_unop_universal.
  apply (snd (coend_universal_iff
    (cowedge_precompose (CoyonedaCowedge (π1F P Z) X)
      ProfRightUnitKernelN))).
  intros W κ.
  exists (coyoneda_desc (π1F P Z) X
    (cowedge_precompose κ ProfRightUnitKernelInvN)).
  pose (U := coyoneda_desc_unique (π1F P Z) X
    (cowedge_precompose κ ProfRightUnitKernelInvN)).
  refine {|this := _; that := _|}.
  - intros Y [[h] x]. exact (@this _ _ _ _ _ U Y (x,{|lower := h|})).
  - intros f H. apply (@that _ _ _ _ _ U f).
    intros Y [x [h]]. exact (H Y ({|lower := h|},x)).
Defined.

End Kernels.

(** Select this special composition explicitly on the original [P] values.
    Importing this module selects no global composition model. *)

(** 在原 [P] 值上显式选择此特殊复合；导入模块不选择全局复合模型。 *)

Program Definition ProfRightUnitComp@{u p +} {C D : Cat}
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
  : HasProfComp C C D P (HomProf C)
  :=
  {|hasProfCompCoend X Z :=
      {|hasOpEnd :=
          {|EndObj := P (X,Z)
          ; end_wedge := op_wedge (ProfRightUnitCowedge P X Z)
          ; end_universal := prof_right_unit_universal P X Z
          |}
      |}
  |}.

(** ** Comparison for One Supplied Kernel Coend

    Select only one right-unit kernel coend at fixed outer objects.
    Evaluate with its original mediator and insert the identity with its
    original injection. Opposite co-Yoneda supplies the full inverse laws. *)

(** ** 一个给定核 Coend 的比较

    固定外部对象，只选择一个右单位核 coend。以原中介求值，以原注入插入恒等，
    反范畴上的 co-Yoneda 提供完整互逆律。 *)

Section FixedCoend.
Universes u p.
Context {C D : Cat}.
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context (X : @Ob C) (Z : @Ob D).
Context `{HC : !HasCoend SetCat
    (ProfCompKernel P (HomProf C) X Z)}.

(** Evaluate the chosen coend with the derived universal cowedge. *)

(** 用派生的泛余楔求值选定 coend。 *)

Definition prof_right_unit_out
  : coend[ProfCompKernel P (HomProf C) X Z] →r P (X,Z)
  := coend⟨ProfRightUnitCowedge P X Z⟩.

(** The unitor applies the represented input arrow by preprocessing. *)

(** 单位子以预处理应用所表示的输入箭头。 *)

Lemma prof_right_unit_β (Y : @Ob C) (h : Hom X Y) (x : P (Y,Z))
  : prof_right_unit_out (ιcoend[ProfCompKernel P (HomProf C) X Z] Y
      ({|lower := h|},x)) ≈S lmap[P; h] x.
Proof.
  transitivity (ProfRightUnitCowedge P X Z Y ({|lower := h|},x)).
  - exact (@coend_β C (SetCat@{u p _ _ _ _ _})
      (ProfCompKernel P (HomProf C) X Z) HC (P (X,Z))
      (ProfRightUnitCowedge P X Z) Y ({|lower := h|},x)).
  - reflexivity.
Defined.

(** Reinsert the identity input arrow together with the original value. *)

(** 将恒等输入箭头与原值一起重新插入。 *)

Definition prof_right_unit_in
  : P (X,Z) →r coend[ProfCompKernel P (HomProf C) X Z]
  := ιcoend[ProfCompKernel P (HomProf C) X Z] X ∘r
      (ProfRightUnitKernelInvN P X Z (X,X) ∘r
        coyoneda_seed (π1F P Z) X).

(** Evaluation after insertion recovers the value in specified equality. *)

(** 插入后求值在指定相等下恢复原值。 *)

Lemma prof_right_unit_out_in
  : (prof_right_unit_out ∘r prof_right_unit_in) ≈f id_resp.
Proof.
  intros x. transitivity (lmap[P; @id X] x).
  - exact (prof_right_unit_β X (@id X) x).
  - exact (prof_lmap_id P X Z x).
Defined.

(** Generator extensionality proves the other inverse on the entire coend. *)

(** 生成元外延性证明整个 coend 上的另一条逆律。 *)

Lemma prof_right_unit_in_out
  : (prof_right_unit_in ∘r prof_right_unit_out) ≈f id_resp.
Proof.
  apply (@coend_hom_ext C SetCat
    (ProfCompKernel P (HomProf C) X Z) HC
    (coend[ProfCompKernel P (HomProf C) X Z])).
  intros Y [[h] x].
  transitivity (prof_right_unit_in (lmap[P; h] x)).
  - exact (@func_proper _ _ prof_right_unit_in _ _
      (prof_right_unit_β Y h x)).
  - exact (prof_right_unit_factor P X Z
      ιcoend[ProfCompKernel P (HomProf C) X Z] Y h x).
Defined.

(** Keep those same evaluation and identity-insertion maps in the comparison. *)

(** 在比较中保留同一求值映射和恒等插入映射。 *)

Definition ProfRightUnitIso
  : coend[ProfCompKernel P (HomProf C) X Z] ≅[SetCat] P (X,Z)
  := (prof_right_unit_out;
      (prof_right_unit_in;
        (prof_right_unit_in_out,prof_right_unit_out_in))).

End FixedCoend.

(** ** Outer-Boundary Naturality

    Fix [P]. Evaluation commutes with ordinary input and output boundary
    maps. A supplied Hom-composition family assembles these maps into the
    natural right unitor; its inverse reuses the fixed-boundary inverses. *)

(** ** 外部边界自然性

    固定 [P]，求值与通常的输入和输出边界映射交换。给定 Hom 复合族后，这些映射
    组成自然右单位子，其逆复用固定边界的逆。 *)

Section OuterNaturality.
Universes u p.
Context {C D : Cat}.
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).

(** The evaluation cowedges commute with the existing boundary maps. *)

(** 求值余楔与已有边界映射交换。 *)

Lemma prof_right_unit_eval_boundary
    {X X' : @Ob C} {Z Z' : @Ob D} (f : Hom X' X) (g : Hom Z Z')
    (Y : @Ob C)
  : (ProfRightUnitCowedge P X' Z' Y ∘r
      ProfCompBoundaryN P (HomProf C) f g (Y,Y)) ≈f
      (dimap[P; f; g] ∘r ProfRightUnitCowedge P X Z Y).
Proof.
  intros [[h] x].
  transitivity (lmap[P; h ∘ f] (rmap[P; g] x)).
  - exact (@prof_lmap_proper C D P Z' Y X' _ _
      (hom_prof_lmap C f {|lower := h|}) (rmap[P; g] x)).
  - transitivity (lmap[P; f] (lmap[P; h] (rmap[P; g] x))).
    + exact (prof_lmap_comp P Z' h f (rmap[P; g] x)).
    + transitivity (lmap[P; f] (rmap[P; g] (lmap[P; h] x))).
      * apply (@func_proper _ _ (lmap[P; f])).
        exact (prof_interchange P h g x).
      * symmetry. exact (prof_dimap_l_r P f g (lmap[P; h] x)).
Defined.

(** Only this Hom-composition family is needed to form natural evaluation. *)

(** 形成自然求值只需此 Hom 复合族。 *)

Program Definition ProfRightUnitorN
    `{HC : !HasProfComp C C D P (HomProf C)}
  : P ∘Pr HomProf C ⇒ P
  :=
  {|nt '(X,Z) := prof_right_unit_out P X Z
  |}.
Next Obligation.
  destruct X as [X Z], Y as [X' Z'], f as [f g]. cbn.
  refine (@coend_hom_ext C (SetCat@{u p _ _ _ _ _})
    (ProfCompKernel P (HomProf C) X Z)
    (@hasProfCompCoend C C D P (HomProf C) HC X Z) (P (X',Z'))
    (prof_right_unit_out P X' Z' ∘r
      coend_map (ProfCompBoundaryN P (HomProf C) f g))
    (dimap[P; f; g] ∘r prof_right_unit_out P X Z) _).
  intros Y0 v.
  transitivity (prof_right_unit_out P X' Z'
    (ιcoend[ProfCompKernel P (HomProf C) X' Z'] Y0
      (ProfCompBoundaryN P (HomProf C) f g (Y0,Y0) v))).
  - apply (@func_proper _ _ (prof_right_unit_out P X' Z')).
    exact (coend_map_β
      (ProfCompBoundaryN P (HomProf C) f g) Y0 v).
  - transitivity (ProfRightUnitCowedge P X' Z' Y0
      (ProfCompBoundaryN P (HomProf C) f g (Y0,Y0) v)).
    + exact (coend_β (ProfRightUnitCowedge P X' Z') Y0 _).
    + transitivity (dimap[P; f; g]
        (ProfRightUnitCowedge P X Z Y0 v)).
      * exact (prof_right_unit_eval_boundary f g Y0 v).
      * symmetry. apply (@func_proper _ _ (dimap[P; f; g])).
        exact (coend_β (ProfRightUnitCowedge P X Z) Y0 v).
Defined.

(** Each component has its already computed identity-insertion inverse. *)

(** 每个分量具有已经计算得到的恒等插入逆。 *)

Definition ProfRightUnitor
    `{HC : !HasProfComp C C D P (HomProf C)}
  : P ∘Pr HomProf C ≅N P.
Proof.
  exists ProfRightUnitorN. intros [X Z].
  exact (ProfRightUnitIso P X Z).2.
Defined.

(** General inverse naturality applies to the same identity insertions. *)

(** 一般逆自然性适用于同一恒等插入。 *)

Definition ProfRightUnitorInvN
    `{HC : !HasProfComp C C D P (HomProf C)}
  : P ⇒ P ∘Pr HomProf C
  := ProfRightUnitorN ^-1N ProfRightUnitor.2.

End OuterNaturality.

(** ** Naturality in the Input Profunctor

    Fix a transformation of [P]. Its original naturality gives evaluation's
    square using only two individual coends at one boundary. Full families
    specialize that law to the existing map of profunctor composites. *)

(** ** 关于输入 Profunctor 的自然性

    固定 [P] 的变换，其原自然性在一个边界处仅用两个单独 coend 给出求值方块。
    完整复合族将该定律特化到已有 profunctor 复合映射。 *)

Section InputNaturality.
Universes u p.
Context {C D : Cat}.
Context {P Q : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}.
Context (α : P ⇒ Q).

(** Two fixed-boundary coends suffice for the input-transformation square. *)

(** 输入变换方块只需两个固定边界 coend。 *)

Lemma prof_right_unit_out_input (X : @Ob C) (Z : @Ob D)
    `{HP : !HasCoend SetCat (ProfCompKernel P (HomProf C) X Z)}
    `{HQ : !HasCoend SetCat (ProfCompKernel Q (HomProf C) X Z)}
  : (prof_right_unit_out Q X Z ∘r
      coend_map (ProfCompInputN α (IdN (F := HomProf C)) X Z))
      ≈f (α (X,Z) ∘r prof_right_unit_out P X Z).
Proof.
  refine (@coend_hom_ext C (SetCat@{u p _ _ _ _ _})
    (ProfCompKernel P (HomProf C) X Z) HP (Q (X,Z))
    (prof_right_unit_out Q X Z ∘r coend_map
      (ProfCompInputN α (IdN (F := HomProf C)) X Z))
    (α (X,Z) ∘r prof_right_unit_out P X Z) _).
  intros Y [[h] x].
  transitivity (prof_right_unit_out Q X Z
    (ιcoend[ProfCompKernel Q (HomProf C) X Z] Y
      ({|lower := h|},α (Y,Z) x))).
  - apply (@func_proper _ _ (prof_right_unit_out Q X Z)).
    exact (coend_map_β (ProfCompInputN α (IdN (F := HomProf C)) X Z)
      Y ({|lower := h|},x)).
  - transitivity (lmap[Q; h] (α (Y,Z) x)).
    + exact (prof_right_unit_β Q X Z Y h (α (Y,Z) x)).
    + transitivity (α (X,Z) (lmap[P; h] x)).
      * symmetry. exact (prof_natural α h (@id Z) x).
      * symmetry. exact (@func_proper _ _ (α (X,Z)) _ _
          (prof_right_unit_β P X Z Y h x)).
Defined.

(** Right unitors intertwine the existing composite transformation. *)

(** 右单位子与已有复合变换交织。 *)

Lemma prof_right_unitor_natural
    `{HP : !HasProfComp C C D P (HomProf C)}
    `{HQ : !HasProfComp C C D Q (HomProf C)}
  : (ProfRightUnitorN Q ∘Nv ProfCompMapN α IdN) ≈N
      (α ∘Nv ProfRightUnitorN P).
Proof. intros [X Z]. exact (prof_right_unit_out_input X Z). Defined.

(** The computed inverse square is the general inverse-isomorphism square. *)

(** 计算逆的方块就是一般逆同构方块。 *)

Lemma prof_right_unitor_inv_natural
    `{HP : !HasProfComp C C D P (HomProf C)}
    `{HQ : !HasProfComp C C D Q (HomProf C)}
    (X : @Ob C) (Z : @Ob D)
  : (ProfRightUnitorInvN Q (X,Z) ∘r α (X,Z)) ≈f
      (ProfCompMapN α IdN (X,Z) ∘r ProfRightUnitorInvN P (X,Z)).
Proof.
  exact (@iso_square_inv SetCat _ _ _ _
    (ProfRightUnitIso P X Z) (ProfRightUnitIso Q X Z)
    (ProfCompMapN α IdN (X,Z)) (α (X,Z))
    (prof_right_unitor_natural (X,Z))).
Defined.

End InputNaturality.
