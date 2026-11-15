From Cats Require Export
  Cat.Profunctor.StrengthNatural
  Cat.Profunctor.ComposeStrength.
From Cats Require Import
  Cat.Profunctor.ComposeMap
  Instance.Set.Core.

Local Open Scope monoidal_scope.
Local Open Scope prof_scope.

(** * Composition of Strength-Preserving Transformations

    The original map of chosen coends commutes with simultaneous context
    extension when both input transformations preserve strength. Prove the
    square on generators, then lift the original composition operations
    into the category of strong profunctors. Existence remains explicit. *)

(** * 保持强度的变换的复合

    当两个输入变换保持强度时，原选定 coend 映射与同时扩展上下文交换。
    在生成元上证明方块，再将原复合运算提升到强 profunctor 范畴；存在性仍须
    显式给定。 *)

(** ** A Square at Fixed Boundaries

    Fix the two transformations and their strength-preservation witnesses.
    At one context and pair of outer objects, only the four corresponding
    kernel coends are required, with independent choices. No full family,
    tensor preservation or bounds on the base category are assumed. *)

(** ** 固定边界处的方块

    固定两个变换及其强度保持性见证。给定一个上下文及一对外部对象，只需要
    对应的四个核 coend，选择彼此独立；不假设完整族、张量保持性或基范畴大小界。 *)

Section FixedSquare.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Context {Q Q' P P' : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}.
Context (SQ : HasProfStrength MC Q) (SQ' : HasProfStrength MC Q').
Context (SP : HasProfStrength MC P) (SP' : HasProfStrength MC P').
Context (β : Q ⇒ Q') (α : P ⇒ P').
Context (Hβ : is_prof_strength_hom SQ SQ' β).
Context (Hα : is_prof_strength_hom SP SP' α).
Context (Z X Y : @Ob C).
Context `{HS : !HasCoend SetCat (ProfCompKernel Q P X Y)}.
Context `{HS' : !HasCoend SetCat (ProfCompKernel Q' P' X Y)}.
Context `{HT : !HasCoend SetCat (ProfCompKernel Q P (Z ⊗ X) (Z ⊗ Y))}.
Context `{HT' : !HasCoend SetCat (ProfCompKernel Q' P' (Z ⊗ X) (Z ⊗ Y))}.

(** Both routes send a generator to the same strengthened image pair;
    the original mediator extensionality proves equality on the full coend. *)

(** 两条路径将生成元送到同一加强后的像对；原中介外延性给出整个 coend 上的相等。 *)

Lemma prof_comp_strength_input
  : (coend_map (ProfCompInputN β α (Z ⊗ X) (Z ⊗ Y)) ∘r
      @prof_comp_strength C MC Q P SQ SP Z X Y HT HS) ≈f
      (@prof_comp_strength C MC Q' P' SQ' SP' Z X Y HT' HS' ∘r
        coend_map (ProfCompInputN β α X Y)).
Proof.
  apply (@prof_comp_hom_ext C C C Q P X Y HS). intros B [x y].
  change (coend_map (ProfCompInputN β α (Z ⊗ X) (Z ⊗ Y))
    (prof_comp_strength MC Q P SQ SP Z X Y (ιPr[Q; P; B] (x,y))) ≈S
    prof_comp_strength MC Q' P' SQ' SP' Z X Y
      (coend_map (ProfCompInputN β α X Y) (ιPr[Q; P; B] (x,y)))).
  transitivity (coend_map (ProfCompInputN β α (Z ⊗ X) (Z ⊗ Y))
    (ιPr[Q; P; Z ⊗ B] (pstrength[SP; Z] x,pstrength[SQ; Z] y))).
  - apply func_proper.
    exact (prof_comp_strength_inject MC Q P SQ SP Z X Y B x y).
  - transitivity (ιPr[Q'; P'; Z ⊗ B]
      (α (Z ⊗ X,Z ⊗ B) (pstrength[SP; Z] x),
        β (Z ⊗ B,Z ⊗ Y) (pstrength[SQ; Z] y))).
    + exact (prof_comp_input_inject β α (Z ⊗ B)
        (pstrength[SP; Z] x) (pstrength[SQ; Z] y)).
    + transitivity (ιPr[Q'; P'; Z ⊗ B]
        (pstrength[SP'; Z] (α (X,B) x),pstrength[SQ'; Z] (β (B,Y) y))).
      * apply func_proper. split.
        -- exact (Hα Z X B x).
        -- exact (Hβ Z B Y y).
      * symmetry. transitivity (prof_comp_strength MC Q' P' SQ' SP' Z X Y
          (ιPr[Q'; P'; B] (α (X,B) x,β (B,Y) y))).
        -- apply func_proper. exact (prof_comp_input_inject β α B x y).
        -- exact (prof_comp_strength_inject MC Q' P' SQ' SP'
            Z X Y B (α (X,B) x) (β (B,Y) y)).
Defined.

End FixedSquare.

(** ** A Map between Two Supplied Composites

    Choose just the source and target composition families. The fixed
    four-coend square proves strength preservation of the existing natural
    map; no uniform choice over all profunctors is needed. *)

(** ** 两个给定复合之间的映射

    只选择来源及目标复合族。固定四 coend 方块证明原自然映射保持强度，
    不需要覆盖全部 profunctor 的统一选择。 *)

Section Preservation.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Context {Q Q' P P' : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}.
Context (SQ : HasProfStrength MC Q) (SQ' : HasProfStrength MC Q').
Context (SP : HasProfStrength MC P) (SP' : HasProfStrength MC P').
Context `{HC : !HasProfComp C C C Q P}.
Context `{HC' : !HasProfComp C C C Q' P'}.

(** The underlying transformation is precisely the old input map. *)

(** 底层变换恰为原输入映射。 *)

Lemma prof_comp_map_strength_hom (β : Q ⇒ Q') (α : P ⇒ P')
    (Hβ : is_prof_strength_hom SQ SQ' β)
    (Hα : is_prof_strength_hom SP SP' α)
  : is_prof_strength_hom
      (@ProfCompStrength C MC Q P SQ SP HC)
      (@ProfCompStrength C MC Q' P' SQ' SP' HC')
      (@ProfCompMapN C C C Q Q' P P' HC HC' β α).
Proof.
  intros Z X Y.
  exact (prof_comp_strength_input MC SQ SQ' SP SP' β α Hβ Hα Z X Y).
Defined.

End Preservation.

(** ** Strong Objects, Arrows and Specified Isomorphisms

    Fix the ambient monoidal structure. Keep each supplied composite and
    its strength once, then lift original maps and natural inverses. The
    same chosen coends underlie all projections. *)

(** ** 强对象、态射及指定同构

    固定环境幺半结构；每个给定复合及其强度只存一次，再提升原映射及自然逆。
    所有投影使用同一选定 coend。 *)

Section StrongOperations.
Context {C : Cat} (MC : MonoidalCat C).

(** Bundle the original composite functor and its accepted strength. *)

(** 打包原复合函子及其已验收强度。 *)

Program Definition StrongProfComp (Q P : StrongProf MC)
    `{HC : !HasProfComp C C C Q P}
  : StrongProf MC
  :=
  {|StrongProfF := @ProfComp C C C Q P HC
  ; hasProfStrength := @ProfCompStrength C MC Q P
      (hasProfStrength Q) (hasProfStrength P) HC
  |}.

(** Retain the original natural input map and only add its preservation
    witness. Source and target composition choices are independent. *)

(** 保留原自然输入映射，只增加其保持性见证；来源及目标复合选择独立。 *)

Definition StrongProfCompMap {Q Q' P P' : StrongProf MC}
    `{HC : !HasProfComp C C C Q P}
    `{HC' : !HasProfComp C C C Q' P'}
    (β : StrongProfHomS MC Q Q') (α : StrongProfHomS MC P P')
  : StrongProfHomS MC (StrongProfComp Q P) (StrongProfComp Q' P')
  := (@ProfCompMapN C C C Q Q' P P' HC HC' β.1 α.1;
      prof_comp_map_strength_hom MC
        (hasProfStrength Q) (hasProfStrength Q')
        (hasProfStrength P) (hasProfStrength P') β.1 α.1 β.2 α.2).

(** Equality of input transformations suffices for equality of lifted
    maps; preservation witnesses are retained but never compared. *)

(** 输入变换相等即足以使提升映射相等；保持性见证被保留，但从不比较。 *)

Global Instance strong_prof_comp_map_proper {Q Q' P P' : StrongProf MC}
    `{HC : !HasProfComp C C C Q P}
    `{HC' : !HasProfComp C C C Q' P'}
  : Proper (@carrier_equiv (StrongProfHomS MC Q Q') ==>
      @carrier_equiv (StrongProfHomS MC P P') ==>
      @carrier_equiv (StrongProfHomS MC
        (@StrongProfComp Q P HC) (@StrongProfComp Q' P' HC')))
      (@StrongProfCompMap Q Q' P P' HC HC').
Proof.
  intros [β Hβ] [β' Hβ'] Eβ [α Hα] [α' Hα'] Eα.
  exact (@prof_comp_map_proper C C C Q Q' P P' HC HC'
    β β' Eβ α α' Eα).
Defined.

(** Supplied input natural inverses give the same original coend map in
    reverse. Lift that chosen isomorphism through the general strong theory. *)

(** 给定输入自然逆在反向给出同一原 coend 映射；通过一般强结构理论提升该选定同构。 *)

Definition StrongProfCompIso {Q Q' P P' : StrongProf MC}
    `{HC : !HasProfComp C C C Q P}
    `{HC' : !HasProfComp C C C Q' P'}
    (β : StrongProfHomS MC Q Q') (α : StrongProfHomS MC P P')
    (Iβ : β.1 ⦂ Q ≅N Q') (Iα : α.1 ⦂ P ≅N P')
  : StrongProfComp Q P ≅[StrongProfCat MC] StrongProfComp Q' P'
  := StrongProfIso MC _ _ (StrongProfCompMap β α)
      (@prof_comp_map_iso C C C Q Q' P P' HC HC' β.1 α.1 Iβ Iα).

End StrongOperations.

(** ** The Strong Composition Bifunctor

    Supply coends only for pairs of strong profunctors, not every ordinary
    profunctor. The original map equality, identity and composition laws
    descend directly to subset hom-setoids; no preservation records are
    compared and importing this module selects no global model. *)

(** ** 强复合双函子

    只为强 profunctor 对提供 coend，不要求每个普通 profunctor 的复合。
    原映射相等、恒等及复合律直接下降到子集 Hom 广集，不比较保持性记录，
    导入本模块不选择全局模型。 *)

Section Bifunctor.
Context {C : Cat} (MC : MonoidalCat C).
Context (HC : ∀ Q P : StrongProf MC, HasProfComp C C C Q P).

(** The two arguments retain ordinary composition order, left after right;
    generating pairs retain execution order, right then left. *)

(** 两个变元保留通常复合次序，即左在右之后；生成对保留执行次序，即先右后左。 *)

Program Definition StrongProfCompF
  : Fct (StrongProfCat MC ×C StrongProfCat MC) (StrongProfCat MC)
  :=
  {|F0 QP := @StrongProfComp C MC (fst QP) (snd QP)
      (HC (fst QP) (snd QP))
  ; F1 QP QP' βα := @StrongProfCompMap C MC
      (fst QP) (fst QP') (snd QP) (snd QP')
      (HC (fst QP) (snd QP)) (HC (fst QP') (snd QP'))
      (fst βα) (snd βα)
  |}.
Next Obligation.
  intros [β α] [β' α'] [H K].
  exact (@prof_comp_map_proper C C C _ _ _ _ _ _
    β.1 β'.1 H α.1 α'.1 K).
Defined.
Next Obligation.
  destruct X as [Q P]. exact (@prof_comp_map_id C C C Q P (HC Q P)).
Defined.
Next Obligation.
  destruct X as [Q P], Y as [Q' P'], Z as [Q'' P''],
    f as [β' α'], g as [β α].
  exact (@prof_comp_map_comp C C C Q Q' Q'' P P' P''
    (HC Q P) (HC Q' P') (HC Q'' P'') β'.1 β.1 α'.1 α.1).
Defined.

(** Forgetting the lifted arrow retains the original composite map in
    designated natural equality, independently of preservation witnesses. *)

(** 忘却提升后的态射，在指定自然相等下保留原复合映射，不依赖保持性见证。 *)

Lemma strong_prof_comp_fmap {Q Q' P P' : StrongProf MC}
    (β : StrongProfHomS MC Q Q') (α : StrongProfHomS MC P P')
  : fmap (StrongProfForgetF MC)
      (fmap StrongProfCompF (X := (Q,P)) (Y := (Q',P')) (β,α)) ≈N
      @ProfCompMapN C C C Q Q' P P' (HC Q P) (HC Q' P') β.1 α.1.
Proof. intros XY v. reflexivity. Defined.

End Bifunctor.
