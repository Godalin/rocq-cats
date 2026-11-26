From Cats.Set Require Import
  Subset.
From Cats Require Export
  Cat.Profunctor.Strength.
From Cats Require Import
  Cat.Isomorphism
  Instance.Set.Core.

Local Open Scope monoidal_scope.
Local Open Scope prof_scope.
Local Open Scope ob_scope.

(** * Strength-Preserving Natural Transformations

    A transformation of profunctors preserves strength when changing the
    value commutes with extending both ends by the same context. Keep the
    original transformation and Type-valued preservation witnesses. No
    coend, symmetry or bound on the base category's sizes is needed. *)

(** * 保持强度的自然变换

    Profunctor 的变换保持强度，意即改变值与在两端扩展同一上下文交换。
    保留原自然变换及 Type 值保持性见证，不需要 coend、对称性或基范畴大小界。 *)

(** ** Preservation on Existing Data

    Fix a monoidal category and independent value carrier/equality bounds.
    The supplied strengths use that same monoidal structure. Preservation
    is stable under natural equality, identities, vertical composition and
    specified natural inverses. *)

(** ** 已有数据上的保持性

    固定幺半范畴及独立的值载体／相等大小界；给定强度使用同一幺半结构。
    保持性对自然相等、恒等、竖直复合及指定自然逆稳定。 *)

Section Preservation.
Universes u p.
Context {C : Cat} {MC : HasMonoidal C}.

(** Only the context square is new; endpoint naturality belongs to the
    original natural transformation and is not stored a second time. *)

(** 只增加上下文方块；端点自然性属于原自然变换，不重复存储。 *)

Definition is_prof_strength_hom
    {P Q : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}
    (SP : HasProfStrength MC P) (SQ : HasProfStrength MC Q) (α : P ⇒ Q)
  : Type
  := ∀ Z X Y : @Ob C,
      (α (Z ⊗ X,Z ⊗ Y) ∘r pstrength[SP; Z]) ≈f
        (pstrength[SQ; Z] ∘r α (X,Y)).

(** Changing a transformation by designated natural equality transports
    its preservation witnesses without identifying their records. *)

(** 按指定自然相等改变变换可运输保持性见证，不识别其记录。 *)

Lemma prof_strength_hom_equiv
    {P Q : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}
    (SP : HasProfStrength MC P) (SQ : HasProfStrength MC Q)
    (α β : P ⇒ Q) (E : α ≈N β)
  : is_prof_strength_hom SP SQ α ↔ is_prof_strength_hom SP SQ β.
Proof.
  split; intros H Z X Y v.
  - change (β (Z ⊗ X,Z ⊗ Y) (pstrength[SP; Z] v) ≈S
      pstrength[SQ; Z] (β (X,Y) v)).
    transitivity (α (Z ⊗ X,Z ⊗ Y) (pstrength[SP; Z] v)).
    + symmetry. apply E.
    + transitivity (pstrength[SQ; Z] (α (X,Y) v)).
      * exact (H Z X Y v).
      * apply func_proper. apply E.
  - change (α (Z ⊗ X,Z ⊗ Y) (pstrength[SP; Z] v) ≈S
      pstrength[SQ; Z] (α (X,Y) v)).
    transitivity (β (Z ⊗ X,Z ⊗ Y) (pstrength[SP; Z] v)).
    + apply E.
    + transitivity (pstrength[SQ; Z] (β (X,Y) v)).
      * exact (H Z X Y v).
      * apply func_proper. symmetry. apply E.
Defined.

(** The original identity transformation preserves each chosen strength. *)

(** 原恒等变换保持每个选定强度。 *)

Lemma prof_strength_hom_id
    {P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}
    (SP : HasProfStrength MC P)
  : is_prof_strength_hom SP SP IdN.
Proof. intros Z X Y v. reflexivity. Defined.

(** The two supplied context squares compose pointwise; the underlying
    transformation is precisely the original vertical composite. *)

(** 两个给定上下文方块逐点复合，底层变换恰为原竖直复合。 *)

Lemma prof_strength_hom_comp
    {P Q R : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}
    (SP : HasProfStrength MC P) (SQ : HasProfStrength MC Q)
    (SR : HasProfStrength MC R) (β : Q ⇒ R) (α : P ⇒ Q)
    (Hβ : is_prof_strength_hom SQ SR β)
    (Hα : is_prof_strength_hom SP SQ α)
  : is_prof_strength_hom SP SR (β ∘Nv α).
Proof.
  intros Z X Y v.
  change (β (Z ⊗ X,Z ⊗ Y) (α (Z ⊗ X,Z ⊗ Y) (pstrength[SP; Z] v))
    ≈S pstrength[SR; Z] (β (X,Y) (α (X,Y) v))).
  transitivity (β (Z ⊗ X,Z ⊗ Y) (pstrength[SQ; Z] (α (X,Y) v))).
  - apply func_proper. exact (Hα Z X Y v).
  - exact (Hβ Z X Y (α (X,Y) v)).
Defined.

(** Invert the same context square through its two specified component
    isomorphisms. The general inverse-square theorem supplies the proof. *)

(** 通过两个指定分量同构反转同一上下文方块，证明由一般逆方块定理提供。 *)

Lemma prof_strength_hom_inverse
    {P Q : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}
    (SP : HasProfStrength MC P) (SQ : HasProfStrength MC Q)
    (α : P ⇒ Q) (Hα : is_prof_strength_hom SP SQ α) (I : α ⦂ P ≅N Q)
  : is_prof_strength_hom SQ SP (α ^-1N I).
Proof.
  intros Z X Y.
  exact (@iso_square_inv SetCat _ _ _ _
    (α (X,Y); I (X,Y)) (α (Z ⊗ X,Z ⊗ Y); I (Z ⊗ X,Z ⊗ Y))
    (pstrength[SP; Z]) (pstrength[SQ; Z]) (Hα Z X Y)).
Defined.

End Preservation.

(** A strong profunctor owns its one underlying mixed-variance functor
    and its strength relative to the named monoidal structure. Minks supplies
    [MakeStrongProf] and the unique native view [StrongProfToFct]. The
    [hasProfStrength] projection exposes that same stored choice to instance
    search; importing the module selects no strength for an arbitrary functor. *)

(** 强 profunctor 保存唯一底层混合变元函子，以及相对于具名幺半结构的强度。
    Minks 提供 [MakeStrongProf] 及唯一原生视图 [StrongProfToFct]。
    [hasProfStrength] 投影向实例搜索暴露同一存储选择；导入模块不为任意函子
    选取强度。 *)

Minks.Struct StrongProf@{u p +} {C : Cat} (MC : HasMonoidal C)
  extends Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})
  with hasProfStrength as hasProfStrength
    : HasProfStrength [C, MC, carrier].

Arguments MakeStrongProf {_ _} _ _.
Arguments StrongProfToFct {_ _} _.
Arguments hasProfStrength {_ _} _.

(** ** The Strong Profunctor Category

    Fix the ambient monoidal structure and value bounds. Subset hom-sets
    retain preservation evidence but compare only the underlying natural
    transformations. Identity, composition and specified inverses retain
    their original computational maps. *)

(** ** 强 Profunctor 范畴

    固定环境幺半结构及值大小界。子集 Hom 广集保留保持性见证，但只比较底层
    自然变换。恒等、复合及指定逆均保留其原可计算映射。 *)

Section Categories.
Context {C : Cat} (MC : HasMonoidal C).

(** Cut out strength-preserving transformations in the original Hom setoid. *)

(** 从原 Hom 广集中截取保持强度的变换。 *)

Definition StrongProfHomS (P Q : StrongProf MC)
  : SetC
  := SubsetS (@HomSet (FctCat ((C^op) ×C C) SetCat) P Q)
      (is_prof_strength_hom (hasProfStrength P) (hasProfStrength Q)).

(** Identity changes no value and keeps the original chosen strength. *)

(** 恒等不改变值，并保留原选定强度。 *)

Definition strong_prof_id (P : StrongProf MC)
  : StrongProfHomS P P
  := (IdN; prof_strength_hom_id (hasProfStrength P)).

(** Lift the original vertical composition, with its two preservation proofs. *)

(** 提升原竖直复合，并保留两项保持性证明。 *)

Definition strong_prof_comp {P Q R : StrongProf MC}
    (β : StrongProfHomS Q R) (α : StrongProfHomS P Q)
  : StrongProfHomS P R
  := (β.1 ∘Nv α.1; prof_strength_hom_comp
      (hasProfStrength P) (hasProfStrength Q) (hasProfStrength R)
      β.1 α.1 β.2 α.2).

(** The category laws are the original natural-transformation laws in
    designated equality, without proof irrelevance for the subset witnesses. *)

(** 范畴律就是指定相等下的原自然变换定律，不对隶属见证使用证明无关性。 *)

Program Definition StrongProfCat
  : Cat
  :=
  {|Ob := StrongProf MC
  ; HomSet := StrongProfHomS
  ; id := strong_prof_id
  ; comp _ _ _ := strong_prof_comp
  |}.
Next Obligation.
  intros [β Hβ] [β' Hβ'] Eβ [α Hα] [α' Hα'] Eα O.
  exact (comp_proper (β O) (β' O) (Eβ O) (α O) (α' O) (Eα O)).
Defined.
Next Obligation. intros O. exact (comp_id_r (f.1 O)). Defined.
Next Obligation. intros O. exact (comp_id_l (f.1 O)). Defined.
Next Obligation.
  intros O. exact (comp_assoc (f.1 O) (g.1 O) (h.1 O)).
Defined.

(** Forget only the strength and preservation witnesses, retaining the
    supplied underlying functor and transformation exactly. *)

(** 只忘却强度及保持性见证，完整保留给定底层函子和变换。 *)

Program Definition StrongProfForgetF
  : Fct StrongProfCat (ProfCat C C)
  :=
  {|fobj := StrongProfToFct
  ; fmap P Q α := α.1
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros α β E. exact E. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** Faithfulness follows from inherited natural equality. *)

(** 忠实性来自继承的自然相等。 *)

Lemma strong_prof_forget_faithful
  : is_faithful StrongProfForgetF.
Proof. intros P Q α β E. exact E. Defined.

(** Lift a supplied natural isomorphism, with its same forward and inverse
    maps. Preservation of the inverse comes from the general square lemma. *)

(** 用同一正向和逆向映射提升给定自然同构，逆的保持性来自一般方块引理。 *)

Program Definition StrongProfIso (P Q : StrongProf MC)
    (α : StrongProfHomS P Q) (I : α.1 ⦂ P ≅N Q)
  : P ≅[StrongProfCat] Q
  := (α; ((α.1 ^-1N I;
      prof_strength_hom_inverse (hasProfStrength P) (hasProfStrength Q)
        α.1 α.2 I); _)).
Next Obligation.
  split; intros XY.
  - exact (fst (I XY).2).
  - exact (snd (I XY).2).
Defined.

End Categories.
