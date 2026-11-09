From Cats Require Export STLC.Completeness.Core.
From Cats Require Import
  Cat.Core
  Cat.CCC.

Local Open Scope cat_scope.

(** * Inhabitation Soundness and Completeness

    Validity here carries a morphism for each CCC model at the common
    bound used for equational validity. It is a uniform family of witnesses
    in [Type], rather than mere nonemptiness in one model. *)

(** * 可居留性的可靠性与完备性

    这里的有效性在与等式有效性相同的共同大小界内，为每个 CCC 模型携带
    一条态射。它是 [Type] 中统一给出的见证族，而非某个模型中的单纯非空性。 *)

Definition TmModelInhabited@{b e l +} {B : Type@{b}}
    (Γ : Ctx B) (A : Ty B)
  : Type
  := ∀ (C : Cat@{b b e l l}) (HC : CCC C) (I : B → @Ob C),
      (@Hom C) (@CtxI B C HC I Γ) (@TyI B C HC I A).

(** Interpret an intrinsically typed term in each chosen CCC model. *)

(** 在每个选定 CCC 模型中解释一个内在带类型的项。 *)

Definition tm_inhabitation_soundness@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : TmModelInhabited@{b e l _ _ _ _} Γ A
  := λ C HC I, @tm_interp B C HC I Γ A t.

(** Instantiate the model family with the syntactic CCC and recover a term
    using the canonical comparison maps. No normalization or choice is needed. *)

(** 将模型族实例化为语法 CCC，再由规范比较映射恢复一个项；
    无须正规化或选择原理。 *)

Definition tm_inhabitation_completeness@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B}
    (H : TmModelInhabited@{b e l _ _ _ _} Γ A)
  : Tm Γ A
  := tm_interp_canonical_inhabited
      (H (TyCat@{b e l} B) (TyCat_CCC B) (@ty_base B)).

(** This Type-valued equivalence bundles the two constructive maps; it makes
    no claim that terms or families of semantic witnesses are equal. Under
    Curry--Howard--Lambek it expresses provability completeness for unit,
    conjunction and implication, separately from beta/eta equality. *)

(** 此 Type 值等价打包两个构造性映射，不断言项或语义见证族相等。
    在 Curry--Howard--Lambek 对应下，它表达单位、合取与蕴含片段的可证性
    完备性，与 βη 等式完备性分开陈述。 *)

Definition tm_inhabitation_soundness_iff_completeness@{b e l +}
    {B : Type@{b}} (Γ : Ctx B) (A : Ty B)
  : Tm Γ A ↔ TmModelInhabited@{b e l _ _ _ _} Γ A
  := (tm_inhabitation_soundness, tm_inhabitation_completeness).
