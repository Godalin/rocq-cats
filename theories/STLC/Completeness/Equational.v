From Cats Require Export STLC.Completeness.Core.
From Cats Require Import
  Cat.Core
  Cat.CCC.

(** * Equational Soundness and Completeness

    Soundness above applies to arbitrary model sizes. Completeness needs only
    a common universe bound containing the syntactic CCC; this avoids any
    universe of all categories or resizing principle. *)

(** * 等式可靠性与完备性

    前面的可靠性适用于任意模型大小。完备性只需要包含语法 CCC 的共同宇宙界，
    不构造所有范畴的宇宙，也不使用大小重设原理。 *)

Local Open Scope cat_scope.

(** Validity in all CCC models at a common bound. The object/hom bound is b,
    equality witnesses live at e, and category laws at l. Larger or differently
    arranged model universes remain covered separately by soundness. *)

(** 共同大小界内全部 CCC 模型的有效性：对象与 Hom 载体界为 b，相等见证界为 e，
    范畴律界为 l。更大或采用其他大小排列的模型仍由一般可靠性定理覆盖。 *)

Definition TmModelEq@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type
  := ∀ (C : Cat@{b b e l l}) (HC : CCC C) (I : B → @Ob C),
      @HomEq C _ _ (@tm_interp B C HC I Γ A t)
        (@tm_interp B C HC I Γ A u).

Notation "t '≈CCC' u" := (TmModelEq t u)
  (at level 50, no associativity) : stlc_tm_scope.

(** The syntactic model supplies the reverse implication; no normalization,
    decidability, choice, proof irrelevance or extensionality axiom is used. *)

(** 语法模型给出反方向；不使用正规化、可判定性、选择、证明无关性或外延公理。 *)

Theorem tm_soundness_iff_completeness@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : TmEq@{b e _} t u ↔ TmModelEq@{b e l _ _ _ _} t u.
Proof.
  split.
  - intros H C HC I. exact (@tm_interp_sound B C HC I Γ A t u H).
  - intros H. apply tm_interp_canonical_reflect.
    exact (H (TyCat@{b e l} B) (TyCat_CCC B) (@ty_base B)).
Defined.
