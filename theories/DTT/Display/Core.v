From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Pullback
  Instance.Set.Core.

(** * Coherent Display Maps over a Type Presheaf

    Types use the specified equality of a set-valued presheaf. Display maps
    carry its action on equality and chosen substitution pullbacks; no terms,
    terminal context or pullbacks of arbitrary arrows are assumed. *)

(** * 类型预层上的相干显示映射

    类型使用集合值预层的指定相等。显示映射承载类型相等的作用和选定替换拉回，不
    假设项、终上下文或任意箭头的拉回。 *)

Section TypePresheaf.
Context {C : Cat} (P : Functor (C^op) SetCat).

(** The type-presheaf action on a context substitution. *)

(** 类型预层在上下文替换上的作用。 *)

Definition type_sub {Γ Δ : @Ob C} (σ : Hom Δ Γ)
  : P Γ →r P Δ
  := fmap P σ.

(** The type-presheaf action preserves designated type equality. *)

(** 类型预层的作用保持指定类型相等。 *)

Definition type_eq_sub {Γ Δ : @Ob C} (σ : Hom Δ Γ) {A B : P Γ} (e : A ≈S B)
  : type_sub σ A ≈S type_sub σ B
  := @func_proper _ _ (type_sub σ) _ _ e.

(** Compatibility with identities for [type_sub]. *)

(** [type_sub] 与恒等的相容性。 *)

Definition type_sub_id {Γ : @Ob C} (A : P Γ)
  : type_sub id A ≈S A
  := functor_id (C^op) SetCat P A.

(** Compatibility with composition for [type_sub]. *)

(** [type_sub] 与复合的相容性。 *)

Definition type_sub_comp {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (τ : Hom Θ Δ) (A : P Γ)
  : type_sub τ (type_sub σ A) ≈S type_sub (σ ∘ τ) A
  := symmetry (functor_comp (C^op) SetCat P τ σ) A.

(** Equal substitutions induce equal type-presheaf actions. *)

(** 相等替换诱导相等的类型预层作用。 *)

Definition type_sub_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ} (H : σ ≈ σ') (A : P Γ)
  : type_sub σ A ≈S type_sub σ' A
  := @functor_fmap_proper (C^op) SetCat P Γ Δ σ σ' H A.

End TypePresheaf.

Notation "A '[' σ ']TyF[' P ']'" := (type_sub P σ A)
  (at level 8, left associativity, format "A [ σ ]TyF[ P ]") : cat_scope.
Notation "e '[' σ ']EqF[' P ']'" := (type_eq_sub P σ e)
  (at level 8, left associativity, format "e [ σ ]EqF[ P ]") : cat_scope.

(** Selected display projections with coherent type conversion and
    substitution pullbacks. *)

(** 带相干类型转换和替换拉回的选定显示投影。 *)

Class HasDisplay (C : Cat) (P : Functor (C^op) SetCat)
  :=
  { Display {Γ : @Ob C} (A : P Γ) : @Ob C
  ; display_proj {Γ : @Ob C} (A : P Γ) : Hom (Display A) Γ
  ; display_conv {Γ : @Ob C} {A B : P Γ} (e : A ≈S B) : Hom (Display A) (Display B)
  ; display_conv_proj {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
    : display_proj B ∘ display_conv e ≈ display_proj A
  ; display_conv_id {Γ : @Ob C} {A : P Γ} (e : A ≈S A)
    : display_conv e ≈ id
  ; display_conv_comp {Γ : @Ob C} {A B D : P Γ}
      (e : A ≈S B) (d : B ≈S D) (r : A ≈S D)
    : display_conv r ≈ display_conv d ∘ display_conv e
  ; display_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
    : Hom (Display A[σ]TyF[P]) (Display A)
  ; display_lift_universal {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
    : is_pullback σ (display_proj A) (Display A[σ]TyF[P])
        (display_proj A[σ]TyF[P]) (display_lift σ A)
  ; display_lift_id {Γ : @Ob C} (A : P Γ)
    : display_lift id A ≈ display_conv (type_sub_id P A)
  ; display_lift_comp {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (τ : Hom Θ Δ) (A : P Γ)
    : display_lift σ A ∘ display_lift τ A[σ]TyF[P] ≈
      display_lift (σ ∘ τ) A ∘ display_conv (type_sub_comp P σ τ A)
  ; display_lift_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ} (H : σ ≈ σ') (A : P Γ)
    : display_lift σ A ≈ display_lift σ' A ∘ display_conv (type_sub_equiv P H A)
  ; display_lift_conv {Γ Δ : @Ob C} (σ : Hom Δ Γ) {A B : P Γ} (e : A ≈S B)
    : display_lift σ B ∘ display_conv e[σ]EqF[P] ≈ display_conv e ∘ display_lift σ A
  }.

Arguments Display {_} _ {_ _} _.
Arguments display_proj {_} _ {_ _} _.
Arguments display_conv {_} _ {_ _ _ _} _.
Arguments display_lift {_} _ {_ _ _} _ _.

Notation "Γ '▹D[' P ']' A" := (Display P (Γ := Γ) A)
  (at level 40, left associativity, format "Γ  ▹D[ P ]  A") : cat_scope.
Notation "e '^D[' P ']'" := (display_conv P e)
  (at level 35, format "e ^D[ P ]") : cat_scope.
Notation "σ '^D[' P ',' A ']'" := (display_lift P σ A)
  (at level 35, format "σ ^D[ P ,  A ]") : cat_scope.

(** ** Conversion and Lifting for Displays

    Fix a setoid-valued presheaf [P] with chosen display structure over [C].
    Derive independence and invertibility of conversion and the projection
    equation for display lifts. *)

(** ** 显示结构的转换与提升

    固定 [C] 上带选定显示结构的广集值预层 [P]，导出转换的见证无关性与可逆性，以及显示提升的投影方程。 *)

Section DisplayLaws.
Context {C : Cat} (P : Functor (C^op) SetCat) `{HD : !HasDisplay C P}.

(** Any two witnesses of the same designated type equality act identically.
    Inverses use symmetry of that equality, rather than an additional choice. *)

(** 同一指定类型相等的任意两个见证作用一致；逆由相等的对称性给出，不再额外选取。 *)

Theorem display_conv_witness_independent {Γ : @Ob C} {A B : P Γ} (e d : A ≈S B)
  : e^D[P] ≈ d^D[P].
Proof.
  transitivity ((reflexivity B)^D[P] ∘ d^D[P]).
  - apply display_conv_comp.
  - rewrite display_conv_id. apply comp_id_l.
Qed.

(** Conversions along opposite type equalities compose to identity. *)

(** 沿反向类型相等的转换复合为恒等。 *)

Theorem display_conv_inv {Γ : @Ob C} {A B : P Γ} (e : A ≈S B) (d : B ≈S A)
  : d^D[P] ∘ e^D[P] ≈ id.
Proof.
  transitivity ((reflexivity A)^D[P]).
  - symmetry. apply display_conv_comp.
  - apply display_conv_id.
Qed.

(** Each display conversion is invertible. *)

(** 每个显示转换都可逆。 *)

Definition display_conv_is_iso {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
  : is_iso (e^D[P]).
Proof. exists ((symmetry e)^D[P]). split; apply display_conv_inv. Defined.

(** Equal types have isomorphic display objects over their common context. *)

(** 相等类型在共同上下文上具有同构显示对象。 *)

Definition display_conv_iso {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
  : (Γ ▹D[P] A) ≅[C] (Γ ▹D[P] B)
  := (e^D[P]; display_conv_is_iso e).

(** The chosen display substitution square commutes. *)

(** 选定显示替换方形交换。 *)

Definition display_lift_proj {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
  : display_proj P A ∘ σ^D[P, A] ≈ σ ∘ display_proj P A[σ]TyF[P]
  := symmetry (fst (display_lift_universal σ A)).

End DisplayLaws.
