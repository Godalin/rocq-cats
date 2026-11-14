From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  DTT.CwF
  DTT.Context.Extension.
From Cats Require Import
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat.

(** * Context Extensions along Designated Type Equality *)

(** * 沿指定类型相等转换上下文扩张 *)

Section ConversionSubstitution.
Context {C : Cat} (T : Fct (C^op) FamCat).

(** Conversion commutes with substitution and the conversion associated to a
    commuting triangle of base substitutions. *)

(** 转换与替换相容，也与基底替换交换三角形产生的转换相容。 *)

Theorem tm_conv_sub_comm {Γ Δ Θ : @Ob C} {A B : Ty T Γ} (e : A ≈S B)
    (σ : Hom Δ Γ) (τ : Hom Θ Δ) {ρ : Hom Θ Γ} (H : σ ∘ τ ≈ ρ)
    (t : Tm T Δ A[σ]Ty[T])
  : ty_sub_comm T B σ τ H ▸[T] (e[σ]Eq[T] ▸[T] t)[τ]Tm[T] ≈S
    e[ρ]Eq[T] ▸[T] (ty_sub_comm T A σ τ H ▸[T] t[τ]Tm[T]).
Proof.
  transitivity (ty_sub_comm T B σ τ H ▸[T]
    (e[σ]Eq[T][τ]Eq[T] ▸[T] t[τ]Tm[T])).
  - apply func_proper. apply tm_sub_conv.
  - transitivity (transitivity e[σ]Eq[T][τ]Eq[T] (ty_sub_comm T B σ τ H)
      ▸[T] t[τ]Tm[T]).
    + symmetry. apply tm_conv_comp.
    + apply tm_conv_comp.
Qed.

End ConversionSubstitution.

(** ** Mapping Extensions along Type Equality

    Fix a family-valued presheaf [T] with chosen context extensions. Use its
    generic term and conversion to map extensions along designated type
    equality. *)

(** ** 沿类型相等映射扩张

    固定具有选定上下文扩张的族值预层 [T]，用泛项及转换沿指定类型相等映射扩张。 *)

Section ContextConversionMap.
Context {C : Cat} (T : Fct (C^op) FamCat) `{HC : !HasContextExtension T}.

(** Map context extensions along designated equality of their types. *)

(** 沿指定类型相等映射上下文扩张。 *)

Definition context_conv {Γ : @Ob C} {A B : Ty T Γ} (e : A ≈S B)
  : Hom (Γ ▹[T] A) (Γ ▹[T] B)
  := ⟨context_proj T A; e[context_proj T A]Eq[T] ▸[T] context_var T A⟩[T, B].

End ContextConversionMap.

Notation "e '^Ext[' T ']'" := (context_conv T e)
  (at level 35, format "e ^Ext[ T ]") : cat_scope.

(** ** Coherence of Context Conversion

    With the same chosen extensions for [T], prove that conversion preserves
    projection and generic terms, composes coherently and gives an
    isomorphism. *)

(** ** 上下文转换的相干性

    在 [T] 的同一选定扩张下，证明转换保持投影与泛项、满足复合相干性，并给出同构。 *)

Section ContextConversion.
Context {C : Cat} (T : Fct (C^op) FamCat) `{HC : !HasContextExtension T}.

(** Context conversion preserves the display projection. *)

(** 上下文转换保持显示投影。 *)

Definition context_conv_proj {Γ : @Ob C} {A B : Ty T Γ} (e : A ≈S B)
  : context_proj T B ∘ e^Ext[T] ≈ context_proj T A
  := context_pair_β1 T B (context_proj T A)
    (e[context_proj T A]Eq[T] ▸[T] context_var T A).

(** Context conversion preserves the generic term after type conversion. *)

(** 上下文转换在类型转换后保持泛项。 *)

Theorem context_conv_var {Γ : @Ob C} {A B : Ty T Γ} (e : A ≈S B)
  : ty_sub_comm T B (context_proj T B) (e^Ext[T]) (context_conv_proj e)
      ▸[T] (context_var T B)[e^Ext[T]]Tm[T] ≈S
    e[context_proj T A]Eq[T] ▸[T] context_var T A.
Proof. apply context_pair_β2. Qed.

(** Changing equality witnesses leaves the resulting action equal. *)

(** 改变相等见证后，所得作用仍然相等。 *)

Theorem context_conv_witness_independent {Γ : @Ob C} {A B : Ty T Γ}
    (e d : A ≈S B)
  : e^Ext[T] ≈ d^Ext[T].
Proof. apply context_pair_proper. apply tm_conv_witness_independent. Qed.

(** Context conversion sends a pairing to the pairing of the converted term. *)

(** 上下文转换将配对送到转换后项的配对。 *)

Theorem context_conv_pair {Γ Δ : @Ob C} {A B : Ty T Γ} (e : A ≈S B)
    (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
  : e^Ext[T] ∘ ⟨σ; t⟩[T, A] ≈ ⟨σ; e[σ]Eq[T] ▸[T] t⟩[T, B].
Proof.
  transitivity ⟨context_proj T A ∘ ⟨σ; t⟩[T, A];
    ty_sub_comp T (context_proj T A) ⟨σ; t⟩[T, A] B ▸[T]
      (e[context_proj T A]Eq[T] ▸[T] context_var T A)[⟨σ; t⟩[T, A]]Tm[T]⟩[T, B].
  - apply context_pair_comp.
  - apply (context_pair_equiv T B (context_pair_β1 T A σ t)).
    transitivity (ty_sub_comm T B (context_proj T A) ⟨σ; t⟩[T, A]
      (context_pair_β1 T A σ t) ▸[T]
        (e[context_proj T A]Eq[T] ▸[T] context_var T A)[⟨σ; t⟩[T, A]]Tm[T]).
    + symmetry. apply tm_conv_comp.
    + transitivity (e[σ]Eq[T] ▸[T]
        (ty_sub_comm T A (context_proj T A) ⟨σ; t⟩[T, A]
          (context_pair_β1 T A σ t) ▸[T] (context_var T A)[⟨σ; t⟩[T, A]]Tm[T])).
      * apply tm_conv_sub_comm.
      * apply func_proper. apply context_pair_β2.
Qed.

(** Compatibility with identities for [context_conv]. *)

(** [context_conv] 与恒等的相容性。 *)

Theorem context_conv_id {Γ : @Ob C} {A : Ty T Γ} (e : A ≈S A)
  : e^Ext[T] ≈ id.
Proof.
  symmetry. apply context_pair_unique. exists (comp_id_r (context_proj T A)).
  transitivity (context_var T A).
  - transitivity (ty_sub_id T A[context_proj T A]Ty[T]
      ▸[T] (context_var T A)[id]Tm[T]).
    + apply tm_conv_witness_independent.
    + apply tm_sub_id.
  - symmetry. apply tm_conv_id.
Qed.

(** Compatibility with composition for [context_conv]. *)

(** [context_conv] 与复合的相容性。 *)

Theorem context_conv_comp {Γ : @Ob C} {A B D : Ty T Γ}
    (e : A ≈S B) (d : B ≈S D) (r : A ≈S D)
  : r^Ext[T] ≈ d^Ext[T] ∘ e^Ext[T].
Proof.
  symmetry. transitivity ⟨context_proj T A;
    d[context_proj T A]Eq[T] ▸[T]
      (e[context_proj T A]Eq[T] ▸[T] context_var T A)⟩[T, D].
  - apply context_conv_pair.
  - apply context_pair_proper. symmetry. apply tm_conv_comp.
Qed.

(** Context conversions along opposite equalities are mutually inverse. *)

(** 沿反向相等的上下文转换互逆。 *)

Theorem context_conv_inv {Γ : @Ob C} {A B : Ty T Γ}
    (e : A ≈S B) (d : B ≈S A)
  : d^Ext[T] ∘ e^Ext[T] ≈ id.
Proof.
  transitivity ((reflexivity A)^Ext[T]).
  - symmetry. apply context_conv_comp.
  - apply context_conv_id.
Qed.

(** Context conversion is an invertible arrow. *)

(** 上下文转换是可逆箭头。 *)

Definition context_conv_is_iso {Γ : @Ob C} {A B : Ty T Γ} (e : A ≈S B)
  : is_iso (e^Ext[T]).
Proof. exists ((symmetry e)^Ext[T]). split; apply context_conv_inv. Defined.

(** Equal types induce an isomorphism of their context extensions. *)

(** 相等类型诱导其上下文扩张的同构。 *)

Definition context_conv_iso {Γ : @Ob C} {A B : Ty T Γ} (e : A ≈S B)
  : (Γ ▹[T] A) ≅[C] (Γ ▹[T] B)
  := (e^Ext[T]; context_conv_is_iso e).

End ContextConversion.
