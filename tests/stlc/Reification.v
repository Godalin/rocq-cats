From Cats.STLC Require Import Reification.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Lift
  Instance.Set.Kripke.

(** * Semantic Reification Interface Regressions *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** ** Reification at Separated Bounds

    Fix [B], [A] and [Γ], separating signature, world equality,
    equational evidence, semantic values, world laws and both raised
    bounds. Check reflection, reification and their eta comparison. *)

Section SeparatedBounds.
Universes b r e s l u p.
Constraint b < r.
Constraint r < e.
Constraint e < s.
Constraint s < l.
Constraint l < u.
Constraint u < p.
Context (B : Type@{b}) (A : Ty B) (Γ : Ctx B).

(** Syntax, world equality, equational evidence, semantic construction and
    category laws all accept distinct bounds. *)

Definition separated_type_reification
  : Reification A
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := TypeReification A.

(** Raise carrier and equality bounds separately, preserving the same
    internal semantic presheaf and all reflection/reification laws. *)

Definition separated_raised_reification
  : Reification A (LiftF@{u p _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F
      SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := lift_reification separated_type_reification.

Definition separated_raised_reify_transformation
  : @Nat ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{u p _ _ _ _ _}
      (LiftF@{u p _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F
        SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
      (LiftF@{u p _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F NfPsh A)
  := ReifyN separated_raised_reification.

Definition separated_neutral_soundness (n : Ne Γ A)
  : TmEq@{b e _} (embed_ne n)
      (embed_nf (reify_sem separated_type_reification Γ
        (reflect_ne separated_type_reification Γ n)))
  := reify_reflect_sound A Γ n.

End SeparatedBounds.

(** ** Raised Equality below Raised Carriers

    Fix [B] and [A] with [b < r < s < p < u < l]. Check the lifting
    interfaces when raised equality lies below the raised carrier. *)

Section SmallerRaisedEquality.
Universes b r s p u l.
Constraint b < r.
Constraint r < s.
Constraint s < p.
Constraint p < u.
Constraint u < l.
Context (B : Type@{b}) (A : Ty B).

(** The raised equality bound may also be below the raised carrier bound. *)

Definition smaller_raised_equality_reification
  : Reification A (LiftF@{u p _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F
      SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := lift_reification (TypeReification A).

Definition raised_semantic_family
  : Fct ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{u p _ _ _ _ _}
  := RaisedSemF A.

End SmallerRaisedEquality.

(** ** World Laws below Semantic Values

    Fix [B], [A] and [Γ] with [b < r < l < s]. Check reification and
    eta comparison when semantic values exceed the world-law bound. *)

Section SmallerWorldLawBound.
Universes b r l s.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Context (B : Type@{b}) (A : Ty B) (Γ : Ctx B).

(** World laws may live below the semantic bound. Same-level beta/eta
    evidence is still enough for the neutral round-trip theorem. *)

Definition smaller_world_law_reification
  : Reification A
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := TypeReification A.

Definition same_level_neutral_soundness (n : Ne Γ A)
  : TmEq@{b b _} (embed_ne n)
      (embed_nf (reify_sem smaller_world_law_reification Γ
        (reflect_ne smaller_world_law_reification Γ n)))
  := reify_reflect_sound A Γ n.

End SmallerWorldLawBound.

(** ** Computing Reflection and Reification

    Fix arbitrary base labels [p] and [q] and a context [Γ]. Check
    reflection and reification computations at base and composite types. *)

Section Computations.
Context {B : Type} (p q : B) (Γ : Ctx B).

(** Reflection followed by reification computes an eta-long lambda even
    when the domain is itself a function. No correctness proof is executed. *)

Example higher_order_reflection_computes
    (f : Ne Γ ((ty_base p ⇒ ty_base q) ⇒ ty_base q))
  : reify_sem (TypeReification _) Γ (reflect_ne (TypeReification _) Γ f) =
      nf_lam (nf_base (ne_app (f⟨wkRen⟩ne)
        (nf_lam (nf_base
          (ne_app (ne_var (var_succ var_zero))
            (nf_base (ne_var var_zero))))))).
Proof. reflexivity. Qed.

(** A reflected higher-order head accepts a reflected function variable;
    its semantic application reifies the argument to a long lambda. *)

Example reflected_application_computes
  : let Δ := Γ ▻ (ty_base p ⇒ ty_base q) ▻
        ((ty_base p ⇒ ty_base q) ⇒ ty_base q) in
    reify_sem (TypeReification (ty_base q)) Δ
      (kripke_eval (SemF (ty_base p ⇒ ty_base q)) (SemF (ty_base q))
        (reflect_ne (TypeReification _) Δ (ne_var var_zero))
        (reflect_ne (TypeReification _) Δ
          (ne_var (var_succ var_zero)))) =
    nf_base (ne_app (ne_var var_zero)
      (nf_lam (nf_base
        (ne_app (ne_var (var_succ (var_succ var_zero)))
          (nf_base (ne_var var_zero)))))).
Proof. reflexivity. Qed.

(** Unit values all reify to the canonical unit tree. *)

Example semantic_unit_is_canonical (v : SemF (⊤ : Ty B) Γ)
  : reify_sem (TypeReification ⊤) Γ v = nf_unit.
Proof. reflexivity. Qed.

(** Lifting both operations cancels its outer wrapper computationally. *)

Example lifted_reflection_computes (A : Ty B) (n : Ne Γ A)
  : reify_sem (lift_reification (TypeReification A)) Γ
      (reflect_ne (lift_reification (TypeReification A)) Γ n) =
    reify_sem (TypeReification A) Γ (reflect_ne (TypeReification A) Γ n).
Proof. reflexivity. Qed.

(** Natural-transformation wrappers preserve the same computation. *)

Example reification_components_compute (A : Ty B) (n : Ne Γ A)
  : lower (ReifyN (TypeReification A) Γ
      (ReflectN (TypeReification A) Γ {|lower := n
                                     |})) =
      reify_sem (TypeReification A) Γ
        (reflect_ne (TypeReification A) Γ n).
Proof. reflexivity. Qed.

(** Function values are compared pointwise in all future contexts; that
    suffices for structural equality of the reified lambda trees. *)

Example extensional_function_reification (A U : Ty B)
    (f g : SemF (A ⇒ U) Γ)
    (h : KripkeFunctionEq (SemF A) (SemF U) f g)
  : reify_sem (TypeReification (A ⇒ U)) Γ f =
      reify_sem (TypeReification (A ⇒ U)) Γ g.
Proof. apply reify_sem_proper. exact h. Qed.

(** Naturality is available through the public pair interface. *)

Example reification_renaming_interface (A : Ty B)
    (Δ : Ctx B) (ρ : Ren Δ Γ) (v : SemF A Γ)
  : reify_sem (TypeReification A) Δ (fmap (SemF A) ρ v) =
      (reify_sem (TypeReification A) Γ v)⟨ρ⟩nf.
Proof. apply reify_sem_rename. Qed.

End Computations.
