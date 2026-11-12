From Cats.STLC Require Import Reification.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Lift
  Instance.Set.Kripke.

(** * Semantic Reification Interface Regressions *)

(** * 语义实化接口回归检查 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** ** Reification at Separated Bounds

    Fix [B], [A] and [Γ], separating signature, world equality,
    equational evidence, semantic values, world laws and both raised
    bounds. Check reflection, reification and their eta comparison. *)

(** ** 独立界限处的实化

    固定 [B]、[A]、[Γ]，分开签名、世界相等、等式证据、语义值、世界定律及
    两个提升界限，检查反射、实化与 η 比较。 *)

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

(** 语法、世界相等、等式见证、语义构造与范畴律均接受不同界限。 *)

Definition separated_type_reification
  : Reification A
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := TypeReification A.

(** Raise carrier and equality bounds separately, preserving the same
    internal semantic presheaf and all reflection/reification laws. *)

(** 分别提升载体与相等界限，保留同一个内部语义预层及全部反射/实化定律。 *)

Definition separated_raised_reification
  : Reification A (LiftF@{u p _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F
      SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := lift_reification separated_type_reification.

Definition separated_raised_reify_transformation
  : @Nat ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{u p _ _ _ _ _}
      (LiftF@{u p _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F
        SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
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

(** ** 提升相等低于提升载体

    固定 [B]、[A] 并取 [b < r < s < p < u < l]，检查提升相等低于提升载体
    时的提升接口。 *)

Section SmallerRaisedEquality.
Universes b r s p u l.
Constraint b < r.
Constraint r < s.
Constraint s < p.
Constraint p < u.
Constraint u < l.
Context (B : Type@{b}) (A : Ty B).

(** The raised equality bound may also be below the raised carrier bound. *)

(** 提升后的相等界限也可以低于提升后的载体界限。 *)

Definition smaller_raised_equality_reification
  : Reification A (LiftF@{u p _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F
      SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := lift_reification (TypeReification A).

Definition raised_semantic_family
  : Functor ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{u p _ _ _ _ _}
  := RaisedSemF A.

End SmallerRaisedEquality.

(** ** World Laws below Semantic Values

    Fix [B], [A] and [Γ] with [b < r < l < s]. Check reification and
    eta comparison when semantic values exceed the world-law bound. *)

(** ** 世界定律低于语义值

    固定 [B]、[A]、[Γ] 并取 [b < r < l < s]，检查语义值高于世界定律界限
    时的实化与 η 比较。 *)

Section SmallerWorldLawBound.
Universes b r l s.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Context (B : Type@{b}) (A : Ty B) (Γ : Ctx B).

(** World laws may live below the semantic bound. Same-level beta/eta
    evidence is still enough for the neutral round-trip theorem. *)

(** 世界定律可以低于语义界限；中性项往返定理仍只需与语法同层的 βη 见证。 *)

Definition smaller_world_law_reification
  : Reification A
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
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

(** ** 反射与实化的计算

    固定任意基标签 [p]、[q] 与上下文 [Γ]，检查基类型及复合类型处反射与实化
    的计算。 *)

Section Computations.
Context {B : Type} (p q : B) (Γ : Ctx B).

(** Reflection followed by reification computes an eta-long lambda even
    when the domain is itself a function. No correctness proof is executed. *)

(** 即使定义域自身是函数，反射后实化也直接计算出 η 长的 λ，不执行正确性证明。 *)

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

(** 反射的高阶头接受反射的函数变量，其语义应用将实参实化为长 λ。 *)

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

(** 所有单位值均实化为规范的单位语法树。 *)

Example semantic_unit_is_canonical (v : SemF (⊤ : Ty B) Γ)
  : reify_sem (TypeReification ⊤) Γ v = nf_unit.
Proof. reflexivity. Qed.

(** Lifting both operations cancels its outer wrapper computationally. *)

(** 同时提升两个操作后，外层包装通过计算直接抵消。 *)

Example lifted_reflection_computes (A : Ty B) (n : Ne Γ A)
  : reify_sem (lift_reification (TypeReification A)) Γ
      (reflect_ne (lift_reification (TypeReification A)) Γ n) =
    reify_sem (TypeReification A) Γ (reflect_ne (TypeReification A) Γ n).
Proof. reflexivity. Qed.

(** Natural-transformation wrappers preserve the same computation. *)

(** 自然变换包装保留相同的计算。 *)

Example reification_components_compute (A : Ty B) (n : Ne Γ A)
  : lower (ReifyN (TypeReification A) Γ
      (ReflectN (TypeReification A) Γ {|lower := n
                                     |})) =
      reify_sem (TypeReification A) Γ
        (reflect_ne (TypeReification A) Γ n).
Proof. reflexivity. Qed.

(** Function values are compared pointwise in all future contexts; that
    suffices for structural equality of the reified lambda trees. *)

(** 函数值在全部未来上下文中逐点比较，这足以推出实化所得 λ 树的结构相等。 *)

Example extensional_function_reification (A U : Ty B)
    (f g : SemF (A ⇒ U) Γ)
    (h : KripkeFunctionEq (SemF A) (SemF U) f g)
  : reify_sem (TypeReification (A ⇒ U)) Γ f =
      reify_sem (TypeReification (A ⇒ U)) Γ g.
Proof. apply reify_sem_proper. exact h. Qed.

(** Naturality is available through the public pair interface. *)

(** 自然性可通过公开的操作对接口调用。 *)

Example reification_renaming_interface (A : Ty B)
    (Δ : Ctx B) (ρ : Ren Δ Γ) (v : SemF A Γ)
  : reify_sem (TypeReification A) Δ (fmap (SemF A) ρ v) =
      (reify_sem (TypeReification A) Γ v)⟨ρ⟩nf.
Proof. apply reify_sem_rename. Qed.

End Computations.
