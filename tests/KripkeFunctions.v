From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Functor.FiniteProducts
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Lift
  Instance.Set.Kripke
  STLC.NormalPresheaf.

(** * Coherent Function Interface Regressions *)

(** * 相容函数接口回归检查 *)

(** ** Function Equality below World Equality

    Fix a category [C], presheaves [F], [G], [H] and a world [X], with
    function equality below world equality and a larger value carrier.
    Check coherent functions, lifted currying and their beta/eta laws. *)

(** ** 函数相等低于世界相等

    固定范畴 [C]、预层 [F]、[G]、[H] 及世界 [X]，使函数相等低于世界相等，
    值载体取更大界限。检查相容函数、提升柯里化及其 β、η 律。 *)

Section SmallFunctionEquality.
Universes b p e r l v.
Constraint b < p.
Constraint p < e.
Constraint e < r.
Constraint r < l.
Constraint l < v.
Context (C : Cat@{b b r l l}).
Context (F G H : Functor (C^op) SetCat@{b p _ _ _ _ _}).
Context (X : @Ob C).
Local Existing Instance SetCat_HasProduct.

(** Function values store world-respectfulness witnesses above their own
    pointwise equality. A smaller equality level must remain usable. *)

(** 函数值保存的世界保相等见证高于自身的逐点相等；较小的相等层级仍须可用。 *)

Definition separated_function_set
  : SetC@{v e}
  := KripkeFunctionS F G X.

Definition separated_function_presheaf
  : Functor (C^op) SetCat@{v e _ _ _ _ _}
  := KripkeFunctionF F G.

Definition separated_curry (α : PointwiseProductF H F ⇒ G)
  : @Nat (C^op) SetCat@{v e _ _ _ _ _}
      (LiftF@{v e _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F H)
      (KripkeFunctionF F G)
  := KripkeCurryN F G H α.

Definition separated_uncurry
    (β : @Nat (C^op) SetCat@{v e _ _ _ _ _}
      (LiftF@{v e _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F H)
      (KripkeFunctionF F G))
  : PointwiseProductF H F ⇒ G
  := KripkeUncurryN F G H β.

Definition separated_curry_beta (α : PointwiseProductF H F ⇒ G)
  : separated_uncurry (separated_curry α) ≈N α
  := kripke_curry_β F G H α.

Definition separated_curry_eta
    (β : @Nat (C^op) SetCat@{v e _ _ _ _ _}
      (LiftF@{v e _ _ _ _ _ _ _ _ _ _ _ _ _} ∘F H)
      (KripkeFunctionF F G))
  : separated_curry (separated_uncurry β) ≈N β
  := kripke_curry_η F G H β.

End SmallFunctionEquality.

(** ** Function Equality above World Equality

    Fix [C], [F] and [G] with function equality above world equality.
    Check that the coherent-function presheaf retains distinct bounds. *)

(** ** 函数相等高于世界相等

    固定 [C]、[F]、[G]，使函数相等高于世界相等，检查相容函数预层仍保留
    不同的大小界限。 *)

Section LargerFunctionEquality.
Universes b r p e l v.
Constraint b < r.
Constraint r < p.
Constraint p < e.
Constraint e < l.
Constraint l < v.
Context (C : Cat@{b b r l l}).
Context (F G : Functor (C^op) SetCat@{b p _ _ _ _ _}).

(** Function equality can also exceed world equality without forcing the
    carrier, the value relation and the category laws to share a level. *)

(** 函数相等也可高于世界相等，且不迫使载体、值关系与范畴律共用一个层级。 *)

Definition larger_function_equality_presheaf
  : Functor (C^op) SetCat@{v e _ _ _ _ _}
  := KripkeFunctionF F G.

End LargerFunctionEquality.

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** ** Currying over Syntax Presheaves

    Fix a signature, types [A] and [U], and a context [Γ]. Enable the
    chosen setoid product and check captured normal values and currying
    directly in syntax presheaves. *)

(** ** 语法预层上的柯里化

    固定签名、类型 [A]、[U] 和上下文 [Γ]，启用选定广集积，直接在语法预层
    中检查捕获的正规值与柯里化。 *)

Section SyntaxComputations.
Context {B : Type} (A U : Ty B) (Γ : Ctx B).
Local Existing Instance SetCat_HasProduct.

(** Currying the first projection yields a constant semantic function,
    whose captured normal form is renamed in each future context. *)

(** 柯里化第一投影得到常值语义函数，其捕获的正规形在每个未来上下文中重命名。 *)

Definition captured_normal_function (v : Nf Γ A)
  : KripkeFunction (NfPsh U) (NfPsh A) Γ
  := kripke_curry_at (NfPsh U) (NfPsh A) (NfPsh A)
      (PointwiseFstN _ _ (NfPsh A) (NfPsh U)) Γ v.

(** Applying in an extended context computes without evaluating proof fields. *)

(** 在扩张上下文中应用时，无须计算证明字段便可直接得到结果。 *)

Example captured_function_under_binder (v : Nf Γ A)
    (x : Nf (Γ ▻ U) U)
  : captured_normal_function v (Γ ▻ U) wkRen x = v⟨wkRen⟩nf.
Proof. reflexivity. Qed.

Example reindexed_function_computes (v : Nf Γ A)
    (x : Nf (Γ ▻ U) U)
  : kripke_eval (NfPsh U) (NfPsh A)
      (kripke_reindex (NfPsh U) (NfPsh A) wkRen
        (captured_normal_function v)) x =
      v⟨wkRen⟩nf.
Proof. reflexivity. Qed.

(** The generic beta and eta laws apply to syntax presheaves directly,
    with no STLC-specific transposition proof. *)

(** 一般 β、η 律直接适用于语法预层，无须 STLC 专用的转置证明。 *)

Definition syntax_curry_beta
    (α : PointwiseProductF (NfPsh A) (NfPsh U) ⇒ NfPsh A)
  : KripkeUncurryN _ _ _ (KripkeCurryN _ _ _ α) ≈N α
  := kripke_curry_β _ _ _ α.

Definition syntax_curry_eta
    (β : LiftF ∘F NfPsh A ⇒ KripkeFunctionF (NfPsh U) (NfPsh A))
  : KripkeCurryN _ _ _ (KripkeUncurryN _ _ _ β) ≈N β
  := kripke_curry_η _ _ _ β.

Definition syntax_curry_universal
    (α : PointwiseProductF (NfPsh A) (NfPsh U) ⇒ NfPsh A)
  : ∃ β : LiftF ∘F NfPsh A ⇒ KripkeFunctionF (NfPsh U) (NfPsh A),
      is_unique (λ β, KripkeUncurryN _ _ _ β ≈N α) β
  := kripke_curry_universal _ _ _ α.

End SyntaxComputations.
