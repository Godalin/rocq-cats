From Cats.STLC Require Export
  EtaSource
  PartialRenaming.

(** * Observing a Function Eta Root

    Function eta applies a weakened function to the newest variable. That
    variable's indexed marker exposes its declared type. This permits an
    observer to recover the function at the correct type without comparing
    hidden type annotations. Partial renaming then cancels weakening. *)

(** * 观测函数 η 根

    函数 η 将弱化后的函数应用于最新变量。该变量的索引标记暴露其声明类型，
    因此可以在正确类型处恢复函数，无须比较隐藏的类型注解。随后由部分重命名
    消去弱化。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Fresh Application Observers

    Fix arbitrary base labels. Observers inspect constructors and the
    newest-variable marker; they make no equality decision on labels. *)

(** ** 新鲜应用观测

    固定任意基标签。观测检查构造器与最新变量标记，不对标签作相等判定。 *)

Section FreshApplications.
Context {B : Type}.

(** Recognize an actual variable occurrence, retaining its typed position. *)

(** 识别实际变量出现，保留其带类型位置。 *)

Definition variable_position {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : option (Var Γ A)
  := match t with tm_var x => Some x | _ => None end.

(** When an argument is the newest variable, its marker aligns the
    function domain with the most recent context declaration. *)

(** 当实参为最新变量时，其标记将函数定义域与上下文的最新声明对齐。 *)

Definition newest_function {Γ : Ctx B} {A U V : Ty B}
    (f : Tm (Γ ▻ A) (U ⇒ V)) (x : Var (Γ ▻ A) U)
  : option (Tm (Γ ▻ A) (A ⇒ V)).
Proof.
  destruct x as [x | x]; [exact None |].
  destruct x. exact (Some f).
Defined.

(** Optional function of an application to the newest variable. At an
    empty context there is no newest declaration to observe. *)

(** 应用于最新变量的项所含的可选函数。空上下文中没有最新声明可供观测。 *)

Definition FreshFunction (Γ : Ctx B) (U : Ty B)
  : Type
  := match Γ with
      | ctx_empty => unit
      | ctx_snoc Δ A => option (Tm (Δ ▻ A) (A ⇒ U))
      end.

(** An absent fresh function, uniformly over contexts. *)

(** 在全部上下文中一致表示缺失的新鲜函数。 *)

Definition fresh_function_none (Γ : Ctx B) (U : Ty B)
  : FreshFunction Γ U.
Proof. destruct Γ; exact tt || exact None. Defined.

(** Read the application and variable constructors; no dependent injection
    of applications is used. *)

(** 读取应用与变量构造器，不使用应用项的依赖单射消去。 *)

Definition fresh_function {Γ : Ctx B} {U : Ty B} (t : Tm Γ U)
  : FreshFunction Γ U.
Proof.
  destruct t.
  - exact (fresh_function_none _ _).
  - exact (fresh_function_none _ _).
  - exact (fresh_function_none _ _).
  - exact (fresh_function_none _ _).
  - exact (fresh_function_none _ _).
  - exact (fresh_function_none _ _).
  - destruct Γ as [| Γ A']; [exact tt |].
    exact (match variable_position t2 with
      | Some x => newest_function t1 x
      | None => None
      end).
Defined.

End FreshApplications.

(** A fixed function eta source has exactly its displayed target.
    Applying the fresh-function observer aligns the hidden domain;
    the transparent left inverse of weakening recovers the raw target. *)

(** 固定函数 η 来源恰有其所显示的目标。新鲜函数观测对齐隐藏定义域；弱化的
    透明左逆恢复原始目标。 *)

Definition root_eta_function_unique@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A U : Ty B} (f v : Tm Γ (A ⇒ U))
    (h : RootEtaContract@{b e} (ƛ (f⟨wkRen⟩ · (# var_zero))) v)
  : f = v.
Proof.
  pose proof (root_eta_source h) as k. cbn [EtaRootSource lambda_body] in k.
  pose proof (f_equal (λ p : option (Tm (Γ ▻ A) U),
    match p with Some w => w | None => f⟨wkRen⟩ · (# var_zero) end) k)
    as body_eq.
  pose proof (f_equal fresh_function body_eq) as q.
  change (Some f⟨@ren_weaken B Γ A⟩ =
    Some v⟨@ren_weaken B Γ A⟩) in q.
  apply (rename_weaken_injective (A := A) f v).
  exact (f_equal (λ p : option (Tm (Γ ▻ A) (A ⇒ U)),
    match p with Some w => w | None => f⟨wkRen⟩ end) q).
Defined.
