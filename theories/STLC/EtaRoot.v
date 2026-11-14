From Cats.STLC Require Export
  EtaSource
  PartialRenaming
  VariableProduct.

(** * Observing Eta Roots

    Function eta applies a weakened function to the newest variable. That
    variable's indexed marker exposes its declared type. This permits an
    observer to recover the function at the correct type without comparing
    hidden type annotations. Partial renaming then cancels weakening.

    For products, the two projections determine the optional pair
    components through their root beta observations. This identifies
    pair targets of competing eta roots without injecting projections.
    The two typed variable views likewise identify variable targets,
    preserving their positions and binding markers. *)

(** * 观测 η 根

    函数 η 将弱化后的函数应用于最新变量。该变量的索引标记暴露其声明类型，
    因此可以在正确类型处恢复函数，无须比较隐藏的类型注解。随后由部分重命名
    消去弱化。

    对于积，两个投影通过各自的根 β 观测确定可选的配对分量。因此可以识别
    竞争 η 根的配对目标，无须对投影作构造器单射消去。两个带类型变量视图
    同样识别变量目标，保持其位置与绑定标记。 *)

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

(** A discovered variable position reconstructs the term itself. *)

(** 发现的变量位置重构项本身。 *)

Definition variable_position_spec {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : match variable_position t return Type with
    | Some x => t = # x
    | None => unit
    end.
Proof. destruct t; reflexivity || exact tt. Defined.

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

(** Restricting a defined root eta source also defines its target and
    retains the root contraction. The function case uses the commuting
    square for weakening; no test for unused variables is postulated. *)

(** 若根 η 来源的限制有定义，则其目标的限制也有定义，且保持根收缩。函数
    分支使用弱化的交换方块，不假定未使用变量的额外测试。 *)

Definition root_eta_partial@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : RootEtaContract@{b e} t u)
  : ∀ (Δ : Ctx B) (σ : PartialRen Δ Γ) (t' : Tm Δ A),
      partial_rename t Δ σ = Some t' →
      ∃ u', partial_rename u Δ σ = Some u' ∧ RootEtaContract@{b e} t' u'.
Proof.
  destruct h as [Γ A U f | Γ A U p]; intros Δ σ t' h.
  - cbn [partial_rename] in h. rewrite partial_rename_weaken in h.
    destruct (partial_rename f Δ σ) as [f' |] eqn:k; cbn in h;
      try discriminate h.
    injection h as h. subst t'. exists f'. split.
    + reflexivity.
    + exact (root_eta_contract_function f').
  - cbn [partial_rename] in h.
    destruct (partial_rename p Δ σ) as [p' |] eqn:k; cbn in h;
      try discriminate h.
    injection h as h. subst t'. exists p'. split.
    + reflexivity.
    + exact (root_eta_contract_product p').
Defined.

(** ** Product Observations from Both Projections

    Fix arbitrary base labels. Equality of the two projections implies
    equality of the optional pair observations: beta at each projection
    reads one component. This does not claim injectivity of projections
    on arbitrary raw terms. The separate variable views recover position
    and marker information even when the pair observation is absent. *)

(** ** 从两个投影得到积观测

    固定任意基标签。两个投影分别相等，蕴含可选配对观测相等，因为每个投影
    处的 β 根各读取一个分量。这不声称投影对任意原始项联合单射。独立的变量
    视图在配对观测缺失时仍可恢复位置与标记信息。 *)

Section ProductObservations.
Context {B : Type}.

(** A left projection of an actual variable exposes its left view.
    Every other head returns [None], without comparing hidden types. *)

(** 实际变量的左投影暴露其左视图；其他头部返回 [None]，不比较隐藏类型。 *)

Definition projected_var_left {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : option (LeftProductVar Γ A)
  := match t in Tm Γ A return option (LeftProductVar Γ A) with
     | tm_fst p => option_map product_var_left (variable_position p)
     | _ => None
     end.

(** The right projection exposes the corresponding right view. *)

(** 右投影暴露对应的右视图。 *)

Definition projected_var_right {Γ : Ctx B} {U : Ty B} (t : Tm Γ U)
  : option (RightProductVar Γ U)
  := match t in Tm Γ U return option (RightProductVar Γ U) with
     | tm_snd p => option_map product_var_right (variable_position p)
     | _ => None
     end.

(** Projection equality preserves exactly the pair information needed
    to reconstruct an introduction. Other term shapes return [None]. *)

(** 投影相等保持重构引入形式所需的配对信息；其他项形状返回 [None]。 *)

Definition product_projection_parts {Γ : Ctx B} {A U : Ty B}
    (t v : Tm Γ (A × U)) (left : π₁ t = π₁ v) (right : π₂ t = π₂ v)
  : pair_parts t = pair_parts v.
Proof.
  pose proof (f_equal root_contractum left) as first.
  pose proof (f_equal root_contractum right) as second.
  change (option_map fst (pair_parts t) =
    option_map fst (pair_parts v)) in first.
  change (option_map snd (pair_parts t) =
    option_map snd (pair_parts v)) in second.
  destruct (pair_parts t) as [[a u] |];
    destruct (pair_parts v) as [[a' u'] |]; cbn in *;
    try discriminate first.
  - injection first as first. injection second as second.
    subst a' u'. reflexivity.
  - reflexivity.
Defined.

End ProductObservations.

(** A competing product root has the same two displayed projections.
    Fixed-type observers read each component of its source equation. *)

(** 竞争的积根具有相同的两个投影；固定类型的观测读取来源等式的各个分量。 *)

Definition root_eta_product_projections@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A U : Ty B} (t v : Tm Γ (A × U))
    (h : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v)
  : (π₁ t = π₁ v) ∧ (π₂ t = π₂ v).
Proof.
  pose proof (root_eta_source h) as parts.
  change (Some (π₁ t, π₂ t) = Some (π₁ v, π₂ v)) in parts.
  split.
  - exact (f_equal (λ z,
      match z with Some p => fst p | None => π₁ t end) parts).
  - exact (f_equal (λ z,
      match z with Some p => snd p | None => π₂ t end) parts).
Defined.

(** Competing product eta roots expose the same optional pair parts.
    Use fixed-type observers of the source pair, retaining independent
    syntax and root-evidence bounds. *)

(** 竞争的积 η 根暴露同一份可选配对分量。使用固定类型的源配对观测，保持
    语法界与根证据界独立。 *)

Definition root_eta_product_parts@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A U : Ty B} (t v : Tm Γ (A × U))
    (h : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v)
  : pair_parts t = pair_parts v.
Proof.
  pose proof (root_eta_source h) as parts.
  change (Some (π₁ t, π₂ t) = Some (π₁ v, π₂ v)) in parts.
  apply product_projection_parts.
  - exact (f_equal (λ z,
      match z with Some p => fst p | None => π₁ t end) parts).
  - exact (f_equal (λ z,
      match z with Some p => snd p | None => π₂ t end) parts).
Defined.

(** If one root target is a pair, the other target is that same pair by
    native syntax equality. No assertion about non-pair targets follows. *)

(** 若一个根目标为配对，另一个目标按语法原生相等就是该配对；此结论不处理
    非配对目标。 *)

Definition root_eta_product_pair_unique@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A U : Ty B} (a : Tm Γ A) (u : Tm Γ U)
    (v : Tm Γ (A × U))
    (h : RootEtaContract@{b e} (⟨π₁ (⟨a, u⟩), π₂ (⟨a, u⟩)⟩) v)
  : ⟨a, u⟩ = v.
Proof.
  pose proof (pair_parts_spec v) as spec.
  pose proof (root_eta_product_parts (⟨a, u⟩) v h) as parts.
  change (Some (a, u) = pair_parts v) in parts.
  rewrite <- parts in spec. cbn in spec. symmetry. exact spec.
Defined.

(** If one product root target is a variable, both projection views
    recover its position and marker in the other target. Thus the targets
    coincide natively, for arbitrary base labels and contexts. This does
    not yet identify targets headed by an elimination. *)

(** 若一个积根目标为变量，两个投影视图恢复另一目标中同一位置及标记。因此
    在任意基标签与上下文中，两目标原生相等。此结论尚不处理消去形式的目标。 *)

Definition root_eta_product_var_unique@{b e +} {B : Type@{b}}
    {Γ : Ctx B} {A U : Ty B} (x : Var Γ (A × U))
    (v : Tm Γ (A × U))
    (h : RootEtaContract@{b e} (⟨π₁ (# x), π₂ (# x)⟩) v)
  : # x = v.
Proof.
  destruct (root_eta_product_projections (# x) v h) as [first second].
  pose proof (f_equal projected_var_left first) as left.
  pose proof (f_equal projected_var_right second) as right.
  change (Some (product_var_left x) =
    option_map (@product_var_left B Γ A U) (variable_position v)) in left.
  change (Some (product_var_right x) =
    option_map (@product_var_right B Γ A U) (variable_position v)) in right.
  pose proof (variable_position_spec v) as spec.
  destruct (variable_position v) as [y |] eqn:position;
    cbn in left, right, spec; [| discriminate left].
  subst v. apply f_equal. apply (product_var_projections_injective x y).
  - exact (f_equal (λ z,
      match z with Some p => p | None => product_var_left x end) left).
  - exact (f_equal (λ z,
      match z with Some p => p | None => product_var_right x end) right).
Defined.
