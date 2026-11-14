From Cats.STLC Require Import BetaEtaNormalization.

(** * Beta/Eta Normalization Regressions

    Check independent component and result trees, paths and edge sizes in
    the generic interaction theorem. Check the STLC result at separated
    and equal levels, and observe residual work in concrete overlap cases. *)

(** * βη 归一化回归

    检查一般相互作用定理中的分量树、结果树、路径及边大小独立。检验 STLC
    结果在层级分离与相等时的接口，并观察具体重叠情形的剩余工作。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Large Paths and Small Component Trees

    Fix [a < r < t < sr < st < s < p < k]. The two edge types, component
    trees, output tree, path and law bounds are all strictly separated. *)

(** ** 大路径与小分量树

    固定 [a < r < t < sr < st < s < p < k]。两个边类型、分量树、输出树、
    路径及定律界全部严格分离。 *)

Section LargePaths.
Universes a r t sr st s p k.
Constraint a < r, r < t, t < sr, sr < st, st < s, s < p, p < k.
Context {X : Type@{a}} (R : X → X → Type@{r}) (S : X → X → Type@{t}).
Context (commute : is_quasi_commuting@{a r t p k t} R S).
Context (normalS : ∀ x, SN@{a t st} S x).

(** Large paths do not force larger output trees. *)

(** 大路径不迫使输出树增大。 *)

Definition large_path_sum_sn {x : X} (h : SN@{a r sr} R x)
  : SN@{a t s} (R ⊕R S) x
  := sn_sum_quasi_commuting commute normalS h.

End LargePaths.

(** ** Large Inputs and Small Result Trees

    Fix [t < r < a < p < s < sr < st < k]. The edge order is reversed;
    paths and the result tree are smaller than either input tree. *)

(** ** 大输入与小结果树

    固定 [t < r < a < p < s < sr < st < k]。边的次序反转，路径及结果树
    小于任一输入树。 *)

Section LargeInputTrees.
Universes t r a p s sr st k.
Constraint t < r, r < a, a < p, p < s, s < sr, sr < st, st < k.
Context {X : Type@{a}} (R : X → X → Type@{r}) (S : X → X → Type@{t}).
Context (commute : is_quasi_commuting@{a r t p k r} R S).
Context (normalS : ∀ x, SN@{a t st} S x).

(** Recursion constructs the mixed tree without storing large input
    trees or path witnesses in the result. *)

(** 递归构造混合树，不在结果中存储大的输入树或路径见证。 *)

Definition large_input_sum_sn {x : X} (h : SN@{a r sr} R x)
  : SN@{a r s} (R ⊕R S) x
  := sn_sum_quasi_commuting commute normalS h.

End LargeInputTrees.

(** ** Separate STLC Levels

    Fix [b < e < p < s < l]. The interaction produces paths at [p],
    whereas the final theorem returns trees at the independent [s]. *)

(** ** 分离的 STLC 层级

    固定 [b < e < p < s < l]。相互作用产生 [p] 处的路径，最终定理返回独立
    [s] 处的树。 *)

Section SeparatedLevels.
Universes b e p s l.
Constraint b < e, e < p, p < s, s < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The mixed theorem retains genuinely different syntax and edge sizes. *)

(** 混合定理保留真正不同的语法与边大小。 *)

Definition separated_beta_eta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaEtaContractStep@{b e l} B Γ A) t
  := beta_eta_strong_normalization t.

(** The diagram itself is available at the requested path bound. *)

(** 相互作用图本身适用于所要求的路径界。 *)

Definition separated_beta_eta_diagram {x y z : Tm Γ A}
    (h : EtaContractStep@{b e l} x y) (k : BetaStep@{b e l b} y z)
  : ∃ v, BetaStep@{b e l b} x v ∧
      ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} v z
  := beta_eta_quasi_commuting Γ A x y z h k.

End SeparatedLevels.

(** ** Trees above Classification

    Fix [b < e < l < s < p]. Step classification must not bound mixed
    trees or interaction paths. *)

(** ** 高于分类界的树

    固定 [b < e < l < s < p]。步骤分类不应限制混合树或相互作用路径。 *)

Section LargeTrees.
Universes b e l s p.
Constraint b < e, e < l, l < s, s < p.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The result is independent of the classification/tree ordering. *)

(** 结果不依赖分类界与树界的次序。 *)

Definition large_beta_eta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaEtaContractStep@{b e l} B Γ A) t
  := beta_eta_strong_normalization t.

(** Interaction paths may exceed both classification and tree bounds. *)

(** 相互作用路径可以同时超过分类界与树界。 *)

Definition large_beta_eta_diagram {x y z : Tm Γ A}
    (h : EtaContractStep@{b e l} x y) (k : BetaStep@{b e l b} y z)
  : ∃ v, BetaStep@{b e l b} x v ∧
      ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} v z
  := beta_eta_quasi_commuting Γ A x y z h k.

End LargeTrees.

(** ** Equal Computational Levels

    Syntax, edge and tree sizes may coincide, with only [b < l]. *)

(** ** 相等的计算层级

    语法、边及树的大小可以相同，只需 [b < l]。 *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** No strict computational separation is required by the theorem. *)

(** 定理不要求计算层级严格分离。 *)

Definition equal_beta_eta_sn (t : Tm Γ A)
  : SN@{b b b} (@BetaEtaContractStep@{b b l} B Γ A) t
  := beta_eta_strong_normalization t.

End EqualLevels.

(** ** Residual Work and Mixed Choices

    Fix an empty base signature. Product eta duplicates the beta source;
    root beta can in turn duplicate an eta-redex argument. Observe both
    phenomena without equating their derivation witnesses. *)

(** ** 剩余工作与混合选择

    固定空基签名。积 η 复制 β 来源；根 β 又可以复制带 η 可归约式的实参。
    观察两种现象，不比较其推导见证。 *)

Section Residuals.

(** Count edges, preserving the distinction from an empty path. *)

(** 计算边数，保留其与空路径的区别。 *)

Fixpoint path_length {X : Type} {R : X → X → Type}
    {x y : X} (h : (R^*) x y)
  : nat
  := match h with
  | rtc_refl _ => 0
  | rtc_cons _ tail => S (path_length tail)
  end.

(** A product beta redex with a free product argument. *)

(** 一个以自由积项为实参的积类型 β 可归约式。 *)

Definition product_redex
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤)) (⊤ × ⊤)
  := (ƛ (# var_zero)) · (# var_zero).

(** The diagram's first beta changes one copy; its tail contains the
    other copy's beta followed by eta contraction. *)

(** 图的首个 β 改变一个副本；其尾部包含另一副本的 β，再接 η 收缩。 *)

Example product_residual_length
  : path_length (snd (projT2
      (root_eta_beta_diagram (root_eta_product product_redex)
        (# var_zero) (context_step_root _
          (root_beta_function (# var_zero) (# var_zero)))))) = 2
  := eq_refl.

(** A closed identity used in the enclosing application overlap. *)

(** 一个闭恒等函数，用于外层应用重叠。 *)

Definition unit_identity
  : Tm (@ctx_empty Empty_set) (⊤ ⇒ ⊤)
  := ƛ (# var_zero).

(** Contracting the expanded lambda at the enclosing beta leaves one
    beta step, computed through the typed introduction observer. *)

(** 在外层 β 处收缩展开的 λ 后留下一个 β 步骤，经带类型引入观测计算得到。 *)

Example enclosing_function_residual_length
  : path_length (snd (projT2
      (eta_expansion_root_context (op_app_l ⋆)
        (context_step_root _ (root_eta_function unit_identity))
        (root_beta_function (# var_zero) ⋆)))) = 1
  := eq_refl.

(** A free product fixes the signature and context of the argument case. *)

(** 一个自由积项，固定实参情形的签名与上下文。 *)

Definition product_variable
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤)) (⊤ × ⊤)
  := # var_zero.

(** Moving beta first duplicates the eta edge into two residual steps. *)

(** 将 β 移到前面，会把 η 边复制为两个剩余步骤。 *)

Example duplicated_argument_residual_length
  : path_length (snd (projT2
      (eta_expansion_root_context
        (op_app_r (ƛ (⟨# var_zero, # var_zero⟩)))
        (context_step_root _ (root_eta_product product_variable))
        (root_beta_function (⟨# var_zero, # var_zero⟩) product_variable)))) = 2
  := eq_refl.

(** A duplicator applied to an eta-expanded free product. *)

(** 一个作用于 η 展开后的自由积项的复制函数。 *)

Definition duplicating_eta_argument
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤))
      ((⊤ × ⊤) × (⊤ × ⊤))
  := (ƛ (⟨# var_zero, # var_zero⟩)) ·
      (⟨π₁ (# var_zero), π₂ (# var_zero)⟩).

(** The all-term tree includes eta in the argument followed by root beta. *)

(** 所有项的树包含实参中的 η，随后是根 β。 *)

Example eta_then_duplicating_beta_sn
  : SN BetaEtaContractStep
      (⟨# var_zero, # var_zero⟩ :
        Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤))
          ((⊤ × ⊤) × (⊤ × ⊤)))
  := sn_step
      (sn_step (beta_eta_strong_normalization duplicating_eta_argument)
        (inr (eta_contract_lift (op_app_r (ƛ (⟨# var_zero, # var_zero⟩)))
          (eta_contract_root (root_eta_contract_product (# var_zero))))))
      (inl (context_step_root _
        (root_beta_function (⟨# var_zero, # var_zero⟩) (# var_zero)))).

(** Beta may instead duplicate the expanded argument first. The mixed
    tree covers eta contraction independently in both resulting copies. *)

(** β 也可先复制展开后的实参；混合树覆盖随后在两个副本中独立进行的 η 收缩。 *)

Example duplicated_eta_redexes_sn
  : SN BetaEtaContractStep
      (⟨⟨π₁ (# var_zero), π₂ (# var_zero)⟩,
        ⟨π₁ (# var_zero), π₂ (# var_zero)⟩⟩ :
        Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤))
          ((⊤ × ⊤) × (⊤ × ⊤)))
  := sn_step (beta_eta_strong_normalization duplicating_eta_argument)
      (inl (context_step_root _ (root_beta_function
        (⟨# var_zero, # var_zero⟩)
        (⟨π₁ (# var_zero), π₂ (# var_zero)⟩)))).

End Residuals.
