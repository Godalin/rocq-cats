From Cats Require Import
  STLC.CategoricalGluing
  STLC.Set
  Cat.Core
  Cat.Natural
  Cat.Gluing.Core
  Cat.CCC
  Cat.Exponential.Core
  Cat.Product.Core
  Cat.Functor.FiniteProducts
  Instance.Set.Core
  Instance.Set.Lift
  Instance.Set.Product
  Instance.Set.PresheafExponential.

(** * Categorical Normalization Interfaces

    Check the new squares at two opposite orders of the original semantic
    and equation bounds. Separately instantiate the explicitly chosen CCC
    at its sufficient common value bound. Concrete reductions must retain
    the original normalizer and the unchanged syntax component. *)

(** * 范畴正规化接口

    在原语义与等式界的两个相反次序下检查新方形；另在充分的共同值界下实例化
    显式选定 CCC。具体约化必须保留原正规化器及不变的语法分量。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Larger Semantics and Smaller Ambient Equality

    Keep [b < r < e < s < p < u < l]. Observe both original projections
    from one evaluated categorical object; they cannot silently share a
    semantic/equation bound or a common ambient carrier/equality bound. *)

(** ** 较大语义与较小环境相等

    保持 [b < r < e < s < p < u < l]。从同一个求值后范畴对象观察原两个投影；
    它们不能暗中共用语义/等式界，或将环境载体/相等界合并。 *)

Section LargeSemantics.
Universes b r e s p u l.
Constraint b < r, r < e, e < s, s < p, p < u, u < l.
Context {B : Type@{b}}.

(** Both retained values come from the left component of one new square. *)

(** 两个保留值来自同一个新方形的左分量。 *)

Definition categorical_separated_values (A : Ty B) (Γ : Ctx B)
    (t : Tm Γ A)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{s s _ _ _ _ _}) Γ))%type
  := let x := comma_left (CategoricalEvaluationM A) Γ {|lower := t
                                                      |} in
      (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

(** The categorical comparison accepts the same ambient strict order. *)

(** 范畴比较接受同一个环境严格次序。 *)

Definition categorical_separated_comparison (A : Ty B)
  : @HomEq (Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}))) _ _
      (CategoricalQuoteM A ∘ CategoricalEvaluationM A)
      (CategoricalNormalizeM A)
  := categorical_evaluation_quote A.

(** Compare the complete respectful projections of the categorical
    object's domain, including the original equation and semantic
    relations. This catches wrappers that only preserve carrier values. *)

(** 比较范畴对象定义域上的完整保相等投影，包括原等式与语义关系；这能检测
    仅保留载体值的包装。 *)

Definition categorical_separated_projection_arrows (A : Ty B) (Γ : Ctx B)
  : let R : Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _} :=
        comma_left_ob (NormalizationRelationOb A) in
    ((R Γ →r LiftS@{b e u p} (TmS@{b e} Γ A)) *
     (R Γ →r LiftS@{s s u p} ((SemF A : Fct
       ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ)))%type
  := (GluingSyntaxN A Γ, GluingValuesN A Γ).

End LargeSemantics.

(** ** Larger Equations and Larger Ambient Equality

    Reverse to [b < r < l < s < e < u < p]. World laws are now below
    semantics, and ambient equality is above the carrier. *)

(** ** 较大等式与较大环境相等

    反转为 [b < r < l < s < e < u < p]；世界定律现在低于语义，而环境相等
    高于载体。 *)

Section LargeEquations.
Universes b r l s e u p.
Constraint b < r, r < l, l < s, s < e, e < u, u < p.
Context {B : Type@{b}}.

(** The same paired observation retains the opposite native bounds. *)

(** 同样的配对观察保留相反的原生界限。 *)

Definition categorical_reversed_values (A : Ty B) (Γ : Ctx B)
    (t : Tm Γ A)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{s s _ _ _ _ _}) Γ))%type
  := let x := comma_left (CategoricalEvaluationM A) Γ {|lower := t
                                                      |} in
      (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

(** The inverse also exists at this larger equality bound. *)

(** 在这个较大相等界下，逆仍存在。 *)

Definition categorical_reversed_inverse (A : Ty B)
  : @is_iso (Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}))) _ _ (CategoricalNormalizeM A)
  := categorical_normalization_iso A.

(** Compare the complete respectful projections of the categorical
    object's domain, including the original equation and semantic
    relations. This catches wrappers that only preserve carrier values. *)

(** 比较范畴对象定义域上的完整保相等投影，包括原等式与语义关系；这能检测
    仅保留载体值的包装。 *)

Definition categorical_reversed_projection_arrows (A : Ty B) (Γ : Ctx B)
  : let R : Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _} :=
        comma_left_ob (NormalizationRelationOb A) in
    ((R Γ →r LiftS@{b e u p} (TmS@{b e} Γ A)) *
     (R Γ →r LiftS@{s s u p} ((SemF A : Fct
       ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ)))%type
  := (GluingSyntaxN A Γ, GluingValuesN A Γ).

End LargeEquations.

(** ** Chosen Structures with Larger World Laws

    Only the CCC wrapper uses a common value/equality bound. Its world
    laws may still exceed that bound: [b < r < u < l]. *)

(** ** 世界定律较大时的选定结构

    只有 CCC 包装使用共同值/相等界；世界定律仍可超过该界：[b < r < u < l]。 *)

Section LargeWorldLaws.
Universes b r u l.
Constraint b < r, r < u, u < l.
Context (B : Type@{b}).

(** Instantiate the full arrow-category CCC at the native world levels. *)

(** 在原生世界层级实例化完整箭头范畴 CCC。 *)

Definition categorical_large_law_ccc
  : CCC (Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u u _ _ _ _ _})))
  := RenamingGluing_CCC B.

(** Application compares with the selected evaluation at these bounds. *)

(** 在这些界限下，应用与选定求值相比较。 *)

Definition categorical_large_law_application (A U : Ty B)
  : SemanticApplyN A U ≈N
      (@Cats.Cat.Exponential.Core.eval (FctCat
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{u u _ _ _ _ _})
        (@FctCat_HasProduct _ _ SetCat_HasProduct)
        (Psh_HasExponential (RenamingCat B)) (SemF A) (SemF U))
  := semantic_application_eval A U.

End LargeWorldLaws.

(** ** Chosen Structures with Smaller World Laws

    Reverse the world Hom/equality and law/value orders to [r < b < l < u].
    The semantic operation comparisons must use the same world and value
    bounds as that CCC. *)

(** ** 世界定律较小时的选定结构

    将世界 Hom/相等及定律/值次序反转为 [r < b < l < u]；语义操作比较必须
    使用与此 CCC 相同的世界和值界限。 *)

Section SmallWorldLaws.
Universes b r l u.
Constraint r < b, b < l, l < u.
Context (B : Type@{b}).

(** The reverse strict order also instantiates the complete structure. *)

(** 相反的严格次序也可实例化完整结构。 *)

Definition categorical_small_law_ccc
  : CCC (Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u u _ _ _ _ _})))
  := RenamingGluing_CCC B.

(** The natural isomorphism uses the same selected exponential object. *)

(** 自然同构使用同一个选定指数对象。 *)

Definition categorical_small_law_arrow (A U : Ty B)
  : SemF (A ⇒ U) ≅N
      (@exp (FctCat ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{u u _ _ _ _ _})
        (@FctCat_HasProduct _ _ SetCat_HasProduct)
        (Psh_HasExponential (RenamingCat B)) (SemF U) (SemF A))
  := SemanticArrowIsoN A U.

(** Transposition comparison accepts an arbitrary body natural map. *)

(** 转置比较接受任意函数体自然映射。 *)

Definition categorical_small_law_curry (A U : Ty B)
    (H : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u u _ _ _ _ _})
    (α : PointwiseProductF H (SemF A) ⇒ SemF U)
  : SemanticCurryN A U H α ≈N
      (@Cats.Cat.Exponential.Core.curry (FctCat
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{u u _ _ _ _ _})
        (@FctCat_HasProduct _ _ SetCat_HasProduct)
        (Psh_HasExponential (RenamingCat B)) (SemF A) (SemF U) H α)
  := semantic_abstraction_curry A U H α.

(** The normalization isomorphism inhabits this same explicitly selected
    CCC; no separate choice or reconstructed category is needed. *)

(** 正规化同构属于这个同一个显式选定 CCC，无需另一选择或重建范畴。 *)

Definition categorical_selected_normalization_iso (A : Ty B)
  : @is_iso (categorical_small_law_ccc : Cat) _ _
      (CategoricalNormalizeM A)
  := categorical_normalization_iso A.

End SmallWorldLaws.

(** ** Original Computation under the Squares

    A base-labelled identity abstraction tests the function case, without
    deciding labels. Both squares and their composite keep the original
    executable NbE and identity syntax maps. *)

(** ** 方形之下的原计算

    带基标签的恒等抽象检查函数情形，无须判定标签。两个方形及其复合保持原有
    可执行 NbE 与恒等语法映射。 *)

Section Computations.
Context {B : Type} (a : B).

(** A closed identity at an arbitrary base label. *)

(** 任意基标签处的闭恒等项。 *)

Definition categorical_identity_term
  : Tm (ctx_empty : Ctx B) (ty_base a ⇒ ty_base a)
  := tm_lam (tm_var var_zero).

(** The normalizing square computes the old long normal form natively. *)

(** 正规化方形原生计算出原长正规形。 *)

Example categorical_normalize_computes
  : lower (comma_left (CategoricalNormalizeM _) ctx_empty
      {|lower := categorical_identity_term
      |}) = nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Defined.

(** Factoring through the realized pair computes exactly the same tree. *)

(** 通过已实现配对分解，计算得到完全相同的树。 *)

Example categorical_evaluation_quote_computes
  : lower (comma_left (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
      ctx_empty {|lower := categorical_identity_term
                |}) = nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Defined.

(** The composite's base component retains the actual input term. *)

(** 复合的基分量保留实际输入项。 *)

Example categorical_base_computes
  : lower (comma_right (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
      ctx_empty {|lower := categorical_identity_term
                |}) = categorical_identity_term.
Proof. reflexivity. Defined.

(** The chosen inverse is the original normal-form embedding. *)

(** 选定逆就是原正规形嵌入。 *)

Example categorical_inverse_computes
  : lower (comma_left (categorical_normalization_iso
      (ty_base a ⇒ ty_base a)).1 ctx_empty
      {|lower := nf_lam (nf_base (ne_var var_zero))
      |}) = categorical_identity_term.
Proof. reflexivity. Defined.

(** A beta redex with a free input tests open evaluation. *)

(** 含自由输入的 β 红项检查开放求值。 *)

Definition categorical_open_redex
  : Tm ((ctx_empty : Ctx B) ▻ ty_base a) (ty_base a)
  := tm_app (tm_lam (tm_var var_zero)) (tm_var var_zero).

(** Quotation of the lifted realized value removes this redex natively. *)

(** 提升后的已实现值经引用，原生消去此红项。 *)

Example categorical_open_beta_computes
  : lower (comma_left (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
      _ {|lower := categorical_open_redex
         |}) = nf_base (ne_var var_zero).
Proof. reflexivity. Defined.

(** Restrict the output along a genuine weakening; the variable moves to
    the older position, so this is not an identity-world computation. *)

(** 沿真正的弱化限制输出；变量移到较旧位置，因此这不是恒等世界计算。 *)

Example categorical_weakening_computes
  : lower (fmap (comma_left_ob (NormalizationNormalOb (ty_base a)))
      (@ren_weaken B (ctx_empty ▻ ty_base a) (ty_base a))
      (comma_left (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
        _ {|lower := categorical_open_redex
           |})) = nf_base (ne_var (var_succ var_zero)).
Proof. reflexivity. Defined.

End Computations.
