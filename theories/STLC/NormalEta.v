From Cats Require Export
  STLC.Normal
  STLC.Equivalence.

(** * Type-Directed Eta Expansion of Neutral Terms

    A blocked neutral term already has no beta redex, but at a composite
    type it is not eta long. Expansion inspects its type: unit forgets the
    blocked term, products expose both projections, and functions introduce
    a fresh variable and apply the weakened neutral head to its expansion.
    Recursion follows the finite type, including both arrow components.

    This operation only accepts neutral terms. It is the syntactic prototype
    of reflection followed by reification, not an evaluator of arbitrary
    terms, and proves no strong normalization result about reduction paths.
    It imports no small-step reduction module. Its correctness uses the
    existing unit, product and function eta equations. *)

(** * 中性项的类型导向 η 展开

    被阻塞的中性项已不含 β 可归约式，但在复合类型处尚非 η 长。展开检查其
    类型：单位类型忘却被阻塞项，积类型暴露两个投影，函数类型引入新变量，
    并将弱化后的中性头应用于该变量的展开。递归沿有限类型进行，包括箭头的
    两个分量。

    此操作只接受中性项，是反射后再实化的语法原型，并非任意项的求值器，
    也不证明归约路径的强归一化。它不导入小步归约模块；正确性使用既有的
    单位、积与函数 η 方程。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** Expand a neutral term into a long normal form by structural recursion
    on its type. In the arrow case even the new argument is eta expanded;
    passing a bare variable would fail at a non-base domain. *)

(** 沿类型结构递归，将中性项展开为长正规形。箭头情形连新实参也作 η 展开；
    若定义域不是基类型，直接传入裸变量就不能满足长正规形要求。 *)

Fixpoint eta_expand_ne {B : Type} {Γ : Ctx B} {A : Ty B}
    (n : Ne Γ A) {struct A}
  : Nf Γ A
  := match A as U return Ne Γ U → Nf Γ U with
  | ty_base _ => λ n, nf_base n
  | ty_unit => λ _, nf_unit
  | ty_prod A U => λ n,
      nf_pair (eta_expand_ne (ne_fst n)) (eta_expand_ne (ne_snd n))
  | ty_arr A U => λ n,
      nf_lam (eta_expand_ne
        (ne_app (n⟨wkRen⟩ne) (eta_expand_ne (ne_var var_zero))))
  end n.

(** Expansion is beta/eta equal to its input after embedding. The syntax
    universe and the derivation universe remain independent, with the
    existing bound required by [TmEq]. The transparent witness first exposes
    eta structure, then expands its components by congruence. *)

(** 嵌入后的展开与输入 βη 相等。语法宇宙与推导宇宙保持独立，只满足 [TmEq]
    所需的既有界限。透明见证先暴露 η 结构，再通过同余展开其分量。 *)

Fixpoint eta_expand_ne_sound@{b e +} {B : Type@{b}} (A : Ty B)
    {Γ : Ctx B} (n : Ne Γ A)
  : TmEq@{b e _} (embed_ne n) (embed_nf (eta_expand_ne n)).
Proof.
  destruct A; cbn.
  - apply tm_eq_refl.
  - apply tm_eq_unit_η.
  - eapply tm_eq_trans.
    + apply tm_eq_sym. apply tm_eq_product_η.
    + apply tm_eq_pair.
      * exact (@eta_expand_ne_sound B A1 Γ (ne_fst n)).
      * exact (@eta_expand_ne_sound B A2 Γ (ne_snd n)).
  - eapply tm_eq_trans.
    + apply tm_eq_sym. apply tm_eq_function_η.
    + apply tm_eq_lam.
      refine (tm_eq_trans
        (u := embed_ne (ne_app (n⟨wkRen⟩ne)
          (eta_expand_ne (ne_var var_zero)))) _ _).
      * cbn [embed_ne]. apply tm_eq_app.
        -- apply tm_eq_of_eq. symmetry. apply embed_rename_ne.
        -- exact (@eta_expand_ne_sound B A1 (Γ ▻ A1)
             (ne_var var_zero)).
      * exact (@eta_expand_ne_sound B A2 (Γ ▻ A1)
          (ne_app (n⟨wkRen⟩ne)
            (eta_expand_ne (ne_var var_zero)))).
Defined.

(** Expansion commutes with renaming as a strict equation of normal trees.
    The function case uses weakening/lifting coherence and expands the fresh
    variable at its entire domain type. No equality of assignments is used. *)

(** 展开与重命名按正规语法树的严格等式交换。函数情形使用弱化与提升的相容律，
    并在整个定义域类型处展开新变量，无须比较赋值函数本身。 *)

Lemma eta_expand_ne_rename {B : Type} (A : Ty B)
  : ∀ (Γ Δ : Ctx B) (n : Ne Γ A) (ρ : Ren Δ Γ),
      eta_expand_ne (n⟨ρ⟩ne) = (eta_expand_ne n)⟨ρ⟩nf.
Proof.
  induction A; intros Γ Δ n ρ; cbn; try reflexivity.
  - f_equal.
    + exact (IHA1 Γ Δ (ne_fst n) ρ).
    + exact (IHA2 Γ Δ (ne_snd n) ρ).
  - f_equal. rewrite <- IHA2. cbn.
    rewrite rename_ne_weaken. rewrite <- IHA1. reflexivity.
Defined.
