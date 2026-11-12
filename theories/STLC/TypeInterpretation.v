From Cats Require Export
  STLC.Interpretation
  STLC.TypeCategory.
From Cats Require Import
  Cat.Induced

  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Exponential.Core
  Cat.CCC
  Cat.Functor.Closed.

(** * Interpreting the Type Presentation *)

(** * 类型呈现的解释 *)

(** ** Removing an irrelevant terminal factor

    Recursive context interpretation sends a singleton context to a product
    of the terminal object with its variable type. For the type presentation
    we instead evaluate its single-variable component using [single_env],
    whose variable assignment is the identity on [TyI I A]. The arrow map
    [type_interp] therefore has source [TyI I A] directly.

    Substitution compatibility proves the functor laws, and equational
    soundness proves respectfulness. The chosen literal unit, product and
    function objects interpret as the corresponding target constructions.
    Preservation is nevertheless stated through the standard canonical
    comparisons of [IsCCCF]. This supplies the common interface used for
    arbitrary structure-preserving functors, without identifying records
    or all their chosen objects by native equality. *)

(** ** 消除无关的终对象因子

    递归上下文解释把单变量上下文送到终对象与变量类型的积。类型呈现则使用
    [single_env] 求值其单变量分量，变量赋值为 [TyI I A] 上的恒等箭头。
    因此，箭头映射 [type_interp] 直接以 [TyI I A] 为源。

    替换相容性证明函子律，等式可靠性证明保相等性。所选的字面单位、积和函数
    对象解释为目标的相应构造；保持性仍通过 [IsCCCF] 的标准规范比较陈述。
    这给任意保持结构函子提供统一接口，无须把记录或其全部选定对象判为原生
    相等。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

(** ** Interpreting the Type Category

    Fix a CCC [C] and base-type assignment [I]. Interpret arrows between types
    using singleton environments and assemble the functor together with
    terminal and product preservation. *)

(** ** 解释类型范畴

    固定 CCC [C] 及基类型赋值 [I]，用单变量环境解释类型间箭头，组装解释函子，并给出终对象及积的保持性。 *)

Section TypeInterpretation.
Universes b e l.
Context {B : Type@{b}} {C : Cat} `{HC : !CCC C} (I : B → @Ob C).

(** The single input variable denotes the identity, without a terminal factor. *)

(** 单个输入变量表示恒等态射，不带额外终对象因子。 *)

Definition single_env (A : Ty B)
  : Env I (TyI I A) (ctx_snoc ctx_empty A)
  := λ U x, match x with
  | inl x => match x with end
  | inr x => match x in NewVar _ V return Hom (TyI I A) (TyI I V) with
    | new_var => id
    end
  end.

(** Evaluate a singleton substitution directly on its input object. *)

(** 在输入对象上直接求值单变量替换。 *)

Definition type_interp {A U}
    (h : (@Hom (TyCat@{b e l} B)) A U)
  : Hom (TyI I A) (TyI I U)
  := tm_eval I (h U var_zero) (single_env A).

(** Singleton composition is semantic precomposition. *)

(** 单变量复合解释为语义预合成。 *)

Lemma type_interp_comp {A U V}
    (g : (@Hom (TyCat@{b e l} B)) U V)
    (f : (@Hom (TyCat@{b e l} B)) A U)
  : type_interp (g ∘ f) ≈ type_interp g ∘ type_interp f.
Proof.
  change (tm_eval I ((g V var_zero)[f]) (single_env A) ≈
    tm_eval I (g V var_zero) (single_env U) ∘
      tm_eval I (f U var_zero) (single_env A)).
  rewrite tm_eval_subst.
  transitivity (tm_eval I (g V var_zero)
    (env_comp I (single_env U)
      (tm_eval I (f U var_zero) (single_env A)))).
  - apply tm_eval_ext. intros W [x | x]; [destruct x | destruct x].
    cbn [single_env env_comp]. symmetry. apply comp_id_l.
  - apply tm_eval_comp.
Qed.

(** The semantic functor on literal type objects. *)

(** 字面类型对象上的语义函子。 *)

Program Definition TypeInterpretF
  : Functor (TyCat@{b e l} B) C
  :=
  {|F0 := TyI I
  ; F1 A U h := type_interp h
  |}.
Next Obligation.
  intros f g H. apply tm_eval_sound. exact (H _ var_zero).
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. exact (type_interp_comp f g). Qed.

(** Interpretation preserves the first literal projection. *)

(** 解释保持第一个字面投影。 *)

Lemma type_interp_π1 (X Y : Ty B)
  : fmap TypeInterpretF (@Cats.Cat.Product.Core.π1
      (TyCat@{b e l} B) (TyCat_HasProduct B) X Y) ≈
      π1 (C := C) (X := TyI I X) (Y := TyI I Y).
Proof. exact (@comp_id_r C _ _ (π1 (X := TyI I X) (Y := TyI I Y))). Qed.

(** Interpretation preserves the second literal projection. *)

(** 解释保持第二个字面投影。 *)

Lemma type_interp_π2 (X Y : Ty B)
  : fmap TypeInterpretF (@Cats.Cat.Product.Core.π2
      (TyCat@{b e l} B) (TyCat_HasProduct B) X Y) ≈
      π2 (C := C) (X := TyI I X) (Y := TyI I Y).
Proof. exact (@comp_id_r C _ _ (π2 (X := TyI I X) (Y := TyI I Y))). Qed.

(** Literal evaluation denotes the selected target evaluation. *)

(** 字面求值解释为目标选定求值。 *)

Lemma type_interp_eval (X Y : Ty B)
  : fmap TypeInterpretF (@Cats.Cat.Exponential.Core.eval
      (TyCat@{b e l} B) (TyCat_HasProduct B)
      (TyCat_HasExponential B) X Y) ≈
      @Cats.Cat.Exponential.Core.eval C (@hasProduct C HC)
        (@hasExponential C HC) (TyI I X) (TyI I Y).
Proof.
  change (app
    (π1 (C := C) (X := (TyI I Y ^ TyI I X)%ob) (Y := TyI I X) ∘ id)
    (π2 ∘ id) ≈ @Cats.Cat.Exponential.Core.eval C
      (@hasProduct C HC) (@hasExponential C HC) (TyI I X) (TyI I Y)).
  rewrite !(@comp_id_r C). unfold app.
  transitivity (@Cats.Cat.Exponential.Core.eval C
    (@hasProduct C HC) (@hasExponential C HC) (TyI I X) (TyI I Y) ∘ id).
  - apply comp_proper; [reflexivity |].
    symmetry. apply product_pair_unique. split; apply comp_id_r.
  - apply comp_id_r.
Qed.

(** This interpretation preserves the terminal and product universal properties. *)

(** 此解释保持终对象与积的泛性质。 *)

Program Definition TypeInterpretF_IsCartesianF
  : IsCartesianF TypeInterpretF (TyCat_HasTerminal B) (TyCat_HasProduct B)
  :=
  {|functor_terminal := @terminal_universal C (@hasTerminal C HC)
  |}.
Next Obligation.
  refine (product_cone_equiv _ _ (@product_universal C
    (@hasProduct C HC) (TyI I X) (TyI I Y))).
  - symmetry. apply comp_id_r.
  - symmetry. apply comp_id_r.
Defined.

End TypeInterpretation.

(** ** Preservation of Exponentials by Interpretation

    Keep [C] and [I] fixed and reuse the interpretation functor's cartesian
    structure. Compute the product inverse and exponential comparison to prove
    it is a CCC functor. *)

(** ** 解释对指数结构的保持

    保持 [C]、[I] 固定，复用解释函子的笛卡尔结构，计算积逆及指数比较，证明它是 CCC 函子。 *)

Section TypeStructurePreservation.
Universes b e l.
Context {B : Type@{b}} {C : Cat} `{HC : !CCC C} (I : B → @Ob C).
Let F
  : Functor (TyCat@{b e l} B) C
  := TypeInterpretF I.
Local Existing Instance TypeInterpretF_IsCartesianF.

(** The product comparison is the identity up to specified equality. *)

(** 积比较在指定相等下为恒等。 *)

Lemma type_interp_product_inv (X Y : Ty B)
  : functor_product_inv F
      (TC := TyCat_HasTerminal B) (PC := TyCat_HasProduct B)
      (PD := @hasProduct C HC) X Y ≈ id.
Proof.
  pose proof (functor_product_inv_β F
    (TC := TyCat_HasTerminal B) (PC := TyCat_HasProduct B)
    (PD := @hasProduct C HC)
    X Y) as [H1 H2].
  assert (P1 : fmap F (@Cats.Cat.Product.Core.π1
    (TyCat@{b e l} B) (TyCat_HasProduct B) X Y) ≈
      π1 (X := TyI I X) (Y := TyI I Y)).
  { exact (type_interp_π1 I X Y). }
  assert (P2 : fmap F (@Cats.Cat.Product.Core.π2
    (TyCat@{b e l} B) (TyCat_HasProduct B) X Y) ≈
      π2 (X := TyI I X) (Y := TyI I Y)).
  { exact (type_interp_π2 I X Y). }
  rewrite P1 in H1. rewrite P2 in H2.
  transitivity (⟨π1 (X := TyI I X) (Y := TyI I Y), π2⟩).
  - apply product_pair_unique. split; assumption.
  - symmetry. apply product_pair_unique. split; apply (@comp_id_r C).
Qed.

(** The exponential comparison is also the identity up to specified equality. *)

(** 指数比较也在指定相等下为恒等。 *)

Lemma type_interp_exponential_comparison (X Y : Ty B)
  : functor_exponential_comparison F
      (TC := TyCat_HasTerminal B) (PC := TyCat_HasProduct B)
      (EC := TyCat_HasExponential B)
      (PD := @hasProduct C HC) (ED := @hasExponential C HC) X Y ≈ id.
Proof.
  assert (Pev : fmap F (@Cats.Cat.Exponential.Core.eval
    (TyCat@{b e l} B) (TyCat_HasProduct B) (TyCat_HasExponential B) X Y) ≈
    @Cats.Cat.Exponential.Core.eval C (@hasProduct C HC)
      (@hasExponential C HC) (TyI I X) (TyI I Y)).
  { exact (type_interp_eval I X Y). }
  unfold functor_exponential_comparison.
  rewrite type_interp_product_inv, Pev.
  etransitivity.
  - apply (@exponential_curry_proper C (@hasProduct C HC)
      (@hasExponential C HC) (TyI I X) (TyI I Y)
      (TyI I Y ^ TyI I X)%ob).
    exact (@comp_id_r C _ _ (@Cats.Cat.Exponential.Core.eval C
      (@hasProduct C HC) (@hasExponential C HC) (TyI I X) (TyI I Y))).
  - apply exponential_curry_eval.
Qed.

(** The recursively constructed interpretation is a CCC functor. *)

(** 递归构造的解释是 CCC 函子。 *)

Program Definition TypeInterpretF_IsCCCF
  : IsCCCF F (TyCat_CCC B) HC
  :=
  {|isCartesianF := TypeInterpretF_IsCartesianF I
  |}.
Next Obligation.
  exists id. split; unfold is_linv_of, is_rinv_of;
    [rewrite (@comp_id_l C) | rewrite (@comp_id_r C)];
    apply type_interp_exponential_comparison.
Defined.

End TypeStructurePreservation.
