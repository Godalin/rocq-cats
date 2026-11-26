From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Functor.FiniteProducts
  Cat.Natural
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC.Core
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Terminal
  Instance.Set.Lift
  Instance.Set.Kripke.

(** * Presheaf Exponentials from Existing Kripke Functions

    At a world [X], a coherent Kripke function accepts every future arrow
    [Y → X] and an argument at [Y]. These are the component data of a
    natural map from [Hom(-,X) × A] to [B], rather than an ordinary function
    [A X → B X]. Its equality observes applications, not law fields.

    Reuse the existing function presheaf, restriction, evaluation and the
    size-aware currying universal property. This module only packages them
    as exponential objects in one fixed presheaf category. A common value
    bound contains functions and their respectful/naturality witnesses.
    The world's object, arrow and equality bounds remain independent below
    it; the world-law bound is separate. No resizing is used. *)

(** * 由既有 Kripke 函数得到预层指数

    世界 [X] 处的相容 Kripke 函数接受任意未来箭头 [Y → X] 以及 [Y] 处的
    参数。这些是 [Hom(-,X) × A] 到 [B] 的自然映射的分量数据，而不是普通
    函数 [A X → B X]。其相等观察应用，不比较定律字段。

    复用已有函数预层、限制、求值及大小敏感的柯里化泛性质；本模块仅将它们
    打包为一个固定预层范畴中的指数。共同值界容纳函数及其保相等/自然性见证；
    世界的对象、箭头、相等界在此界下保持独立，世界定律界另设。不使用重缩宇宙。 *)

(** ** A Fixed Value Universe

    Fix a small world category and two presheaves in a common value universe.
    Enable the existing pointwise product choice locally. Evaluation and
    transposition keep exactly the old Kripke values and application maps. *)

(** ** 固定的值宇宙

    固定小世界范畴及共同值宇宙中的两个预层，局部启用已有逐点积选择。
    求值和转置保留原 Kripke 值与应用映射。 *)

Section PresheafExponential.
Universes o h e l u.
Constraint o <= u.
Constraint h <= u.
Constraint e <= u.
Context (C : Cat@{o h e l l}).
Context (A B : Fct (C^op) SetCat@{u u _ _ _ _ _}).

(** Package the existing respectful evaluation as a component arrow. *)

(** 将既有的保相等求值打包为分量箭头。 *)

Program Definition psh_eval_resp (X : @Ob C)
  : KripkeFunctionS A B X ×S A X →r B X
  :=
  {|func p := kripke_eval A B (fst p) (snd p)
  |}.
Next Obligation.
  intros [k a] [j b] [Hk Ha]. apply kripke_eval_proper; assumption.
Defined.

(** The previously proved evaluation/restriction law supplies naturality. *)

(** 已证明的求值/限制律给出自然性。 *)

Program Definition PshEvalN
  : PointwiseProductF (B ^K A) A ⇒ B
  :=
  {|nt X := psh_eval_resp X
  |}.
Next Obligation.
  intros [k a]. symmetry. apply kripke_eval_reindex.
Defined.

(** ** Unlifted Contexts at the Common Bound

    Existing Kripke currying explicitly raises its parameter presheaf. At
    the present sufficient size bounds, both that parameter and function
    values already fit the same category. Wrapping or unwrapping the
    parameter is transparent and does not resize it downward. *)

(** ** 共同界限下未提升的上下文

    既有 Kripke 柯里化显式提升参数预层。在当前充分大小界限下，参数与函数
    值已经容纳于同一范畴；参数的包装与拆包透明，不向下重缩宇宙。 *)

Section Transpose.
Context {Z : Fct (C^op) SetCat@{u u _ _ _ _ _}}.

(** Currying uses the original component function without wrapping values. *)

(** 柯里化使用原分量函数，不包装值。 *)

Program Definition psh_curry_resp (t : PointwiseProductF Z A ⇒ B)
    (X : @Ob C)
  : Z X →r KripkeFunctionS A B X
  :=
  {|func := kripke_curry_at A B Z t X
  |}.

(** Existing restriction compatibility assembles the native transpose. *)

(** 既有的限制相容性将原生转置组织起来。 *)

Program Definition PshCurryN (t : PointwiseProductF Z A ⇒ B)
  : Z ⇒ B ^K A
  :=
  {|nt X := psh_curry_resp t X
  |}.
Next Obligation.
  intros z. symmetry. apply kripke_curry_at_reindex.
Defined.

(** Reuse the old respectful transposition law at wrapped context elements. *)

(** 在包装的上下文元素处复用原转置保相等律。 *)

Global Instance psh_curry_proper
  : Proper (NatEq ==> NatEq) PshCurryN.
Proof.
  intros t s Ht X z.
  exact (KripkeCurryN_proper A B Z t s Ht X {|lower := z
                                          |}).
Defined.

(** Precompose any native function family with the transparent unwrapping
    of the context. This is the input expected by the old universal law. *)

(** 将任意原生函数族与上下文的透明拆包预合成，得到原泛性质所需的输入。 *)

Program Definition PshLiftedContextN (k : Z ⇒ B ^K A)
  : (LiftF ∘F Z) ⇒ B ^K A
  :=
  {|nt X :=
    {|func z := k X (lower z)
    |}
  |}.
Next Obligation.
  intros [z] [w] [Hzw]. exact (@func_proper _ _ (k X) z w Hzw).
Defined.
Next Obligation. intros [z]. exact (nat_naturality k f z). Defined.

(** The old beta law is definitionally the required native evaluation law. *)

(** 原 β 律按定义就是所需的原生求值律。 *)

Lemma psh_exp_β (t : PointwiseProductF Z A ⇒ B)
  : (PshEvalN ∘Nv PointwiseProductN (PshCurryN t) (IdN (F := A))) ≈N t.
Proof. exact (kripke_curry_β A B Z t). Qed.

(** The existing unique transpose applies to the lifted context; evaluation
    at a wrapped element gives uniqueness in the native context. *)

(** 既有转置唯一性应用于提升的上下文，在包装元素处求值就给出原生上下文中的
    唯一性。 *)

Lemma psh_exp_unique (t : PointwiseProductF Z A ⇒ B)
    (k : Z ⇒ B ^K A)
    (Hk : (PshEvalN ∘Nv PointwiseProductN k (IdN (F := A))) ≈N t)
  : k ≈N PshCurryN t.
Proof.
  pose proof (kripke_curry_unique A B Z t (PshLiftedContextN k) Hk)
    as Hu.
  intros X z Y f a. exact (Hu X {|lower := z
                               |} Y f a).
Qed.

End Transpose.

(** ** Candidate Exponential Property

    Use the original chosen pointwise products and the same Kripke function
    presheaf. Neither a terminal object nor a pullback is needed here. *)

(** ** 候选指数性质

    使用原先选定的逐点积及同一个 Kripke 函数预层；此处不需要终对象或拉回。 *)

Local Instance psh_products
  : HasProduct (FctCat (C^op) SetCat@{u u _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

(** The original transposition laws give the full exponential property. *)

(** 原转置定律给出完整的指数泛性质。 *)

Definition psh_exp_universal
  : @is_exp (FctCat (C^op) SetCat) psh_products
      A B (B ^K A) PshEvalN.
Proof.
  intros Z t. exists (PshCurryN t).
  refine {|this := _
         ; that := _
         |}.
  - exact (psh_exp_β t).
  - intros k Hk. apply psh_exp_unique. exact Hk.
Defined.

End PresheafExponential.

(** Select the old Kripke presheaf as the exponential, explicitly and
    relative to the original pointwise product choice. The common value
    bound is a sufficient condition, not an arbitrary resizing principle. *)

(** 显式选择原 Kripke 预层为指数，相对于原逐点积选择。共同值界是充分条件，
    不是任意重缩宇宙原理。 *)

Program Definition Psh_HasExponential@{o h e l u +}
    (C : Cat@{o h e l l})
  : @HasExponential (FctCat (C^op) SetCat@{u u _ _ _ _ _})
      (@FctCat_HasProduct _ _ SetCat_HasProduct)
  :=
  {|exp B A := B ^K A
  ; eval A B := PshEvalN C A B
  |}.
Next Obligation. apply psh_exp_universal. Defined.

(** Combine the already chosen pointwise terminal/products with the
    constructed exponentials. Importing this value enables no model choice. *)

(** 将已选定的逐点终对象/积与所构造的指数组合；导入该值不启用模型选择。 *)

Program Definition Psh_CCC@{o h e l u +} (C : Cat@{o h e l l})
  : CCC
  := MakeCCC (FctCat (C^op) SetCat@{u u _ _ _ _ _})
      (@FctCat_HasTerminal _ _ SetCat_HasTerminal)
      (@FctCat_HasProduct _ _ SetCat_HasProduct)
      (Psh_HasExponential C).
