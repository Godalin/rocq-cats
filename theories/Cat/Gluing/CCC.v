From Cats Require Export
  Cat.Gluing.Exponential
  Cat.CCC.Core.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Pullback.

(** * Explicit Cartesian Closed Structure on Gluing

    Only the comparison cospans need pullbacks. Their supplied Type-valued
    witnesses choose the exponential mediators; the base terminal then
    completes the CCC structure. Each vertex must already be an object
    of [D]; model-specific size bounds belong to the supplied witnesses.
    No resizing or global selection is introduced. *)

(** * 粘合上显式的笛卡尔闭结构

    只有比较余跨度需要拉回。指定的 Type 值见证选择指数中介；基终对象随后
    补全 CCC 结构。每个顶点须已是 [D] 的对象，模型特有的大小界由指定见证
    承担。本构造不作大小提升，也不引入全局选择。 *)

(** ** Choosing Only the Required Pullbacks

    Fix products, exponentials and preservation of the base product cones.
    Supply a pullback for each exponential comparison cospan, not for
    arbitrary arrows. No terminal or exponential preservation is assumed. *)

(** ** 只选择所需拉回

    固定积、指数及基积锥的保持性。为每个指数比较余跨度给出拉回，而非为
    任意箭头选择拉回。不假设终对象或指数保持性。 *)

Section ChosenGluingExps.
Context {C D : Cat} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ A B : @Ob C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (pullbacks : ∀ X Y : @Ob (Gluing F),
    ∃ E : @Ob D,
    ∃ p : Hom E (comma_left_ob Y ^ comma_left_ob X),
    ∃ q : Hom E (F ((comma_right_ob Y ^ comma_right_ob X)%ob)),
      is_pullback (gluing_exp_result F X Y)
        (gluing_exp_base F preserves X Y) E p q).

(** The candidate proof supplies the full selected exponential structure
    for exactly the previously constructed gluing products. *)

(** 候选证明给出完整选定指数结构，积恰为先前构造的粘合积。 *)

Program Definition Gluing_HasExponential
  : HasExponential (Gluing_HasProduct F preserves)
  :=
  {|exp Y X := GluingExp F X Y
      (pullbacks X Y).1 (pullbacks X Y).2.2.1
  ; eval X Y := gluing_eval F preserves X Y
      (pullbacks X Y).1 (pullbacks X Y).2.1
      (pullbacks X Y).2.2.1 (pullbacks X Y).2.2.2
  ; exp_universal X Y := gluing_exp_universal F preserves
      X Y (pullbacks X Y).1 (pullbacks X Y).2.1
      (pullbacks X Y).2.2.1 (pullbacks X Y).2.2.2
  |}.

(** Adding only a base terminal object completes the inherited cartesian
    structure. A target terminal object is still unnecessary. *)

(** 仅加入基终对象即可补全继承的笛卡尔结构，仍不需要目标终对象。 *)

Program Definition Gluing_CCC `{TC : !HasTerminal C}
  : CCC
  :=
  {|CCCToCartCat := Gluing_CartCat F preserves
  ; hasExponential := Gluing_HasExponential
  |}.

End ChosenGluingExps.

(** ** A Stronger Sufficient Hypothesis

    If all pullbacks in the target have already been chosen, reuse the
    relevant ones. This convenience wrapper changes none of the weaker
    candidate or chosen-family hypotheses above. *)

(** ** 一个更强的充分条件

    若目标的全部拉回已经选定，就复用其中相关的拉回。此便捷包装不改变上述
    较弱候选定理或选定族接口的假设。 *)

Section AllTargetPullbacks.
Context {C D : Cat} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}
    `{HPb : !HasPullback D}.
Context (preserves : ∀ A B : @Ob C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).

(** Extract just the pullback needed for one pair of glued objects. *)

(** 只提取一对粘合对象所需的拉回。 *)

Definition GluingExpPullback (X Y : @Ob (Gluing F))
  : ∃ E : @Ob D,
    ∃ p : Hom E (comma_left_ob Y ^ comma_left_ob X),
    ∃ q : Hom E (F ((comma_right_ob Y ^ comma_right_ob X)%ob)),
      is_pullback (gluing_exp_result F X Y)
        (gluing_exp_base F preserves X Y) E p q
  := (Pb (gluing_exp_result F X Y)
        (gluing_exp_base F preserves X Y);
      (pb1 _ _; (pb2 _ _; pullback_universal))).

(** Enable the resulting exponentials explicitly, using the same mediators. *)

(** 显式启用所得指数，使用相同中介。 *)

Definition GluingPullback_HasExponential
  : HasExponential (Gluing_HasProduct F preserves)
  := Gluing_HasExponential F preserves GluingExpPullback.

(** This is a sufficient CCC construction, not a claim about arbitrary
    pairs of CCCs: product preservation and target pullbacks are inputs. *)

(** 这是 CCC 的一个充分构造，并非任意两个 CCC 的断言：积保持性和目标拉回
    都是输入。 *)

Definition GluingPullback_CCC `{TC : !HasTerminal C}
  : CCC
  := Gluing_CCC F preserves GluingExpPullback.

End AllTargetPullbacks.
