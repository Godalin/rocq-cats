From Cats Require Export
  Cat.Computational.Arrow.StaticEvaluation
  Instance.Set.Arrow.
From Cats Require Import
  Cat.Computational.Arrow.Static
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Exponential.
Import Cats.Cat.Exponential.Core.
Local Open Scope computation_scope.

(** * Static Computations Interpreted in the Original Arrow

    Work in the existing closed setoid model at a common carrier/equality
    level. Fix any cartesian Arrow with a computation category of independent
    object size. Extract its Applicative, form the static computation category,
    and interpret it back through the generic evaluation construction.
    Pure arrows, sequencing and ordinary context are preserved. No inverse,
    faithfulness or reconstruction claim is made. *)

(** * 在原 Arrow 中解释静态计算

    使用载体／相等共用层级的已有闭广集模型，固定计算范畴对象大小独立的任意
    笛卡尔 Arrow。抽取其 Applicative，组成静态计算范畴，再经一般求值构造
    解释回原 Arrow。保持纯箭头、顺序及通常上下文；此处不给出逆、忠实性或
    重建结论。 *)

Section StaticInterpretation.
Universe u.
Let C
  : Cat
  := SetCat@{u u _ _ _ _ _}.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasExponential.
Context (K : Cat)
    (A : Arrow C K
      (@CartesianMonoidal C SetCat_HasTerminal SetCat_HasProduct)).

(** Evaluate the outer singleton argument, then reuse generic global-
    function interpretation. *)

(** 求值外层单元素参数，再复用一般全局函数解释。 *)

Definition static_interpret {X Y : @Ob C}
    (f : (@Hom (StaticCat (ArrowA K A))) X Y)
  : Hom (A X) (A Y)
  := arrow_static_eval A (f tt).

(** Interpretation respects the original static hom-setoid equality. *)

(** 解释保持原静态 Hom 广集相等。 *)

Global Instance static_interpret_proper {X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@static_interpret X Y).
Proof.
  intros f g H. apply arrow_static_eval_proper. exact (H tt).
Qed.

(** Interpreting a static pure arrow gives the original pure inclusion. *)

(** 解释静态纯箭头，得到原有纯嵌入。 *)

Lemma static_interpret_arr {X Y : @Ob C} (f : Hom X Y)
  : static_interpret (static_arr (ArrowA K A) f) ≈ arr[A; f].
Proof.
  unfold static_interpret. etransitivity; [| exact (arrow_static_eval_pure A f)].
  unfold arrow_static_eval, arrow_global_context.
  apply comp_proper; [reflexivity |]. apply comp_proper; [| reflexivity].
  apply arrow_second_proper.
  apply (@functor_fmap_proper C K A UnitS (Y ^ X)%ob). intros [].
  intros x. reflexivity.
Qed.

(** Interpretation preserves execution-order composition in designated Hom
    equality. *)

(** 解释在指定 Hom 相等下保持按执行次序的复合。 *)

Lemma static_interpret_comp {X Y Z : @Ob C}
    (g : (@Hom (StaticCat (ArrowA K A))) Y Z)
    (f : (@Hom (StaticCat (ArrowA K A))) X Y)
  : static_interpret (g ∘ˢ[ArrowA K A] f) ≈
      static_interpret g ∘ static_interpret f.
Proof.
  change (arrow_static_eval A
    (arr[A; internal_then X Y Z] ∘ (f tt &&&[A] g tt)) ≈
      arrow_static_eval A (g tt) ∘ arrow_static_eval A (f tt)).
  apply arrow_static_eval_comp.
Qed.

(** Interpretation preserves the same selected left-context action. *)

(** 解释保持同一组选定左上下文作用。 *)

Lemma static_interpret_context {X Y : @Ob C} (W : @Ob C)
    (f : (@Hom (StaticCat (ArrowA K A))) X Y)
  : static_interpret (static_context (ArrowA K A) W f) ≈
      context[A; W; static_interpret f].
Proof.
  change (arrow_static_eval A
    (arr[A; internal_context W X Y] ∘ f tt) ≈
      context[A; W; arrow_static_eval A (f tt)]).
  apply arrow_static_eval_context.
Qed.

(** The comparison functor uses the original pure object map. Its laws come
    from the preceding generic preservation results. *)

(** 比较函子使用原纯对象映射，定律来自前述一般保持性结果。 *)

Program Definition StaticInterpretF
  : Functor (StaticCat (ArrowA K A)) K
  :=
  {|F0 := A
  ; F1 X Y f := static_interpret f
  ; functor_fmap_proper X Y := static_interpret_proper
  |}.
Next Obligation.
  change (static_interpret
    (static_arr (ArrowA K A) (id_resp (X := X))) ≈ @id (A X)).
  rewrite static_interpret_arr. exact (@functor_id C K A X).
Defined.
Next Obligation. exact (static_interpret_comp f g). Defined.

(** Interpreting the static pure inclusion compares naturally with the
    original pure functor, using identity components. *)

(** 解释静态纯嵌入，以恒等分量自然比较原来的纯函子。 *)

Program Definition StaticInterpretPureN
  : (StaticInterpretF ∘F StaticPureF (ArrowA K A)) ⇒ A
  :=
  {|nt X := id
  |}.
Next Obligation.
  change (id ∘ static_interpret (static_arr (ArrowA K A) f) ≈
    arr[A; f] ∘ id).
  rewrite comp_id_l, comp_id_r. apply static_interpret_arr.
Defined.

(** Identity inverse components give the pure-inclusion natural isomorphism. *)

(** 恒等逆分量给出纯嵌入的自然同构。 *)

Definition StaticInterpretPureIso
  : (StaticInterpretF ∘F StaticPureF (ArrowA K A)) ≅N A.
Proof.
  exists StaticInterpretPureN. intro X. exists id. split; apply comp_id_l.
Defined.

End StaticInterpretation.
