From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.DoubleDual
  Cat.Exponential.Equalizing
  Cat.Equalizer
  Cat.Coequalizer
  Cat.Pullback
  Cat.Pushout
  Cat.Morphism
  Cat.Limit.Finite
  Cat.Colimit.Core
  Cat.Colimit.Finite
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder
  Topos.Image
  Topos.Initial
  Topos.Coproduct.

Import Cats.Cat.Exponential.Core.

(** * Coequalizers from Elementary Topos Choices

    Evaluate on the equalizing predicates of a parallel pair, then take
    the image. Monic double evaluation retains actual descent into every
    other coequalizing target; the image factor's epimorphic property
    proves uniqueness. No stability or quotient axiom is assumed. *)

(** * 从初等拓扑斯选择构造余等化子

    在平行箭头对的等化谓词上求值并取像。单态的双重求值保留进入任意其他
    余等化目标的实际下降映射；像分解的满性证明唯一性。不假设稳定性或商公理。 *)

Section ToposCoequalizers.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HX : !HasExponential HP}.
Let EQ
  : HasEqualizer C
  := @ProductPullbackEqualizer C HP PB.
Local Existing Instance EQ.

(** Take the image of evaluation restricted to the equalizing predicates. *)

(** 对限制到等化谓词的求值取像。 *)

Definition ToposCoequalizerSub {A B : C} (f g : Hom A B)
  : Sub (Ω ^ EqualizingTests Ω f g)
  := ToposImage (EqualizingEvaluation Ω f g).

(** The image's domain is the candidate coequalizer object. *)

(** 像的定义域是候选余等化子对象。 *)

Definition ToposCoequalizer {A B : C} (f g : Hom A B)
  : C
  := sub (ToposCoequalizerSub f g).

(** Retain the same image factor as the coequalizer projection. *)

(** 保留同一像分解因子作为余等化子投影。 *)

Definition topos_coeq {A B : C} (f g : Hom A B)
  : Hom B (ToposCoequalizer f g)
  := topos_image_factor (EqualizingEvaluation Ω f g).

(** Cancel the image inclusion to inherit the evaluation equation. *)

(** 消去像包含以继承求值方程。 *)

Theorem topos_coequalizer_comm {A B : C} (f g : Hom A B)
  : topos_coeq f g ∘ f ≈ topos_coeq f g ∘ g.
Proof.
  apply (@mor_mono C _ _ (sub_mono _ (ToposCoequalizerSub f g)) A
    (topos_coeq f g ∘ f) (topos_coeq f g ∘ g)).
  unfold topos_coeq, ToposCoequalizerSub.
  rewrite <- !comp_assoc, (topos_image_factor_comm (EqualizingEvaluation Ω f g)).
  apply equalizing_evaluation_comm.
Qed.

(** ** Descent and Universality

    An arrow identifying the parallel pair induces a lift to its target
    double power. Its truth test contains the original evaluation, hence
    also its least image. Classification retains the descent map. *)

(** ** 下降与泛性质

    识别平行箭头对的箭头诱导到目标双重幂对象的提升。其为真判据包含原求值，
    因而也包含该求值的最小像；分类保留下降映射。 *)

(** The lift restricted to the image factors through monic double evaluation. *)

(** 提升限制到像后经单态的双重求值分解。 *)

Definition topos_coequalize_factored {A B Z : C} {f g : Hom A B}
    (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : is_factored_through (ToposDoubleDualMono Z)
      (EqualizingLift Ω h Hh ∘ ToposCoequalizerSub f g).
Proof.
  pose (q := EqualizingEvaluation Ω f g).
  pose (m := ToposDoubleDualMono Z).
  pose (r := χ m ∘ EqualizingLift Ω h Hh).
  assert (H : r ∘ q ≈ truth ∘ !).
  { unfold r. rewrite comp_assoc.
    apply (snd (classifier_char_factor m (EqualizingLift Ω h Hh ∘ q))).
    exists h. apply equalizing_lift_comm. }
  pose (K := image_predicate_le q r H).
  pose (Hr := fst (predicate_le_truth (image_predicate q) r) K).
  apply (fst (classifier_char_factor m
    (EqualizingLift Ω h Hh ∘ ToposCoequalizerSub f g))).
  rewrite <- comp_assoc. exact Hr.
Defined.

(** Read the descent from the retained classifier factor. *)

(** 从保留的分类子因子读取下降映射。 *)

Definition topos_coequalize {A B Z : C} {f g : Hom A B}
    (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : Hom (ToposCoequalizer f g) Z
  := (topos_coequalize_factored h Hh).1.

(** The same factor equation compares descent with the test lift. *)

(** 同一分解方程将下降与测试提升比较。 *)

Theorem topos_coequalize_comm {A B Z : C} {f g : Hom A B}
    (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : ToposDoubleDualMono Z ∘ topos_coequalize h Hh
    ≈ EqualizingLift Ω h Hh ∘ ToposCoequalizerSub f g.
Proof. symmetry. exact (topos_coequalize_factored h Hh).2. Qed.

(** Monicity of double evaluation yields the descent beta law. *)

(** 双重求值的单态性给出下降 β 律。 *)

Theorem topos_coequalizer_β {A B Z : C} {f g : Hom A B}
    (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : topos_coequalize h Hh ∘ topos_coeq f g ≈ h.
Proof.
  apply (@mor_mono C _ _ (ToposDoubleDualMono Z) B
    (topos_coequalize h Hh ∘ topos_coeq f g) h).
  rewrite <- comp_assoc, (topos_coequalize_comm h Hh), comp_assoc.
  unfold topos_coeq, ToposCoequalizerSub.
  transitivity (EqualizingLift Ω h Hh ∘ EqualizingEvaluation Ω f g).
  - apply comp_proper; [reflexivity |].
    exact (@topos_image_factor_comm C HT HC PB HP HX B
      (Ω ^ EqualizingTests Ω f g) (EqualizingEvaluation Ω f g)).
  - exact (equalizing_lift_comm Ω h Hh).
Qed.

(** Uniqueness uses the general image factor's already proved epimorphic
    property, without choosing sections or assuming stable images. *)

(** 唯一性使用一般像分解已证明的满性，不选择截面或假设像稳定。 *)

Theorem topos_coequalizer_unique {A B Z : C} {f g : Hom A B}
    (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : is_unique (λ k, k ∘ topos_coeq f g ≈ h) (topos_coequalize h Hh).
Proof.
  split; [exact (topos_coequalizer_β h Hh) |].
  intros k Hk.
  apply (@topos_image_factor_epi C HT HC PB HP HX _ _
    (EqualizingEvaluation Ω f g) Z k (topos_coequalize h Hh)).
  rewrite (topos_coequalizer_β h Hh). exact Hk.
Qed.

(** The projection satisfies the existing opposite-equalizer universal
    property with the same transparent descent. *)

(** 投影以同一透明下降满足既有反等化子泛性质。 *)

Definition topos_coequalizer_universal {A B : C} (f g : Hom A B)
  : @is_coequalizer C A B f g (ToposCoequalizer f g) (topos_coeq f g).
Proof.
  split; [exact (topos_coequalizer_comm f g) |].
  intros Z h Hh. exists (topos_coequalize h Hh).
  exact (topos_coequalizer_unique h Hh).
Defined.

(** Explicitly enable the derived coequalizers through the original
    opposite equalizer interface. Import registers no chosen structure. *)

(** 通过原反等化子接口显式启用推导的余等化子；导入不注册选定结构。 *)

Program Definition Topos_HasCoequalizer
  : HasCoequalizer C
  :=
  {|hasOpEqualizer :=
      {|EqObj A B f g := ToposCoequalizer f g
      ; eqι A B f g := topos_coeq f g
      ; equalizer_universal A B f g := topos_coequalizer_universal f g
      |}
  |}.

End ToposCoequalizers.

(** ** Pushouts and Finite Colimits

    Combine the already derived initial objects and coproducts with the
    new coequalizers through the existing opposite finite-limit theory.
    Shape finiteness remains explicit data, with no global choices. *)

(** ** 推出与有限余极限

    经既有反有限极限理论，将已推导始对象、余积与新余等化子组合。形状有限性
    保持为显式数据，不作全局选择。 *)

Section ToposFiniteColimits.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HX : !HasExponential HP}.

(** The general coproduct/coequalizer construction gives chosen pushouts. *)

(** 一般余积／余等化子构造给出选定推出。 *)

Definition Topos_HasPushout
  : HasPushout C
  := @CoproductCoequalizerPushout C
      (@Topos_HasCoproduct C HT HC PB HP HX)
      (@Topos_HasCoequalizer C HT HC PB HP HX).

(** A supplied finite object/hom cover gives all colimits of that shape. *)

(** 给定有限对象／Hom 覆盖给出该形状的全部余极限。 *)

Definition ToposFiniteColimits {J : Cat} `{HJ : !HasFiniteHomCover J}
  : HasColimitsOfShape C J
  := @FiniteColimits C J (@Topos_HasInitial C HT HC PB HP HX)
      (@Topos_HasCoproduct C HT HC PB HP HX)
      (@Topos_HasCoequalizer C HT HC PB HP HX) HJ.

(** A supplied finite generating graph also suffices; all mediator and
    diagram laws are inherited from the same general construction. *)

(** 给定有限生成图也已足够；全部中介与图式定律均继承自同一一般构造。 *)

Definition ToposGeneratedColimits {J : Cat} `{HJ : !HasFiniteGen J}
  : HasColimitsOfShape C J
  := @GeneratedColimits C J (@Topos_HasInitial C HT HC PB HP HX)
      (@Topos_HasCoproduct C HT HC PB HP HX)
      (@Topos_HasCoequalizer C HT HC PB HP HX) HJ.

End ToposFiniteColimits.
