From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.Exponential.DoubleDual
  Cat.Equalizer
  Cat.EqualizerMorphism
  Cat.Morphism.

Import Cats.Cat.Exponential.Core.

(** * Equalizing Tests and Double Evaluation

    Fix products, relative exponentials and equalizers in an arbitrary
    category. The tests which identify a parallel pair form an equalizer
    of precomposition maps. Evaluation into their power object identifies
    that pair and lifts every other identifying map to double evaluation.
    Neither a classifier nor image choices are used here. *)

(** * 等化测试与双重求值

    在任意范畴中固定积、相对指数和等化子。识别一对平行箭头的测试形成预合成
    映射的等化子。向其幂对象求值识别原箭头对，并将其他识别映射提升到双重
    求值；此处不使用分类子或像选择。 *)

Section EqualizingTests.
Context {C : Cat} `{HP : !HasProduct C} `{HX : !HasExponential HP}
    `{EQ : !HasEqualizer C}.

(** Tests are arrows into the supplied result object whose precomposites
    with the parallel pair agree. *)

(** 测试是到给定结果对象的箭头，沿平行箭头对的预合成相等。 *)

Definition EqualizingTests (R : C) {A B : C} (f g : Hom A B)
  : C
  := Eq[exp_dimap f (@Cats.Cat.Core.id C R),
      exp_dimap g (@Cats.Cat.Core.id C R)].

(** Retain the original equalizer inclusion and its monicity. *)

(** 保留原等化子包含箭头及其单态性。 *)

Definition EqualizingTestMono (R : C) {A B : C} (f g : Hom A B)
  : EqualizingTests R f g ↣ (R ^ B)
  := EqualizerMono (equalizer_universal
      (f := exp_dimap f (@Cats.Cat.Core.id C R))
      (g := exp_dimap g (@Cats.Cat.Core.id C R))).

(** Restrict double evaluation to those equalizing tests. *)

(** 将双重求值限制到这些等化测试。 *)

Definition EqualizingEvaluation (R : C) {A B : C} (f g : Hom A B)
  : Hom B (R ^ EqualizingTests R f g)
  := exp_dimap (EqualizingTestMono R f g)
      (@Cats.Cat.Core.id C R) ∘ ExpDoubleDualUnit R B.

(** The evaluation map identifies the original pair by the equation
    already stored in the test equalizer. *)

(** 求值映射通过测试等化子中已存储的方程识别原箭头对。 *)

Theorem equalizing_evaluation_comm (R : C) {A B : C} (f g : Hom A B)
  : EqualizingEvaluation R f g ∘ f ≈ EqualizingEvaluation R f g ∘ g.
Proof.
  pose (i := EqualizingTestMono R f g).
  assert (K : exp_dimap f (@Cats.Cat.Core.id C R) ∘ i
    ≈ exp_dimap g (@Cats.Cat.Core.id C R) ∘ i).
  { exact (equalizer_comm (f := exp_dimap f (@Cats.Cat.Core.id C R))
      (g := exp_dimap g (@Cats.Cat.Core.id C R))). }
  assert (H : app ((exp_dimap f (@Cats.Cat.Core.id C R) ∘ i) ∘ π2)
      π1 ≈ app ((exp_dimap g (@Cats.Cat.Core.id C R) ∘ i) ∘ π2) π1).
  { rewrite K. reflexivity. }
  rewrite !comp_assoc, !exp_app_dimap, !comp_id_l in H.
  apply exp_ext. unfold EqualizingEvaluation.
  rewrite !exp_uncurry_app, !comp_assoc,
    !exp_app_dimap, !comp_id_l, !exp_double_dual_app.
  exact H.
Qed.

(** Precomposing tests with an identifying map preserves the equalizing
    equation, using only exponential functoriality. *)

(** 沿识别映射预合成测试保持等化方程，仅用指数函子性。 *)

Definition EqualizingTestFactor (R : C) {A B Z : C} {f g : Hom A B}
    (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : Hom (R ^ Z) (EqualizingTests R f g).
Proof.
  apply (equalize (exp_dimap h (@Cats.Cat.Core.id C R))).
  apply exp_ext.
  rewrite !exp_uncurry_app, !comp_assoc,
    !exp_app_dimap, !comp_id_l.
  rewrite <- !comp_assoc, Hh. reflexivity.
Defined.

(** The selected factor retains the original precomposition map. *)

(** 选定因子保留原预合成映射。 *)

Theorem equalizing_test_factor_comm (R : C) {A B Z : C}
    {f g : Hom A B} (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : EqualizingTestMono R f g ∘ EqualizingTestFactor R h Hh
    ≈ exp_dimap h (@Cats.Cat.Core.id C R).
Proof. apply equalizer_β. Qed.

(** Restriction of tests induces a map to the target double power. *)

(** 测试的限制诱导到目标双重幂对象的映射。 *)

Definition EqualizingLift (R : C) {A B Z : C} {f g : Hom A B}
    (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : Hom (R ^ EqualizingTests R f g) (R ^ (R ^ Z))
  := exp_dimap (EqualizingTestFactor R h Hh)
      (@Cats.Cat.Core.id C R).

(** The lift extends double evaluation of the identifying map; the
    mediator's equation and double-dual naturality supply the law. *)

(** 提升延拓识别映射的双重求值；中介方程及双对偶自然性给出该定律。 *)

Theorem equalizing_lift_comm (R : C) {A B Z : C}
    {f g : Hom A B} (h : Hom B Z) (Hh : h ∘ f ≈ h ∘ g)
  : EqualizingLift R h Hh ∘ EqualizingEvaluation R f g
    ≈ ExpDoubleDualUnit R Z ∘ h.
Proof.
  unfold EqualizingLift, EqualizingEvaluation. rewrite <- comp_assoc.
  pose (H := @exp_dimap_comp C HP HX
    (R ^ B) (EqualizingTests R f g) (R ^ Z) R R R
    (EqualizingTestMono R f g) (EqualizingTestFactor R h Hh)
    (@Cats.Cat.Core.id C R) (@Cats.Cat.Core.id C R)).
  rewrite <- H, comp_id_l.
  transitivity (exp_dimap
    (exp_dimap h (@Cats.Cat.Core.id C R))
    (@Cats.Cat.Core.id C R) ∘ ExpDoubleDualUnit R B).
  - apply comp_proper; [| reflexivity].
    apply exp_dimap_proper; [| reflexivity].
    apply equalizing_test_factor_comm.
  - apply exp_double_dual_natural.
Qed.

End EqualizingTests.
