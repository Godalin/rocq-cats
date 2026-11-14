From Cats Require Export
  Cat.Computational.Arrow.Monad
  Cat.Computational.Arrow.Kleisli.
From Cats Require Import
  Cat.Monad.KleisliComparison
  Cat.Functor.FullyFaithful
  Cat.Adjunction
  Cat.Isomorphism
  Instance.Set.StrengthConstruction
  Instance.Set.Arrow
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid
  Instance.Set.KleisliApply.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Open Scope monoidal_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Dynamic Arrow Reconstruction through Kleisli Computations

    Fix an ArrowApply on native setoids, keeping computation-object,
    Hom carrier and equality levels independent. Give its recovered Monad
    canonical setoid strength, reuse the general Kleisli comparison and
    its full-faithful inverse, and compare both composites with identity.
    Both directions preserve pure arrows, sequencing and ordinary context.
    The computation category is indexed by value objects; no representatives
    of other ambient objects are selected. *)

(** * 经 Kleisli 计算重建动态 Arrow

    固定原生广集上的 ArrowApply，保持计算对象、Hom 载体及相等层级独立。
    为回收 Monad 赋予规范广集强度，复用一般 Kleisli 比较及全忠实逆，并将
    两个复合与恒等函子比较。双向保持纯箭头、顺序组合及通常上下文。
    计算范畴按值对象索引，不选择其他环境对象的代表。 *)

Section Recovery.
Universes o u p.
Context {K : Cat@{o u p _ _}} (AA : ArrowApply K).

(** Give the recovered Monad canonical strength, retaining exactly
    [ArrowMonad] as its underlying Monad. *)

(** 为回收 Monad 赋予规范强度，底层恰好保留 [ArrowMonad]。 *)

Definition ArrowStrongM
  : StrongMonad (SetCat@{u p _ _ _ _ _}) SetCartesianMonoidal
  := SetStrongM (ArrowMonad AA).

(** Rebuild the Arrow using the existing strong-Monad construction. *)

(** 使用已有强 Monad 构造重建 Arrow。 *)

Definition ArrowKleisli
  : Arrow (SetCat@{u p _ _ _ _ _}) (KleisliCat (ArrowMonad AA))
      SetCartesianMonoidal
  := KleisliArrow ArrowStrongM.

(** The general adjunction comparison evaluates dynamic names. Its object
    map is identity on value indices. *)

(** 一般伴随比较求值动态命名，在值索引上的对象映射为恒等。 *)

Definition DynamicEvaluationF
  : Functor (KleisliCat (ArrowMonad AA)) (ComputationCat AA)
  := AdjunctionKleisliF (ArrowApplyAdjunction AA).

(** Reuse the general comparison theorem with computational transpose
    preimages; no native Hom sizes are identified. *)

(** 复用带可计算转置原像的一般比较定理，不等同原生 Hom 大小。 *)

Definition dynamic_evaluation_fully_faithful
  : is_fully_faithful DynamicEvaluationF
  := adjunction_kleisli_fully_faithful (ArrowApplyAdjunction AA).

(** Name original computations as reconstructed Kleisli arrows. Both
    functor laws are inherited from the general full-faithful inverse. *)

(** 将原计算命名为重建后的 Kleisli 箭头，两条函子律均继承自一般全忠实逆。 *)

Program Definition DynamicNamingF
  : Functor (ComputationCat AA) (KleisliCat (ArrowMonad AA))
  :=
  {|F0 X := X
  ; F1 X Y f := arrow_dynamic_name AA f
  ; functor_fmap_proper X Y := arrow_dynamic_name_proper AA
  |}.
Next Obligation.
  exact (@functor_id _ _ (FullyFaithfulInverseF DynamicEvaluationF
    dynamic_evaluation_fully_faithful) X).
Defined.

Next Obligation.
  exact (@functor_comp _ _ (FullyFaithfulInverseF DynamicEvaluationF
    dynamic_evaluation_fully_faithful) X Y Z f g).
Defined.

(** Evaluation after naming is naturally isomorphic to the original
    indexed computation category identity, with transparent identity maps. *)

(** 先命名再求值自然同构于原索引计算范畴的恒等，比较为透明恒等映射。 *)

Program Definition DynamicEvaluationNamingIso
  : (DynamicEvaluationF ∘F DynamicNamingF) ≅N (@IdF (ComputationCat AA))
  := ({|nt X := id
      |}; _).
Next Obligation.
  change (id ∘ arrow_dynamic_eval AA (arrow_dynamic_name AA f) ≈ f ∘ id).
  rewrite comp_id_l, comp_id_r. exact (arrow_dynamic_eval_name AA f).
Defined.

Next Obligation.
  intros X. exists id. split;
    exact (@comp_id_l (ComputationCat AA) _ _ id).
Defined.

(** Naming after evaluation is naturally isomorphic to the Kleisli
    identity. Identity components are the recovered Monad units. *)

(** 先求值再命名自然同构于 Kleisli 恒等，恒等分量是回收 Monad 的单位。 *)

Program Definition DynamicNamingEvaluationIso
  : (DynamicNamingF ∘F DynamicEvaluationF) ≅N
    (@IdF (KleisliCat (ArrowMonad AA)))
  := ({|nt X := id
      |}; _).
Next Obligation.
  transitivity (arrow_dynamic_name AA (arrow_dynamic_eval AA f)).
  - exact (@kleisli_comp_id_l SetCat (ArrowMonad AA) X Y
      (arrow_dynamic_name AA (arrow_dynamic_eval AA f))).
  - transitivity f; [exact (arrow_dynamic_name_eval AA f)|].
    symmetry. exact (@kleisli_comp_id_r SetCat (ArrowMonad AA) X Y f).
Defined.

Next Obligation.
  intros X. exists id. split;
    exact (@comp_id_l (KleisliCat (ArrowMonad AA)) _ _ id).
Defined.

(** Naming sends an original pure arrow to reconstructed Monad return. *)

(** 命名将原纯箭头送到重建后的 Monad 返回。 *)

Lemma dynamic_naming_pure {X Y : SetC@{u p}} (f : X →r Y)
  : arrow_dynamic_name AA arr[AA; f] ≈f return[ArrowMonad AA; f].
Proof.
  intros x. transitivity (arrow_value_pure K AA Y (f x)).
  - change (arr[AA; f] ∘ arr[AA; const_resp UnitS x] ≈
      arr[AA; const_resp UnitS (f x)]).
    rewrite <- functor_comp. apply functor_fmap_proper. intros []. reflexivity.
  - symmetry. exact (arrow_monad_unit AA Y (f x)).
Qed.

(** Naming preserves left ordinary context by the weaker ordinary-Arrow
    naming law and the canonical strength formula. *)

(** 由较弱的通常 Arrow 命名定律及规范强度公式，命名保持左侧通常上下文。 *)

Lemma dynamic_naming_context {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : Hom (AA X) (AA Y))
  : arrow_dynamic_name AA (context[AA; Z; f]) ≈f
    context[ArrowKleisli; Z; arrow_dynamic_name AA f].
Proof.
  intros [z x]. exact (arrow_dynamic_name_context AA Z f z x).
Qed.

(** Naming preserves sequencing as Kleisli composition, with the original
    execution order. *)

(** 命名将顺序组合保持为 Kleisli 复合，保留原执行次序。 *)

Lemma dynamic_naming_comp {X Y Z : SetC@{u p}}
    (g : Hom (AA Y) (AA Z)) (f : Hom (AA X) (AA Y))
  : arrow_dynamic_name AA (g ∘ f) ≈f
    arrow_dynamic_name AA g ∘K[ArrowMonad AA] arrow_dynamic_name AA f.
Proof.
  exact (@functor_comp (ComputationCat AA) (KleisliCat (ArrowMonad AA))
    DynamicNamingF X Y Z g f).
Qed.

(** Ordinary input substitution commutes with dynamic evaluation. *)

(** 通常输入代入与动态求值交换。 *)

Lemma dynamic_evaluation_pre {X Y Z : SetC@{u p}}
    (f : Y →r ArrowMonad AA Z) (h : X →r Y)
  : arrow_dynamic_eval AA (f ∘r h) ≈ arrow_dynamic_eval AA f ∘ arr[AA; h].
Proof. exact (unadjunct_comp_r (ArrowApplyAdjunction AA) f h). Qed.

(** Evaluation recovers the original pure arrow from reconstructed return. *)

(** 求值从重建后的返回恢复原纯箭头。 *)

Lemma dynamic_evaluation_pure {X Y : SetC@{u p}} (f : X →r Y)
  : arrow_dynamic_eval AA return[ArrowMonad AA; f] ≈ arr[AA; f].
Proof.
  transitivity (arrow_dynamic_eval AA (arrow_dynamic_name AA arr[AA; f])).
  - apply arrow_dynamic_eval_proper. symmetry. exact (dynamic_naming_pure f).
  - exact (arrow_dynamic_eval_name AA arr[AA; f]).
Qed.

(** Evaluation preserves Kleisli sequencing as original computation
    composition, reusing the comparison functor law. *)

(** 求值将 Kleisli 顺序组合保持为原计算复合，复用比较函子定律。 *)

Lemma dynamic_evaluation_comp {X Y Z : SetC@{u p}}
    (g : Y →r ArrowMonad AA Z) (f : X →r ArrowMonad AA Y)
  : arrow_dynamic_eval AA (g ∘K[ArrowMonad AA] f) ≈
    arrow_dynamic_eval AA g ∘ arrow_dynamic_eval AA f.
Proof.
  exact (@functor_comp (KleisliCat (ArrowMonad AA)) (ComputationCat AA)
    DynamicEvaluationF X Y Z g f).
Qed.

(** The inverse comparison also preserves the original ordinary context
    action, by naming preservation and the two reconstruction laws. *)

(** 由命名保持性及两条重建律，逆向比较也保持原通常上下文作用。 *)

Lemma dynamic_evaluation_context {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : X →r ArrowMonad AA Y)
  : arrow_dynamic_eval AA (context[ArrowKleisli; Z; f]) ≈
    context[AA; Z; arrow_dynamic_eval AA f].
Proof.
  transitivity (arrow_dynamic_eval AA (arrow_dynamic_name AA
    (context[AA; Z; arrow_dynamic_eval AA f]))).
  - apply arrow_dynamic_eval_proper. symmetry.
    transitivity (context[ArrowKleisli; Z;
      arrow_dynamic_name AA (arrow_dynamic_eval AA f)]).
    + exact (dynamic_naming_context Z (arrow_dynamic_eval AA f)).
    + exact (@arrow_context_proper SetCat (KleisliCat (ArrowMonad AA))
        SetCartesianMonoidal ArrowKleisli X Y Z _ _
        (arrow_dynamic_name_eval AA f)).
  - exact (arrow_dynamic_eval_name AA _).
Qed.

End Recovery.

(** * Preservation of Dynamic Application

    Use a common native carrier/equality bound, as required for the
    reconstructed Kleisli Hom setoids to be input values. Reuse its existing
    ArrowApply model on the exact same strong Monad. The application
    comparisons reindex supplied computations through naming or evaluation;
    both equations use native computation equality. *)

(** * 动态应用的保持性

    使用共同原生载体／相等界，使重建后的 Kleisli Hom 广集能够作为输入值。
    在恰好同一个强 Monad 上复用已有 ArrowApply 模型。应用比较通过命名或求值
    重索引所给计算，两个方程均使用原生计算相等。 *)

Section Application.
Universes o u.
Context {K : Cat@{o u u _ _}} (AA : ArrowApply K).

(** Extend the same reconstructed Arrow by the existing Kleisli application
    model; no second strength or parent Arrow is stored. *)

(** 通过已有 Kleisli 应用模型扩充同一重建 Arrow，不另存强度或父 Arrow。 *)

Definition ArrowKleisliApply
  : ArrowApply (KleisliCat (ArrowMonad AA))
  := KleisliArrowApply (ArrowStrongM AA).

(** Naming preserves application after naming the supplied computation
    value. The ordinary input is retained. *)

(** 命名在命名所给计算值后保持应用，保留通常输入。 *)

Lemma dynamic_naming_apply (X Y : SetC@{u u})
  : arrow_dynamic_name AA apply[AA; X; Y] ≈f
    (apply[ArrowKleisliApply; X; Y] ∘r
      (arrow_dynamic_name_resp AA X Y × id_resp)).
Proof.
  intros [f x].
  change (apply[AA; X; Y] ∘ arr[AA; const_resp UnitS (f,x)] ≈
    f ∘ arr[AA; const_resp UnitS x]).
  transitivity (arrow_apply_const AA f ∘ arr[AA; const_resp UnitS x]).
  - unfold arrow_apply_const. rewrite comp_assoc, <- functor_comp.
    apply comp_proper; [reflexivity|].
    apply functor_fmap_proper. intros []. split; reflexivity.
  - rewrite arrow_apply_const_value. reflexivity.
Qed.

(** Evaluation preserves reconstructed application after evaluating the
    supplied computation value, using native Hom equality. *)

(** 求值在求值所给计算值后保持重建应用，使用原生 Hom 相等。 *)

Lemma dynamic_evaluation_apply (X Y : SetC@{u u})
  : arrow_dynamic_eval AA apply[ArrowKleisliApply; X; Y] ≈
    apply[AA; X; Y] ∘ arr[AA;
      arrow_dynamic_eval_resp AA X Y × id_resp].
Proof.
  transitivity (arrow_dynamic_eval AA
    (arrow_dynamic_name AA apply[AA; X; Y] ∘r
      (arrow_dynamic_eval_resp AA X Y × id_resp))).
  - apply arrow_dynamic_eval_proper. intros [f x].
    change (f x ≈ arrow_dynamic_name AA apply[AA; X; Y]
      (arrow_dynamic_eval AA f,x)).
    symmetry. transitivity (arrow_dynamic_name AA (arrow_dynamic_eval AA f) x).
    + exact (dynamic_naming_apply X Y (arrow_dynamic_eval AA f,x)).
    + exact (arrow_dynamic_name_eval AA f x).
  - transitivity (arrow_dynamic_eval AA
      (arrow_dynamic_name AA apply[AA; X; Y]) ∘
        arr[AA; arrow_dynamic_eval_resp AA X Y × id_resp]).
    + exact (dynamic_evaluation_pre AA _ _).
    + apply comp_proper; [exact (arrow_dynamic_eval_name AA _)|reflexivity].
Qed.

End Application.
