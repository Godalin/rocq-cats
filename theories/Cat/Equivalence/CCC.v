From Cats Require Export
  Cat.Equivalence.Cartesian.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Functor.Cartesian
  Cat.Functor.Closed
  Cat.Natural
  Cat.CatCat
  Cat.CCC
  Cat.Product.Core
  Cat.Limit.Product
  Cat.Exponential.Core
  Cat.Exponential.Transport
  Cat.Exponential.Preservation.

(** * Cartesian Closed Structure along Specified Equivalences

    Exponentials are lifted through the fully faithful inverse functor.
    This uses only its product preservation, the source exponentials and the
    supplied object isomorphisms, without new choice or coherence axioms. *)

(** * 沿指定等价运输笛卡尔闭结构

    指数通过全忠实逆函子提升；仅使用其积保持性、来源指数及给定对象同构，
    不引入新的选择或相干公理。 *)

Local Open Scope cat_scope.
Local Open Scope hom_scope.

Section QuasiInverseExponentials.
Context {C D : Cat} (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF)
    `{PC : !HasProduct C} `{EC : !HasExponential PC}.

Let PD
  : HasProduct D
  := QuasiInverseHasProduct F G u v.
Local Existing Instance PD.

Let HG
  : is_fully_faithful G
  := quasi_inverse_fully_faithful G F v u.
Let GP
  := λ X Y, right_adjoint_preserves_product
    (QuasiInverseAdjunction F G u v) (@product_universal D PD X Y).

(** The transported representing object is the forward image of the
    exponential of the two inverse-image objects. *)

(** 运输后的表示对象是两个逆像对象之指数的正向像。 *)

Definition QuasiInverseExp (X Y : @Ob D)
  : @Ob D
  := F ((G Y ^ G X)%ob).

(** Fullness of the inverse functor selects evaluation by lifting the
    source evaluation after the object and product comparisons. *)

(** 逆函子的满性通过对象及积比较之后的来源求值，提升并选择求值箭头。 *)

Definition quasi_inverse_eval (X Y : @Ob D)
  : Hom (QuasiInverseExp X Y × X) Y
  := (fst HG _ _
      ((@Cats.Cat.Exponential.Core.eval C PC EC (G X) (G Y) ∘
        (u.1 ((G Y ^ G X)%ob) × id)) ∘
        (PreservedProductIso G GP (QuasiInverseExp X Y) X).1)).1.

(** Mapping the lifted evaluation recovers its specified comparison square. *)

(** 映射提升后的求值，恢复指定比较方形。 *)

Lemma quasi_inverse_eval_fmap (X Y : @Ob D)
  : fmap G (quasi_inverse_eval X Y) ≈
      (@Cats.Cat.Exponential.Core.eval C PC EC (G X) (G Y) ∘
        (u.1 ((G Y ^ G X)%ob) × id)) ∘
        (PreservedProductIso G GP (QuasiInverseExp X Y) X).1.
Proof. exact (fst HG _ _ _).2. Qed.

(** After inverse product comparison the image is precisely the source
    evaluation with its representing object changed by the supplied iso. *)

(** 与逆向积比较复合后，像恰为沿给定同构更换表示对象的来源求值。 *)

Lemma quasi_inverse_eval_image (X Y : @Ob D)
  : exponential_image_eval G GP (quasi_inverse_eval X Y) ≈
      @Cats.Cat.Exponential.Core.eval C PC EC (G X) (G Y) ∘
        (u.1 ((G Y ^ G X)%ob) × id).
Proof.
  unfold exponential_image_eval. rewrite quasi_inverse_eval_fmap.
  pose (i := PreservedProductIso G GP (QuasiInverseExp X Y) X).
  change (((@Cats.Cat.Exponential.Core.eval C PC EC (G X) (G Y) ∘
    (u.1 ((G Y ^ G X)%ob) × id)) ∘ i.1) ∘ i.2.1 ≈
      @Cats.Cat.Exponential.Core.eval C PC EC (G X) (G Y) ∘
        (u.1 ((G Y ^ G X)%ob) × id)).
  rewrite comp_assoc, (snd i.2.2), comp_id_r. reflexivity.
Qed.

(** Reflect the exponential universal property after changing its source
    representing object by the specified natural-isomorphism component. *)

(** 沿指定自然同构分量更换来源表示对象后，反映指数泛性质。 *)

Definition quasi_inverse_exponential_universal (X Y : @Ob D)
  : is_exponential X Y (QuasiInverseExp X Y) (quasi_inverse_eval X Y).
Proof.
  apply (fully_faithful_reflects_exponential G GP HG).
  refine (exponential_eval_equiv
    (symmetry (quasi_inverse_eval_image X Y)) _).
  refine (exponential_apex_iso
    (@exponential_universal C PC EC (G X) (G Y))
    (iso_symm (u.1 ((G Y ^ G X)%ob); u.2 ((G Y ^ G X)%ob))) _ _).
  change ((@Cats.Cat.Exponential.Core.eval C PC EC (G X) (G Y) ∘
    (u.1 ((G Y ^ G X)%ob) × id)) ∘
      ((u.2 ((G Y ^ G X)%ob)).1 × id) ≈
        @Cats.Cat.Exponential.Core.eval C PC EC (G X) (G Y)).
  rewrite comp_assoc, <- cross_comp, (snd (u.2 ((G Y ^ G X)%ob)).2),
    comp_id_l, cross_id, comp_id_r. reflexivity.
Defined.

(** Select all transported exponentials relative to the transported
    products, retaining the lifted evaluation and transpose computations. *)

(** 相对于运输后的积选择全部运输指数，保留提升求值及转置的计算。 *)

Program Definition QuasiInverseHasExponential
  : HasExponential PD
  :=
  {|exp Y X := QuasiInverseExp X Y
  ; eval X Y := quasi_inverse_eval X Y
  ; exponential_universal X Y := quasi_inverse_exponential_universal X Y
  |}.

End QuasiInverseExponentials.

(** Assemble the three transported choices explicitly. Importing this
    construction does not select any concrete model globally. *)

(** 显式组合三个运输选择；导入此构造不会全局选定任何具体模型。 *)

Program Definition QuasiInverseCCC {C D : Cat}
    (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF) (HC : CCC C)
  : CCC D
  :=
  {|hasTerminal := @QuasiInverseHasTerminal C D F G u v
      (@hasTerminal C HC)
  ; hasProduct := @QuasiInverseHasProduct C D F G u v (@hasProduct C HC)
  ; hasExponential := @QuasiInverseHasExponential C D F G u v
      (@hasProduct C HC) (@hasExponential C HC)
  |}.

(** The ordinary equivalence presentation gives the same explicit choice. *)

(** 通常的等价呈现给出同一个显式选择。 *)

Definition EquivalenceCCC {C D : Cat} (e : C ≃C D) (HC : CCC C)
  : CCC D
  := QuasiInverseCCC e.1 e.2.1 (fst e.2.2) (snd e.2.2) HC.

(** Full faithfulness and essential surjectivity make the canonical
    exponential comparison invertible between any two specified CCC choices.
    Candidate uniqueness identifies its forward arrow with the usual curry. *)

(** 对任意两侧指定 CCC 选择，全忠实性和本质满性使规范指数比较可逆。
    候选唯一性将其正向箭头确定为通常的柯里化。 *)

Program Definition FullyFaithfulIsCCCF {C D : Cat} (F : Functor C D)
    (HC : CCC C) (HD : CCC D) (HF : is_fully_faithful F)
    (HS : is_essentially_surjective F)
    (HP : IsCartesianF F (@hasTerminal C HC) (@hasProduct C HC))
  : IsCCCF F HC HD
  :=
  {|isCartesianF := HP
  |}.
Next Obligation.
  exact (exponential_unique
    (@equivalence_preserves_exponential C D F HF HS
      (@hasProduct C HC) (@hasProduct D HD)
      (@functor_product C D F (@hasTerminal C HC) (@hasProduct C HC) HP)
      X Y (@exp C (@hasProduct C HC) (@hasExponential C HC) Y X)
      (@Cats.Cat.Exponential.Core.eval C (@hasProduct C HC)
        (@hasExponential C HC) X Y)
      (@exponential_universal C (@hasProduct C HC)
        (@hasExponential C HC) X Y))
    (@exponential_universal D (@hasProduct D HD)
      (@hasExponential D HD) (F X) (F Y))).2.
Defined.

(** Either quasi-inverse preserves any specified source/target CCC choices,
    including the choices produced by [QuasiInverseCCC]. *)

(** 任一拟逆都保持两侧任意指定 CCC 选择，包括 [QuasiInverseCCC] 的选择。 *)

Definition QuasiInverseIsCCCF {C D : Cat}
    (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF)
    (HC : CCC C) (HD : CCC D)
  : IsCCCF F HC HD
  := FullyFaithfulIsCCCF F HC HD (quasi_inverse_fully_faithful F G u v)
      (quasi_inverse_essentially_surjective F G v)
      (@QuasiInverseIsCartesianF C D F G u v
        (@hasTerminal C HC) (@hasProduct C HC)).

(** Bundle this preservation without changing the specified functor. *)

(** 打包此保持性，不改变指定函子。 *)

Definition QuasiInverseCCCF {C D : Cat}
    (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF)
    (HC : CCC C) (HD : CCC D)
  : CCCFunctor HC HD
  := CCCFunctorFromPreservation F (QuasiInverseIsCCCF F G u v HC HD).

(** The forward equivalence is a CCC functor into its transported model. *)

(** 正向等价是进入运输模型的 CCC 函子。 *)

Definition EquivalenceCCCF {C D : Cat} (e : C ≃C D) (HC : CCC C)
  : CCCFunctor HC (EquivalenceCCC e HC)
  := QuasiInverseCCCF e.1 e.2.1 (fst e.2.2) (snd e.2.2) HC
      (EquivalenceCCC e HC).

(** Its specified inverse is a CCC functor back to the source model. *)

(** 指定逆是返回来源模型的 CCC 函子。 *)

Definition EquivalenceInverseCCCF {C D : Cat} (e : C ≃C D) (HC : CCC C)
  : CCCFunctor (EquivalenceCCC e HC) HC
  := QuasiInverseCCCF e.2.1 e.1 (snd e.2.2) (fst e.2.2)
      (EquivalenceCCC e HC) HC.
