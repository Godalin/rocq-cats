From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Pullback
  Cat.Morphism
  Topos.Sub.
From Cats Require Import
  Instance.Set.Core
  Cat.Coproduct.Core
  Cat.Coequalizer
  Cat.Equalizer
  Cat.Pushout
  Instance.Set.Limit
  Instance.Set.Colimit
  Instance.Set.Pushout.

From Cats Require Import
  Instance.Set.Simplicial.Vertex.Coskeletal.

(** Coskeletal vertex-nerve structures also require explicit enabling. *)

(** 顶点 nerve 的余骨架结构同样需要显式启用。 *)

Section VertexCoskeletalChoice.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C).

Fail Definition unchosen_vertex_coskeletal
  : Nᵥ(T) ⦂ Cosk[2%nat]
  := ltac:(typeclasses eauto).
End VertexCoskeletalChoice.

(** Importing concrete models alone must not silently choose structures. *)

(** 仅导入具体模型不得隐式选择结构。 *)

Fail Definition unchosen_set_coproducts
  : HasCoproduct SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_coequalizers
  : HasCoequalizer SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_equalizers
  : HasEqualizer SetCat
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_pushouts
  : HasPushout SetCat
  := ltac:(typeclasses eauto).

Section Pullback.
Context {C : Cat} `{HP : !HasPullback C}.
Context {X Y Z P : @Ob C} (f : Hom X Z) (g : Hom Y Z).
Context (p1 : Hom P X) (p2 : Hom P Y).

(** A pair of legs alone must not supply a mediator for a noncommuting cone. *)

(** 仅有两条锥腿不足以为不交换的锥提供中介。 *)

Fail Definition mediator_without_commutativity : Hom P (Pb f g) :=
  @pb C HP X Y Z f g P p1 p2.

End Pullback.

Section Classifier.
Context {C : Cat} `{HT : !HasTerminal C} `{HC : !HasSubObjClassifier C HT}.
Context {X Y : @Ob C} (m : X ↣ Y).

(** The selected square is not evidence that an arbitrary candidate classifies m. *)

(** 选定方形不能证明任意候选都分类给定单态射。 *)

Fail Definition arbitrary_candidate_unique (c : Hom Y Ω) : c ≈ χ m :=
  that (classifier_char_unique (m := m)) c (this (classifier_char_unique (m := m))).

End Classifier.

From Cats Require Import
  Instance.Set.Monoid.

(** Importing a cartesian model must not choose a default monoidal structure. *)

(** 导入笛卡尔模型不得自动选定默认幺半结构。 *)

Fail Definition unchosen_set_monoidal
  : HasMonoidal SetCat
  := ltac:(typeclasses eauto).

(** The weaker tensor choices also require explicit selection. *)

(** 较弱的张量选择同样须显式提供。 *)

Fail Definition unchosen_set_binoidal
  : HasBinoidal SetCat
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Monoidal.Premonoidal.

(** ** Independent Premonoidal Choices

    A fixed tensor may have only an associator or only unitors. Inheriting
    one package must not select the other or a complete extension. *)

(** ** 独立的预幺半选择

    固定张量可以只具有结合子或单位子；继承一份选择不得选定另一份或完整扩展。 *)

Section AssociatorChoice.
Context {C : Cat} `{BC : !HasBinoidal C} `{AC : !@HasTensorAssoc C BC}.

Fail Definition unchosen_unitors
  : @HasTensorUnitors C BC
  := ltac:(typeclasses eauto).

End AssociatorChoice.

(** Unit choices alone likewise select no associator. *)

(** 同样，单独的单位选择不选定结合子。 *)

Section UnitorChoice.
Context {C : Cat} `{BC : !HasBinoidal C} `{UC : !@HasTensorUnitors C BC}.

Fail Definition unchosen_associator
  : @HasTensorAssoc C BC
  := ltac:(typeclasses eauto).

End UnitorChoice.

From Cats Require Import
  Cat.Monoidal.Constant.

(** Bundling the underlying functor must not register a chosen lax structure
    for the concrete model. Clients choose identity or constant explicitly. *)

(** 打包底层函子不得为具体模型注册选定 lax 结构；恒等及常值结构由客户端
    显式选择。 *)

Fail Definition unchosen_set_lax_monoidal
  : LaxMonoidalFct SetCartMonoidal SetCartMonoidal
  := ltac:(typeclasses eauto).

(** Adding invertible comparisons must not choose a monoidal functor. *)

(** 增加比较的可逆性不得自动选取幺半函子。 *)

Fail Definition unchosen_set_monoidal_fct
  : MonoidalFct SetCartMonoidal SetCartMonoidal
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Applicative.Core.

(** Importing the theory must not select an Applicative on the model. *)

(** 导入理论不得为模型自动选定 Applicative。 *)

Fail Definition unchosen_set_applicative
  : Applicative SetCat SetCat_HasTerminal SetCat_HasProduct
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Functor.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Fixed
  Instance.Set.Sieve.Matching.

(** Canonical projections infer the specified set equality from the carrier
    types, without an explicit set annotation or comparison of law fields. *)

(** 典范投影从载体类型推断指定广集相等，无须显式标注广集或比较定律字段。 *)

Definition inferred_family_map_equality {X : SetC} {A B : FamS X}
    (f g : A →Fam B)
  : Type
  := f ≈S g.

Definition inferred_matching_equality {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    (P : Fct (C^op) SetCat) (a b : SieveMatching g P)
  : Type
  := a ≈S b.

From Cats Require Import
  Cat.FreeObject.Adjunction.

(** The general theorem does not install a chosen free-object structure. *)

(** 一般定理不自动注册选定自由对象结构。 *)

Fail Definition unchosen_free_objects
  : HasFreeObj (@IdF SetCat)
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.CCC.Functor
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC.Core
  Instance.Set.CCC.

(** Bundled preservation does not select concrete cartesian or CCC functors
    merely by import. *)

(** 导入打包保持性接口不会自动选定具体笛卡尔或 CCC 函子。 *)

Fail Definition unchosen_set_cartesian_fct
  : @CartFct SetCat SetCat SetCat_HasTerminal SetCat_HasProduct
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_ccc_fct
  : CCCFct SetCat_CCC SetCat_CCC
  := ltac:(typeclasses eauto).

(** Cartesian inheritance needs no chosen structures in the target. *)

(** 笛卡尔保持性的继承不需要目标中的选定结构。 *)

Section BundledCartesianInference.
Context {C D : Cat} {TC : HasTerminal C} {PC : HasProduct C}
    (F : @CartFct C D TC PC).

Definition inferred_cartesian_preservation
  : IsCartF F TC PC
  := ltac:(typeclasses eauto).
End BundledCartesianInference.

(** A supplied CCC bundle supports both inherited interfaces and the
    existing curry theorem through its single functor coercion chain. *)

(** 给定 CCC 包通过单一函子强制转换链，支持两个继承接口及已有柯里化定理。 *)

Section BundledCCCInference.
Context {C D : CCC} (F : CCCFct C D).

(** Packing a fixed functor preserves both of the supplied witnesses
    by conversion, including the dependency between them. *)

(** 打包固定函子时，两份给定见证及其依赖关系均按定义保留。 *)

Example packed_ccc_cart_witness (G : Fct C D) (H : @IsCCCF C D G)
  : isCartF (CCCFctToCartFct (CCCFctOfIsCCCF G H)) = IsCCCF_isCartF H
  := eq_refl.

Example packed_ccc_exp_witness (G : Fct C D) (H : @IsCCCF C D G)
  : CCCFct_preservesExp (CCCFctOfIsCCCF G H) = IsCCCF_preservesExp H
  := eq_refl.

Definition inferred_ccc_preservation
  : @IsCCCF C D F
  := ltac:(typeclasses eauto).
Definition inferred_ccc_cartesian_preservation
  : IsCartF F (hasTerminal C) (hasProduct C)
  := ltac:(typeclasses eauto).
Definition bundled_fct_curry {X Y Z : @Ob C} (f : Hom (Z × X) Y)
  : fct_exp_cmp F X Y ∘ fmap F (ƛ f) ≈
      ƛ (fmap F f ∘ fct_product_inv F Z X)
  := fct_curry F f.
End BundledCCCInference.
