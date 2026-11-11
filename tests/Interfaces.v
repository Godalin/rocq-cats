From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Pullback
  Cat.Morphism
  ETCS.Sub.
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
Context {X : SetC} {C : Cat} (T : Functor (EqGpd X) C).

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
Context {C : Cat} `{HT : !HasTerminal C} `{HC : !HasSubObjectClassifier C HT}.
Context {X Y : @Ob C} (m : X ↣ Y).

(** The selected square is not evidence that an arbitrary candidate classifies m. *)

(** 选定方形不能证明任意候选都分类给定单态射。 *)

Fail Definition arbitrary_candidate_unique (c : Hom Y Ω) : c ≈ χ m :=
  that _ _ (classifier_char_unique (m := m)) c (this _ _ (classifier_char_unique (m := m))).

End Classifier.

From Cats Require Import
  Instance.Set.Monoid.

(** Importing a cartesian model must not choose a default monoidal structure. *)

(** 导入笛卡尔模型不得自动选定默认幺半结构。 *)

Fail Definition unchosen_set_monoidal
  : MonoidalCat SetCat
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Monoidal.Constant.

(** Bundling the underlying functor must not register a chosen lax structure
    for the concrete model. Clients choose identity or constant explicitly. *)

(** 打包底层函子不得为具体模型注册选定 lax 结构；恒等及常值结构由客户端
    显式选择。 *)

Fail Definition unchosen_set_lax_monoidal
  : LaxMonoidalFunctor SetCartesianMonoidal SetCartesianMonoidal
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
    (P : Functor (C^op) SetCat) (a b : SieveMatching g P)
  : Type
  := a ≈S b.

From Cats Require Import
  Cat.FreeObject.Adjunction.

(** The general theorem does not install a chosen free-object structure. *)

(** 一般定理不自动注册选定自由对象结构。 *)

Fail Definition unchosen_free_objects
  : HasFreeObjects (@IdF SetCat)
  := ltac:(typeclasses eauto).

From Cats Require Import
  Cat.Functor.Closed
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC
  Instance.Set.CCC.

(** Bundled preservation does not select concrete cartesian or CCC functors
    merely by import. *)

(** 导入打包保持性接口不会自动选定具体笛卡尔或 CCC 函子。 *)

Fail Definition unchosen_set_cartesian_functor
  : @CartesianFunctor SetCat SetCat SetCat_HasTerminal SetCat_HasProduct
  := ltac:(typeclasses eauto).
Fail Definition unchosen_set_ccc_functor
  : CCCFunctor SetCat_CCC SetCat_CCC
  := ltac:(typeclasses eauto).

(** Cartesian inheritance needs no chosen structures in the target. *)

(** 笛卡尔保持性的继承不需要目标中的选定结构。 *)

Section BundledCartesianInference.
Context {C D : Cat} {TC : HasTerminal C} {PC : HasProduct C}
    (F : @CartesianFunctor C D TC PC).

Definition inferred_cartesian_preservation
  : IsCartesianF F TC PC
  := ltac:(typeclasses eauto).
End BundledCartesianInference.

(** A supplied CCC bundle supports both inherited interfaces and the
    existing curry theorem through its single functor coercion chain. *)

(** 给定 CCC 包通过单一函子强制转换链，支持两个继承接口及已有柯里化定理。 *)

Section BundledCCCInference.
Context {C D : Cat} {HC : CCC C} {HD : CCC D} (F : CCCFunctor HC HD).
Local Existing Instance HC.
Local Existing Instance HD.

Definition inferred_ccc_preservation
  : IsCCCF F HC HD
  := ltac:(typeclasses eauto).
Definition inferred_ccc_cartesian_preservation
  : IsCartesianF F (@hasTerminal C HC) (@hasProduct C HC)
  := ltac:(typeclasses eauto).
Definition bundled_functor_curry {X Y Z : @Ob C} (f : Hom (Z × X) Y)
  : functor_exponential_comparison F X Y ∘ fmap F (ƛ f) ≈
      ƛ (fmap F f ∘ functor_product_inv F Z X)
  := functor_curry F f.
End BundledCCCInference.
