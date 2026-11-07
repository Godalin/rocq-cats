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
  : MonoidalCategory SetCat
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
