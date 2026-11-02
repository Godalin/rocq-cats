From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Pullback
  Cat.Morphism
  ETCS.Sub.

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
