From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Cat.CCC.Core
  Cat.CCC.Functor
  Cat.CCC.Category
  Instance.Set.Core.
From CatsTests Require Import
  BundledCartesian.

(** * The Category of CCC Bundles

    Exercise ordinary categorical notation, setoid rewriting, and forgetting
    structured functors. Two bundles over the same category retain different
    choices while admitting an actual structured arrow between them. *)

(** * CCC 结构包的范畴

    检查普通范畴记号、广集重写及保结构函子的忘却。同一范畴上的两个结构包
    保留不同选择，同时具有实际的保结构连接态射。 *)

(** ** Ordinary Categorical Clients

    Fix three objects of CCCCat and arrows between them. The canonical
    category must infer the intended homs and rewriting through composition. *)

(** ** 普通范畴客户端

    固定 CCCCat 的三个对象及其间态射，规范范畴须能推断对应 Hom，
    并支持穿过复合的重写。 *)

Section CategoricalClients.
Context (C D E : @Ob CCCCat) (F F' : Hom C D) (G : Hom D E).

Definition structured_composite
  : Hom C E
  := G ∘ F.
Definition underlying_composite
  : Fct C E
  := fmap CCCForgetF structured_composite.

Example structured_composition_rewrites (H : F ≈ F')
  : G ∘ F ≈ G ∘ F'.
Proof. rewrite H. reflexivity. Qed.

End CategoricalClients.

(** ** Distinct Choices and Concrete Computation

    Reuse the two terminal-map witnesses from BundledCartesian. Products
    and exponentials agree definitionally, so the existing identity
    preservation fields give a CCC arrow without equating the bundles. *)

(** ** 不同选择及具体计算

    复用 BundledCartesian 的两份终箭头见证。积与指数按定义一致，
    因而已有恒等保持性字段给出 CCC 态射，无需识别两个结构包。 *)

Module ChangedChoices.
Import SeparateChoices.

Program Definition ChoiceChangePreservation
  : @IsCCCF (TokenCCC false) (TokenCCC true) IdF
  :=
  {|isCartF := @isCartF (TokenCCC false) (TokenCCC false) IdF
      (IdF_IsCCCF (TokenCCC false))
  ; functor_exponential :=
      @functor_exponential (TokenCCC false) (TokenCCC false) IdF
        (IdF_IsCCCF (TokenCCC false))
  |}.

Definition ChoiceChange
  : (@Hom CCCCat) (TokenCCC false) (TokenCCC true)
  := CCCFctFromPreservation
    (C := TokenCCC false) (D := TokenCCC true) IdF ChoiceChangePreservation.

Example forget_choice_change_computes
  : fmap (fmap CCCForgetF ChoiceChange)
      (@Cats.Cat.Core.id (TokenCCC false) TokenS) false = false.
Proof. reflexivity. Qed.

Example composite_forget_computes
  : fmap (fmap CCCForgetF
      (@Cats.Cat.Core.comp CCCCat _ _ _ (@Cats.Cat.Core.id CCCCat (TokenCCC true)) ChoiceChange))
      (@Cats.Cat.Core.id (TokenCCC false) TokenS) true = true.
Proof. reflexivity. Qed.

End ChangedChoices.

(** ** Larger Auxiliary Proof Bounds

    Keep object, hom and equality sizes distinct. A functor whose auxiliary
    proof bounds exceed the category laws still enters the common hom-set
    through its transparent view, retaining its selected exponential inverse. *)

(** ** 更大的辅助证明界

    保持对象、Hom 及相等大小分离。辅助证明界高于范畴定律界的函子仍能通过
    透明视图进入共同 Hom，保留其选定的指数逆。 *)

Section ProofBounds.
Universes o h p l m n.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < m.
Constraint m < n.
Constraint n < o.
Context (C D : CCC@{o h p l l})
    (F : CCCFct@{o h p l l l m n o h p l} C D).

Definition larger_proof_hom
  : (@Hom CCCCat) C D
  := CCCCatHom F.

Example larger_proof_inverse_kept (X Y : C)
  : (ccc_functor_exponential larger_proof_hom X Y).1
      = (ccc_functor_exponential F X Y).1.
Proof. reflexivity. Qed.

End ProofBounds.
