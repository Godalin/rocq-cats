From Cats Require Import
  Cat.Core
  Cat.Preorder
  Cat.Terminal
  Cat.Product.Core
  Cat.Functor.Core
  Cat.Functor.Cartesian
  Cat.Functor.Codiscrete
  Cat.Natural
  Cat.Cartesian.Core
  Cat.Cartesian.Construction
  Cat.Cartesian.Category
  Cat.Groupoid.Core
  Cat.Groupoid.Preorder
  Cat.Groupoid.CoreGpd
  Cat.Groupoid.Category.

(** * Universes of Structured Categories

    The constructions check self-membership at distinct universe instances.
    Exercise categorical clients and computation of selected product and
    inverse witnesses here. *)

(** * 结构范畴的宇宙

    构造模块检查不同宇宙实例间的自身成员关系；此处检查实际范畴客户端
    及选定积与逆见证的计算。 *)

(** ** Cartesian Clients

    The stored product choice supplies ordinary pairing and its laws.
    The ambient category is explicit because the objects are bundles. *)

(** ** 笛卡尔客户端

    保存的积选择提供普通配对及其定律。对象本身为结构包，故显式指定环境范畴。 *)

Section CartesianClients.
Context (S C D : @Ob CartUniv)
    (F F' : (@Hom CartUniv) S C) (G : (@Hom CartUniv) S D).
Let HP := hasProduct CartUniv.
Local Existing Instance HP.

Definition universe_pair
  : (@Hom CartUniv) S (C × D)
  := ⟨F,G⟩.

Example universe_pair_rewrites (H : F ≈ F')
  : ⟨F,G⟩ ≈ ⟨F',G⟩.
Proof. rewrite H. reflexivity. Qed.

Example universe_pair_first
  : π1 ∘ universe_pair ≈ F.
Proof. apply product_β1. Qed.

Example universe_pair_second
  : π2 ∘ universe_pair ≈ G.
Proof. apply product_β2. Qed.

Example universe_pair_unique (K : (@Hom CartUniv) S (C × D))
    (H1 : π1 ∘ K ≈ F) (H2 : π2 ∘ K ≈ G)
  : K ≈ universe_pair.
Proof. apply (product_pair_unique S F G). split; assumption. Qed.

End CartesianClients.

(** ** Stored Choices and Computation

    Two codiscrete bundles share a category but choose different terminal
    and product objects. Pairing must keep each component's choice. *)

(** ** 保存的选择与计算

    两个余离散结构包共享范畴，但选定不同终对象及积对象。
    配对必须分别保留各分量的选择。 *)

Module CartesianComputation.
Definition Left
  : CartCat
  := CodiscreteCart bool false.

Definition Right
  : CartCat
  := CodiscreteCart bool true.

Program Definition Change
  : CartFctS Left Right
  :=
  {|CartF := @IdF Left
  ; cartesian_isCartF :=
    {|functor_terminal := _
    ; functor_product X Y := _
    |}
  |}.
Next Obligation.
  intro X. exists tt. split; [exact I |]. intros f _. exact tt.
Defined.
Next Obligation.
  intros Z f g. exists tt. split.
  - split; exact tt.
  - intros h _. exact tt.
Defined.

Definition ChangePair
  : (@Hom CartUniv) Left (ProdCart Left Right)
  := @Cats.Cat.Product.Core.pair CartUniv (hasProduct CartUniv) Left Right Left
    (IdCartF Left (hasTerminal Left) (hasProduct Left)) Change.

Example terminal_choices_compute
  : @Term (ProdCart Left Right) (hasTerminal (ProdCart Left Right))
      = (false,true).
Proof. reflexivity. Qed.

Example product_choices_compute
  : @Prod (ProdCart Left Right) (hasProduct (ProdCart Left Right))
      (true,false) (false,true) = (false,true).
Proof. reflexivity. Qed.

Example mediator_object_computes
  : ChangePair true = (true,true).
Proof. reflexivity. Qed.

Example mediator_arrow_computes
  : fmap ChangePair (X := false) (Y := true) tt = (tt,tt).
Proof. reflexivity. Qed.

Example terminal_functor_computes
  : (@term CartUniv (hasTerminal CartUniv) Left) true = tt.
Proof. reflexivity. Qed.

End CartesianComputation.

(** ** Equivalences and Their Selected Inverses

    A nontrivial object swap in a codiscrete groupoid is an arrow of the
    groupoid universe. Its chosen quasi-inverse must remain executable. *)

(** ** 等价及其选定逆

    余离散群胚的非平凡对象交换给出群胚宇宙中的态射，
    其选定拟逆必须仍可执行。 *)

Module GroupoidComputation.
Definition Two
  : Gpd
  := CodiscreteGpd bool.

Program Definition Swap
  : Fct Two Two
  :=
  {|F0 := negb
  ; F1 X Y f := tt
  |}.
Next Obligation. intros f g H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

Definition SwapEquivalence
  : (@Hom GpdUniv) Two Two
  := (Swap; (Swap;
      (CodiscreteNatIso (Swap ∘F Swap) IdF,
       CodiscreteNatIso (Swap ∘F Swap) IdF))).

Example equivalence_computes
  : (fmap GpdForgetF SwapEquivalence) false = true.
Proof. reflexivity. Qed.

Example inverse_computes
  : (fmap GpdForgetF (gpd_inv SwapEquivalence)) true = false.
Proof. reflexivity. Qed.

Example inverse_law
  : gpd_inv SwapEquivalence ∘ SwapEquivalence ≈ id.
Proof. apply gpd_inv_l. Qed.

Example inverse_rewrites
  : SwapEquivalence ∘ (gpd_inv SwapEquivalence ∘ SwapEquivalence)
      ≈ SwapEquivalence.
Proof. rewrite gpd_inv_l. apply comp_id_r. Qed.

End GroupoidComputation.

(** ** Independent Sizes

    Both strict orders between hom carriers and equality witnesses are
    accepted; law bounds are larger and object bounds remain independent. *)

(** ** 独立大小

    同时接受 Hom 载体及相等见证的两种严格大小次序，
    定律界更大，对象界保持独立。 *)

Section IndependentSizes.
Universes o h p l.
Constraint h < p.
Constraint p < l.
Constraint l < o.
Context (C : CartCat@{l o h p l}) (D : CartCat@{l o p h l})
    (G : Gpd@{o h p l}) (H : Gpd@{o p h l}).

Definition mixed_size_product
  : CartCat
  := ProdCart C D.

Definition high_equality_cartesian_object
  : @Ob CartUniv
  := C.

Definition low_equality_cartesian_object
  : @Ob CartUniv
  := D.

Definition high_equality_groupoid_object
  : @Ob GpdUniv
  := G.

Definition low_equality_groupoid_object
  : @Ob GpdUniv
  := H.

End IndependentSizes.
