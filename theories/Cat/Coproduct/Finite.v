From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Terminal
  Cat.Coproduct.Core
  Cat.Product.Finite.
From Cats Require Export
  Cat.Coproduct.Indexed.

(** * Finite Coproducts through Opposite Finite Products *)

(** * 通过反有限积构造有限余积 *)

Section FiniteCoproducts.
Context {C : Cat} `{HI : !HasInitial C} `{HC : !HasCoproduct C}.

(** The finite coproduct object is the original opposite finite product;
    the empty family uses the selected initial object. *)

(** 有限余积对象就是原反有限积；空族使用选定始对象。 *)

Definition FiniteCoproduct {n : nat} (D : Fin n → @Ob C)
  : @Ob C
  := @FiniteProduct (C^op) (@hasOpTerminal C HI) (@hasOpProduct C HC) n D.

(** The injections are the original recursive projections. *)

(** 注入就是原来的递归投影。 *)

Definition finite_coproduct_inj {n : nat} (D : Fin n → @Ob C) (i : Fin n)
  : Hom (D i) (FiniteCoproduct D)
  := @finite_product_proj (C^op) (@hasOpTerminal C HI)
      (@hasOpProduct C HC) n D i.

(** Copairing retains the original recursive finite-product mediator. *)

(** 余配对保留原递归有限积中介。 *)

Definition finite_coproduct_copair {n : nat} (D : Fin n → @Ob C)
    {X : @Ob C} (κ : ∀ i, Hom (D i) X)
  : Hom (FiniteCoproduct D) X
  := @finite_product_pair (C^op) (@hasOpTerminal C HI)
      (@hasOpProduct C HC) n D X κ.

(** The injection equation is the original finite-product beta law. *)

(** 注入方程就是原有限积 β 律。 *)

Lemma finite_coproduct_β {n : nat} (D : Fin n → @Ob C)
    {X : @Ob C} (κ : ∀ i, Hom (D i) X) (i : Fin n)
  : finite_coproduct_copair D κ ∘ finite_coproduct_inj D i ≈ κ i.
Proof.
  exact (@finite_product_β (C^op) (@hasOpTerminal C HI)
    (@hasOpProduct C HC) n D X κ i).
Qed.

(** Injection composites detect arrows out of any selected finite coproduct. *)

(** 注入复合检测从选定有限余积出发的箭头。 *)

Theorem finite_coproduct_hom_ext {n : nat} (D : Fin n → @Ob C)
    {X : @Ob C} (f g : Hom (FiniteCoproduct D) X)
    (H : ∀ i, f ∘ finite_coproduct_inj D i ≈
      g ∘ finite_coproduct_inj D i)
  : f ≈ g.
Proof.
  exact (@finite_product_hom_ext (C^op) (@hasOpTerminal C HI)
    (@hasOpProduct C HC) n D X f g H).
Qed.

(** Pointwise equal components give equal finite copairs. *)

(** 逐点相等分量给出相等的有限余配对。 *)

Global Instance finite_coproduct_copair_proper {n : nat}
    (D : Fin n → @Ob C) {X : @Ob C}
  : Proper ((λ κ μ : ∀ i, Hom (D i) X, ∀ i, κ i ≈ μ i) ==>
      @HomEq C (FiniteCoproduct D) X) (finite_coproduct_copair D).
Proof.
  exact (@finite_product_pair_proper (C^op) (@hasOpTerminal C HI)
    (@hasOpProduct C HC) n D X).
Qed.

(** The original finite discrete limit gives the ordinary discrete colimit
    through the shared self-duality adapter. *)

(** 原有限离散极限通过共用自对偶适配给出通常离散余极限。 *)

Definition FiniteCoproductColimit {n : nat}
    (D : Functor (DiscreteCat (Fin n)) C)
  : HasColimit C D
  := @DiscreteDiagramColimit C (Fin n) D
      (@FiniteProductLimit (C^op) (@hasOpTerminal C HI)
        (@hasOpProduct C HC) n (D^opF ∘F OpDiscreteF (Fin n))).

(** Select all colimits of a finite discrete shape; importing makes no choice. *)

(** 选择有限离散形状的全部余极限；导入不作选择。 *)

Definition FiniteCoproductColimits (n : nat)
  : HasColimitsOfShape C (DiscreteCat (Fin n))
  := @OpDiscreteColimits C (Fin n)
      (@FiniteProductLimits (C^op) (@hasOpTerminal C HI)
        (@hasOpProduct C HC) n).

End FiniteCoproducts.
