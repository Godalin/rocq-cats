From Cats Require Import
  Cat.Core
  Cat.Product.Core.

(** * Binary Coproducts *)

(** * 二元余积 *)

(** A candidate coproduct is a product in the opposite category. *)

(** 候选余积就是反范畴中的积。 *)

Definition is_coproduct {C : Cat} (X Y S : @Ob C)
    (i : Hom X S) (j : Hom Y S)
  := @is_product (C^op) X Y S i j.

Notation "S '⦂' '≅' X '⊔' Y 'with' i ',' j"
  := (is_coproduct X Y S i j) (at level 50).

(** Store only the selected products of the opposite category. *)

(** 只存储反范畴的选定积。 *)

Class HasCoproduct (C : Cat)
  :=
  { hasOpProduct :: HasProduct (C^op)
  }.

Section Coproduct.
Context {C : Cat} `{HC : !HasCoproduct C}.

(** The coproduct object is the selected opposite product. *)

(** 余积对象就是选定的反范畴积。 *)

Definition Coprod (X Y : @Ob C)
  : @Ob C
  := @Prod (C^op) (@hasOpProduct C HC) X Y.

(** The first injection is the opposite first projection. *)

(** 第一注入就是反范畴中的第一投影。 *)

Definition ι1 {X Y}
  : Hom X (Coprod X Y)
  := @Cat.Product.Core.π1 (C^op) (@hasOpProduct C HC) X Y.

(** The second injection is the opposite second projection. *)

(** 第二注入就是反范畴中的第二投影。 *)

Definition ι2 {X Y}
  : Hom Y (Coprod X Y)
  := @Cat.Product.Core.π2 (C^op) (@hasOpProduct C HC) X Y.

(** The full universal property is the original product property. *)

(** 完整泛性质直接取原来的积泛性质。 *)

Definition coproduct_universal {X Y}
  : is_coproduct X Y (Coprod X Y) ι1 ι2
  := @product_universal (C^op) (@hasOpProduct C HC) X Y.

(** Copairing uses the original product mediator without a new choice. *)

(** 余配对直接使用原来的积中介，不作新的选择。 *)

Definition copair {X Y Z} (f : Hom X Z) (g : Hom Y Z)
  : Hom (Coprod X Y) Z
  := @pair (C^op) (@hasOpProduct C HC) X Y Z f g.

(** Copairing is the unique map with the specified injection composites. *)

(** 余配对是具有指定注入复合的唯一映射。 *)

Theorem coproduct_copair_unique {X Y Z} (f : Hom X Z) (g : Hom Y Z)
  : is_unique (λ h, h ∘ ι1 ≈ f ∧ h ∘ ι2 ≈ g) (copair f g).
Proof. exact (@product_pair_unique (C^op) (@hasOpProduct C HC) X Y Z f g). Qed.

(** Copairing respects both designated hom equalities. *)

(** 余配对保持两侧指定的 Hom 相等。 *)

Global Instance coproduct_copair_proper {X Y Z}
  : Proper (@HomEq[X, Z] ==> @HomEq[Y, Z] ==>
      @HomEq[Coprod X Y, Z]) (@copair X Y Z).
Proof. exact (@product_pair_proper (C^op) (@hasOpProduct C HC) X Y Z). Qed.

(** Copairing after the first injection recovers its first component. *)

(** 余配对与第一注入复合后恢复第一分量。 *)

Theorem coproduct_β1 {X Y Z} (f : Hom X Z) (g : Hom Y Z)
  : copair f g ∘ ι1 ≈ f.
Proof. exact (@product_β1 (C^op) (@hasOpProduct C HC) X Y Z f g). Qed.

(** Copairing after the second injection recovers its second component. *)

(** 余配对与第二注入复合后恢复第二分量。 *)

Theorem coproduct_β2 {X Y Z} (f : Hom X Z) (g : Hom Y Z)
  : copair f g ∘ ι2 ≈ g.
Proof. exact (@product_β2 (C^op) (@hasOpProduct C HC) X Y Z f g). Qed.

(** Postcomposition distributes over copairing. *)

(** 后合成分配到余配对的两个分量。 *)

Theorem coproduct_comp_l {X Y Z W}
    (f : Hom X Z) (g : Hom Y Z) (h : Hom Z W)
  : h ∘ copair f g ≈ copair (h ∘ f) (h ∘ g).
Proof. exact (@product_comp_r (C^op) (@hasOpProduct C HC) X Y Z W f g h). Qed.

(** A map out of a coproduct is determined by its injection composites. *)

(** 从余积出发的映射由其与注入的复合确定。 *)

Theorem coproduct_η {X Y Z} (h : Hom (Coprod X Y) Z)
  : h ≈ copair (h ∘ ι1) (h ∘ ι2).
Proof. exact (@product_η (C^op) (@hasOpProduct C HC) X Y Z h). Qed.

End Coproduct.

Notation "X '⊔' Y" := (Coprod X Y)
  (at level 41, right associativity) : ob_scope.
Notation "'⦗' f ',' g '⦘'" := (copair f g) : hom_scope.

(** Coproduct uniqueness is product uniqueness in the opposite category. *)

(** 余积唯一性就是反范畴中的积唯一性。 *)

Definition coproduct_unique {C : Cat} {X Y S T : @Ob C}
    {i : Hom X S} {j : Hom Y S} {i' : Hom X T} {j' : Hom Y T}
    (HS : is_coproduct X Y S i j) (HT : is_coproduct X Y T i' j')
  : S ≅[C] T.
Proof.
  pose (e := @product_unique (C^op) X Y T S i' j' i j HT HS).
  exists e.1, e.2.1. split;
    [exact (snd e.2.2) | exact (fst e.2.2)].
Defined.
