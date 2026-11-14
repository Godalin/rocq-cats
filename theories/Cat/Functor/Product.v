From Cats Require Export
  Cat.Functor.Core.
From Cats Require Import
  Cat.Core
  Cat.Natural
  Cat.Induced
  Cat.Product.Core.

(** * Pairing Functors and Pointwise Products

    Product-valued diagrams use the existing product category. Pointwise
    products then use the chosen product bifunctor in the target category;
    no new universal-property proof is needed. *)

(** * 函子配对与逐点积

    积值图式使用已有的乘积范畴；逐点积随后使用目标范畴的选定积双函子，
    无需另证泛性质。 *)

(** The first projection keeps the first object and arrow components. *)

(** 第一投影保留对象及箭头的第一分量。 *)

Program Definition FstF (C : Cat) (D : Cat)
  : Functor (C ×C D) C
  :=
  {|F0 := fst
  ; F1 X Y := fst
  |}.
Next Obligation. intros [f g] [h k] [H K]. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** The second projection keeps the second components. *)

(** 第二投影保留第二分量。 *)

Program Definition SndF (C : Cat) (D : Cat)
  : Functor (C ×C D) D
  :=
  {|F0 := snd
  ; F1 X Y := snd
  |}.
Next Obligation. intros [f g] [h k] [H K]. exact K. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Pair two diagrams with a common source, retaining both arrow maps. *)

(** 将同源图式配对，保留两个箭头映射。 *)

Program Definition PairF {J : Cat} {C : Cat} {D : Cat}
    (F : Functor J C) (G : Functor J D)
  : Functor J (C ×C D)
  :=
  {|F0 i := (F i, G i)
  ; F1 i j f := (fmap F f, fmap G f)
  |}.
Next Obligation.
  intros f g H. split; apply functor_fmap_proper; exact H.
Defined.
Next Obligation. split; apply functor_id. Defined.
Next Obligation. split; apply functor_comp. Defined.

(** ** Fixing the Second Product Coordinate

    For categories [A], [B], [C] and [K : Functor (A ×C B) C], fixing
    an object of [B] gives the existing restriction [π1F K b] on [A].
    An arrow of [B] then gives a natural transformation between these
    restrictions. This uses product
    categories, without choosing products inside any of the three categories. *)

(** ** 固定积的第二坐标

    给定范畴 [A]、[B]、[C] 及 [K : Functor (A ×C B) C]，固定 [B] 的一个
    对象就得到已有的限制函子 [π1F K b]；[B] 中的箭头随后给出这些限制之间
    的自然变换。
    此处使用积范畴，不在这三个范畴内选取积结构。 *)

Section ProductRestrictions.
Context {A B C : Cat} (K : Functor (A ×C B) C).

(** The second-coordinate arrow acts at every first-coordinate object. *)

(** 第二坐标的箭头在每个第一坐标对象处作用。 *)

Program Definition ProductAtN {b b' : @Ob B} (a : Hom b b')
  : π1F K b ⇒ π1F K b'
  :=
  {|nt x := fmap K (X := (x, b)) (Y := (x, b')) (id, a)
  |}.
Next Obligation.
  cbn. rewrite <- !functor_comp. apply functor_fmap_proper.
  split; carw.
Defined.

(** Equal parameter arrows induce pointwise equal transformations. *)

(** 相等的参数箭头诱导逐点相等的自然变换。 *)

Global Instance product_at_proper {b b' : @Ob B}
  : Proper (@HomEq B b b' ==> NatEq) (@ProductAtN b b').
Proof.
  intros a a' H x. cbn. apply functor_fmap_proper.
  split; [reflexivity | exact H].
Defined.

(** An identity parameter arrow gives the identity transformation. *)

(** 恒等参数箭头给出恒等自然变换。 *)

Lemma product_at_id (b : @Ob B)
  : ProductAtN (@Cat.Core.id B b) ≈N idN.
Proof. intros x. exact (@functor_id _ _ K (x, b)). Defined.

(** Composition in the parameter becomes vertical composition. *)

(** 参数中的复合变成自然变换的垂直复合。 *)

Lemma product_at_comp {b b' b'' : @Ob B}
    (a' : Hom b' b'') (a : Hom b b')
  : ProductAtN (a' ∘ a) ≈N (ProductAtN a' ∘Nv ProductAtN a).
Proof.
  intros x. cbn. rewrite <- functor_comp. apply functor_fmap_proper.
  split; cbn; carw; reflexivity.
Defined.

(** A product arrow first changes the parameter, then the first coordinate. *)

(** 积中的箭头可先改变参数，再改变第一坐标。 *)

Lemma product_at_map {x y : @Ob A} {b b' : @Ob B}
    (f : Hom x y) (a : Hom b b')
  : fmap K (X := (x, b)) (Y := (y, b')) (f, a) ≈
      fmap (π1F K b') f ∘ ProductAtN a x.
Proof.
  cbn. rewrite <- functor_comp. apply functor_fmap_proper.
  split; cbn; carw; reflexivity.
Defined.

End ProductRestrictions.

(** Restrict a natural comparison to one parameter value. *)

(** 将自然比较限制在一个参数值。 *)

Program Definition ProductRestrictionN {A B C : Cat}
    {K L : Functor (A ×C B) C} (β : K ⇒ L) (b : @Ob B)
  : π1F K b ⇒ π1F L b
  :=
  {|nt x := β (x, b)
  |}.
Next Obligation.
  exact (nt_naturality β (X := (X, b)) (Y := (Y, b)) (f, id)).
Defined.

(** Restriction preserves the specified pointwise equality of comparisons. *)

(** 限制保持比较所指定的逐点相等。 *)

Global Instance product_restriction_proper {A B C : Cat}
    {K L : Functor (A ×C B) C} (b : @Ob B)
  : Proper (NatEq ==> NatEq) (λ β : K ⇒ L, ProductRestrictionN β b).
Proof. intros β γ H x. exact (H (x, b)). Defined.

(** A natural comparison of product functors intertwines their parameter
    transformations. All four sides have their original, possibly different
    object maps; the equation compares transformations with fixed endpoints. *)

(** 积函子之间的自然比较与其参数自然变换相容。四条边沿用原有且可能不同的
    对象映射；方程比较固定两端之间的自然变换。 *)

Lemma product_at_natural {A B C : Cat}
    {K L : Functor (A ×C B) C} (β : K ⇒ L)
    {b b' : @Ob B} (a : Hom b b')
  : (ProductRestrictionN β b' ∘Nv ProductAtN K a) ≈N
      (ProductAtN L a ∘Nv ProductRestrictionN β b).
Proof.
  intros x. exact (nt_naturality β (X := (x, b)) (Y := (x, b')) (id, a)).
Defined.

(** Repackage a product-labelled induced category as a product of induced
    categories. The object and arrow maps are identities; category law
    fields need not be natively equal. *)

(** 将带积标签的诱导范畴重新包装为诱导范畴的积。对象及箭头映射均为恒等，
    不要求范畴定律字段原生相等。 *)

Program Definition InducedProductF {C : Cat} {D : Cat} (X : Type) (Y : Type)
    (j : X → @Ob C) (k : Y → @Ob D)
  : Functor (InducedCat (C := C ×C D) (X * Y)
      (λ xy, (j (fst xy), k (snd xy))))
      (InducedCat X j ×C InducedCat Y k)
  :=
  {|F0 xy := xy
  ; F1 x y f := f
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. split; reflexivity. Defined.
Next Obligation. split; reflexivity. Defined.

(** The reverse repackaging retains the same computational data. *)

(** 反向重新包装保留相同的计算数据。 *)

Program Definition InducedProductInvF {C : Cat} {D : Cat} (X : Type) (Y : Type)
    (j : X → @Ob C) (k : Y → @Ob D)
  : Functor (InducedCat X j ×C InducedCat Y k)
      (InducedCat (C := C ×C D) (X * Y)
        (λ xy, (j (fst xy), k (snd xy))))
  :=
  {|F0 xy := xy
  ; F1 x y f := f
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. split; reflexivity. Defined.
Next Obligation. split; reflexivity. Defined.

(** Pointwise products reuse the chosen product bifunctor of the target. *)

(** 逐点积复用目标范畴的选定积双函子。 *)

Definition PointwiseProductF {J : Cat} {C : Cat} `{HP : !HasProduct C}
    (F G : Functor J C)
  : Functor J C
  := ProductF ∘F PairF F G.

(** Component maps induce a map of pointwise products. *)

(** 分量映射诱导逐点积之间的映射。 *)

Program Definition PointwiseProductN {J : Cat} {C : Cat} `{HP : !HasProduct C}
    {F F' G G' : Functor J C} (α : F ⇒ F') (β : G ⇒ G')
  : PointwiseProductF F G ⇒ PointwiseProductF F' G'
  :=
  {|nt i := α i × β i
  |}.
Next Obligation.
  change ((α Y × β Y) ∘ (fmap F f × fmap G f) ≈
    (fmap F' f × fmap G' f) ∘ (α X × β X)).
  rewrite <- !cross_comp, !nt_naturality. reflexivity.
Defined.
