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

Program Definition π1F (C : Cat) (D : Cat)
  : Fct (C ×C D) C
  :=
  {|fobj := fst
  ; fmap X Y := fst
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros [f g] [h k] [H K]. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** The second projection keeps the second components. *)

(** 第二投影保留第二分量。 *)

Program Definition π2F (C : Cat) (D : Cat)
  : Fct (C ×C D) D
  :=
  {|fobj := snd
  ; fmap X Y := snd
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros [f g] [h k] [H K]. exact K. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** Pair two diagrams with a common source, retaining both arrow maps. *)

(** 将同源图式配对，保留两个箭头映射。 *)

Program Definition PairF {J : Cat} {C : Cat} {D : Cat}
    (F : Fct J C) (G : Fct J D)
  : Fct J (C ×C D)
  :=
  {|fobj i := (F i, G i)
  ; fmap i j f := (fmap F f, fmap G f)
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros f g H. split; apply fmap_proper; exact H.
Qed.
Next Obligation. split; apply fmap_id. Qed.
Next Obligation. split; apply fmap_comp. Qed.

(** ** Fixing the Second Product Coordinate

    For categories [A], [B], [C] and [K : Fct (A ×C B) C], fixing
    an object of [B] gives the existing restriction [AtRF K b] on [A].
    An arrow of [B] then gives a natural transformation between these
    restrictions. This uses product
    categories, without choosing products inside any of the three categories. *)

(** ** 固定积的第二坐标

    给定范畴 [A]、[B]、[C] 及 [K : Fct (A ×C B) C]，固定 [B] 的一个
    对象就得到已有的限制函子 [AtRF K b]；[B] 中的箭头随后给出这些限制之间
    的自然变换。
    此处使用积范畴，不在这三个范畴内选取积结构。 *)

Section ProductRestrictions.
Context {A B C : Cat} (K : Fct (A ×C B) C).

(** The second-coordinate arrow acts at every first-coordinate object. *)

(** 第二坐标的箭头在每个第一坐标对象处作用。 *)

Program Definition ProductAtN {b b' : B} (a : Hom b b')
  : AtRF K b ⇒ AtRF K b'
  :=
  {|nt x := fmap K (X := (x, b)) (Y := (x, b')) (id, a)
  |}.
Next Obligation.
  cbn. rewrite <- !fmap_comp. apply fmap_proper.
  split; carw.
Qed.

(** Equal parameter arrows induce pointwise equal transformations. *)

(** 相等的参数箭头诱导逐点相等的自然变换。 *)

Global Instance product_at_proper {b b' : @Ob B}
  : Proper (@HomEq B b b' ==> NatEq) (@ProductAtN b b').
Proof.
  intros a a' H x. cbn. apply fmap_proper.
  split; [reflexivity | exact H].
Defined.

(** An identity parameter arrow gives the identity transformation. *)

(** 恒等参数箭头给出恒等自然变换。 *)

Lemma product_at_id (b : @Ob B)
  : ProductAtN (@Cat.Core.id B b) ≈N IdN.
Proof. intros x. exact (@fmap_id _ _ _ _ (isFct K) (x, b)). Defined.

(** Composition in the parameter becomes vertical composition. *)

(** 参数中的复合变成自然变换的垂直复合。 *)

Lemma product_at_comp {b b' b'' : B}
    (a' : Hom b' b'') (a : Hom b b')
  : ProductAtN (a' ∘ a)
    ≈N (ProductAtN a' ∘Nv ProductAtN a).
Proof.
  intros x. cbn. rewrite <- fmap_comp.
  apply fmap_proper.
  split; cbn; carw; reflexivity.
Defined.

(** A product arrow first changes the parameter, then the first coordinate. *)

(** 积中的箭头可先改变参数，再改变第一坐标。 *)

Lemma product_at_map {x y : A} {b b' : B}
    (f : Hom x y) (a : Hom b b')
  : fmap K (X := (x, b)) (Y := (y, b')) (f, a)
    ≈ fmap (AtRF K b') f ∘ ProductAtN a x.
Proof.
  cbn. rewrite <- fmap_comp. apply fmap_proper.
  split; cbn; carw; reflexivity.
Defined.

End ProductRestrictions.

(** Changing the first coordinate gives the other parameter transformation.
    Reuse second-coordinate naturality through the explicit flipped diagram. *)

(** 改变第一坐标给出另一参数自然变换；通过显式翻转图式，复用第二坐标自然性。 *)

Program Definition ProductFirstAtN {A B C : Cat}
    (K : Fct (A ×C B) C) {a a' : A} (f : Hom a a')
  : AtLF K a ⇒ AtLF K a'
  :=
  {|nt b := fmap K (X := (a,b)) (Y := (a',b)) (f,id)
  |}.
Next Obligation.
  exact (nat_naturality
    (ProductAtN (K ∘F PairF (π2F B A) (π1F B A)) f) f0).
Qed.

(** Restrict a natural comparison to one parameter value. *)

(** 将自然比较限制在一个参数值。 *)

Program Definition ProductRestrictionN {A B C : Cat}
    {K L : Fct (A ×C B) C} (β : K ⇒ L) (b : @Ob B)
  : AtRF K b ⇒ AtRF L b
  :=
  {|nt x := β (x, b)
  |}.
Next Obligation.
  exact (nat_naturality β (X := (X, b)) (Y := (Y, b)) (f, id)).
Qed.

(** Restriction preserves the specified pointwise equality of comparisons. *)

(** 限制保持比较所指定的逐点相等。 *)

Global Instance product_restriction_proper {A B C : Cat}
    {K L : Fct (A ×C B) C} (b : B)
  : Proper (NatEq ==> NatEq)
    (λ β : K ⇒ L, ProductRestrictionN β b).
Proof. intros β γ H x. exact (H (x, b)). Defined.

(** A natural comparison of product functors intertwines their parameter
    transformations. All four sides have their original, possibly different
    object maps; the equation compares transformations with fixed endpoints. *)

(** 积函子之间的自然比较与其参数自然变换相容。四条边沿用原有且可能不同的
    对象映射；方程比较固定两端之间的自然变换。 *)

Lemma product_at_natural {A B C : Cat}
    {K L : Fct (A ×C B) C} (β : K ⇒ L)
    {b b' : B} (a : Hom b b')
  : (ProductRestrictionN β b' ∘Nv ProductAtN K a) ≈N
      (ProductAtN L a ∘Nv ProductRestrictionN β b).
Proof.
  intros x. exact (nat_naturality β (X := (x, b)) (Y := (x, b')) (id, a)).
Defined.

(** Repackage a product-labelled induced category as a product of induced
    categories. The object and arrow maps are identities; category law
    fields need not be natively equal. *)

(** 将带积标签的诱导范畴重新包装为诱导范畴的积。对象及箭头映射均为恒等，
    不要求范畴定律字段原生相等。 *)

Program Definition InducedProductF
    {C : Cat} {D : Cat} (X : Type) (Y : Type)
    (j : X → C) (k : Y → D)
  : Fct (InducedCat (C := C ×C D) (X * Y)
        (λ xy, (j (fst xy), k (snd xy))))
      (InducedCat X j ×C InducedCat Y k)
  :=
  {|fobj xy := xy
  ; fmap x y f := f
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. split; reflexivity. Qed.
Next Obligation. split; reflexivity. Qed.

(** The reverse repackaging retains the same computational data. *)

(** 反向重新包装保留相同的计算数据。 *)

Program Definition InducedProductInvF
    {C : Cat} {D : Cat} (X : Type) (Y : Type)
    (j : X → C) (k : Y → D)
  : Fct (InducedCat X j ×C InducedCat Y k)
      (InducedCat (C := C ×C D) (X * Y)
        (λ xy, (j (fst xy), k (snd xy))))
  :=
  {|fobj xy := xy
  ; fmap x y f := f
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. split; reflexivity. Qed.
Next Obligation. split; reflexivity. Qed.

(** Pointwise products reuse the chosen product bifunctor of the target. *)

(** 逐点积复用目标范畴的选定积双函子。 *)

Definition PointwiseProductF {J : Cat} {C : Cat}
    `{HP : !HasProduct C} (F G : Fct J C)
  : Fct J C
  := ProductF ∘F PairF F G.

(** Component maps induce a map of pointwise products. *)

(** 分量映射诱导逐点积之间的映射。 *)

Program Definition PointwiseProductN {J : Cat} {C : Cat}
    `{HP : !HasProduct C} {F F' G G' : Fct J C}
    (α : F ⇒ F') (β : G ⇒ G')
  : PointwiseProductF F G ⇒ PointwiseProductF F' G'
  :=
  {|nt i := α i × β i
  |}.
Next Obligation.
  change ((α Y × β Y) ∘ (fmap F f × fmap G f) ≈
    (fmap F' f × fmap G' f) ∘ (α X × β X)).
  rewrite <- !cross_comp, !nat_naturality. reflexivity.
Qed.

(** ** Natural Comparisons of Product-Valued Functors

    Projection comparisons determine a comparison into a product category.
    Retain each supplied component and inverse without identifying objects
    or functor records by native equality. *)

(** ** 积值函子的自然比较

    投影上的比较决定到乘积范畴的比较。保留给定分量及逆，
    不以原生相等识别对象或函子记录。 *)

(** Pair the two prescribed natural-isomorphism components. *)

(** 配对两份指定自然同构的分量。 *)

Program Definition ProdNatIso {J C D : Cat}
    {H K : Fct J (C ×C D)}
    (α : (π1F C D ∘F H) ≅N (π1F C D ∘F K))
    (β : (π2F C D ∘F H) ≅N (π2F C D ∘F K))
  : H ≅N K
  := ({|nt X := (α.1 X, β.1 X)
       |}; λ X, (((α.2 X).1, (β.2 X).1); _)).
Next Obligation.
  split; [exact (nat_naturality α.1 f) | exact (nat_naturality β.1 f)].
Qed.
Next Obligation.
  split; split;
    [exact (fst (α.2 _).2) | exact (fst (β.2 _).2) |
      exact (snd (α.2 _).2) | exact (snd (β.2 _).2)].
Qed.

(** The first projection of a paired functor recovers its first factor. *)

(** 配对函子的第一投影恢复其第一因子。 *)

Program Definition FstPairIso {J C D : Cat}
    (F : Fct J C) (G : Fct J D)
  : (π1F C D ∘F PairF F G) ≅N F
  := ({|nt X := id
       |}; _).
Next Obligation. cbn. carw. Qed.
Next Obligation.
  intro X. exists id.
  split; apply comp_id_l.
Defined.

(** The second projection recovers the second factor. *)

(** 第二投影恢复第二因子。 *)

Program Definition SndPairIso {J C D : Cat}
    (F : Fct J C) (G : Fct J D)
  : (π2F C D ∘F PairF F G) ≅N G
  := ({|nt X := id
       |}; _).
Next Obligation. cbn. carw. Qed.
Next Obligation.
  intro X. exists id.
  split; apply comp_id_l.
Defined.
