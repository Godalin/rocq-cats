From Cats Require Export
  Cat.Isomorphism.

(** * Groupoids

    A groupoid is an existing category in which every arrow has an inverse.
    The inverse laws use the specified hom-setoid equality. All further
    coherence follows from inverse uniqueness. [IsGpd] supplies witnesses
    on a fixed category; [Gpd] bundles that category with those witnesses. *)

(** * 群胚

    群胚是每条箭头均有逆的已有范畴。互逆定律使用 Hom 广集指定的相等；其余
    相干性由逆的唯一性导出。[IsGpd] 为固定范畴提供见证；[Gpd] 将该范畴
    与这些见证打包。 *)

Class IsGpd (C : Cat)
  :=
  { gpd_iso {X Y : @Ob C} (f : Hom X Y)
      : is_iso f
  }.

(** A complete groupoid owns one category. Its inherited inverse witnesses
    use that category's hom equality and remain computational data in [Type].
    The unique underlying chain is [Gpd] to [Cat] to the object type. *)

(** 完整群胚保存唯一底层范畴。继承的逆见证使用该范畴的 Hom 相等，并保持为
    [Type] 中的计算数据。唯一底层转换链由 [Gpd] 经 [Cat] 到对象类型。 *)

Record Gpd
  := GpdOfCat

  (** The only category view stores the category once. *)

  (** 唯一范畴视图只保存一次底层范畴。 *)

  { GpdToCat :> Cat

  (** Reuse the property interface on precisely that category. *)

  (** 在恰好该底层范畴上复用性质接口。 *)

  ; isGpd :: IsGpd GpdToCat

  }.

(** The constructor takes the underlying category and its inverse witnesses
    explicitly, preserving exactly the supplied computational choices. *)

(** 构造器显式接受底层范畴及其逆见证，恰好保留给定的计算选择。 *)

Arguments GpdOfCat _ _ : clear implicits.

Notation "C '⦂' 'Gpd'" := (IsGpd C)
  (at level 50, no associativity) : type_scope.

(** ** Inverse Arrows in a Groupoid

    Assume [C] is a groupoid. Extract each arrow's inverse and prove
    uniqueness, respectfulness and compatibility with identity and
    composition. *)

(** ** 群胚中的逆箭头

    假定 [C] 为群胚，提取每条箭头的逆，并证明唯一性、保相等性及与恒等和复合的相容性。 *)

Section Groupoid.
Context {C : Cat} `{HC : !IsGpd C}.

(** The computational inverse selected by the groupoid structure. *)

(** 群胚结构选取的可计算逆。 *)

Definition gpd_inv {X Y : @Ob C} (f : Hom X Y)
  : Hom Y X
  := (gpd_iso f).1.

Notation "f '⁻¹'" := (gpd_inv f)
  (at level 9) : hom_scope.

(** Left inverse equation in the hom-setoid. *)

(** Hom 广集中的左逆方程。 *)

Lemma gpd_inv_l {X Y : @Ob C} (f : Hom X Y)
  : f⁻¹ ∘ f ≈ id.
Proof. exact (fst (gpd_iso f).2). Qed.

(** Right inverse equation in the hom-setoid. *)

(** Hom 广集中的右逆方程。 *)

Lemma gpd_inv_r {X Y : @Ob C} (f : Hom X Y)
  : f ∘ f⁻¹ ≈ id.
Proof. exact (snd (gpd_iso f).2). Qed.

(** Any left inverse agrees with the selected inverse. *)

(** 任意左逆都与选定逆相等。 *)

Lemma gpd_inv_unique {X Y : @Ob C} (f : Hom X Y) (g : Hom Y X)
    (H : g ∘ f ≈ id)
  : g ≈ f⁻¹.
Proof. exact (inverse_unique f g f⁻¹ H (gpd_inv_r f)). Qed.

(** Inversion respects the specified equality of arrows. *)

(** 取逆保持箭头指定的相等。 *)

Global Instance gpd_inv_proper {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> @HomEq[Y, X]) (@gpd_inv X Y).
Proof.
  intros f g H. apply gpd_inv_unique.
  rewrite <- H. apply gpd_inv_l.
Qed.

(** The inverse of an identity is the identity. *)

(** 恒等箭头的逆仍是恒等箭头。 *)

Lemma gpd_inv_id {X : @Ob C}
  : (@id X)⁻¹ ≈ id.
Proof. symmetry. apply gpd_inv_unique. apply comp_id_l. Qed.

(** Inversion is involutive up to the specified equality. *)

(** 连续取逆两次在指定相等下恢复原箭头。 *)

Lemma gpd_inv_inv {X Y : @Ob C} (f : Hom X Y)
  : (f⁻¹)⁻¹ ≈ f.
Proof. symmetry. apply gpd_inv_unique. apply gpd_inv_r. Qed.

(** Inverting a composite reverses the order of its factors. *)

(** 复合的逆反转两个因子的次序。 *)

Lemma gpd_inv_comp {X Y Z : @Ob C} (g : Hom Y Z) (f : Hom X Y)
  : (g ∘ f)⁻¹ ≈ f⁻¹ ∘ g⁻¹.
Proof.
  symmetry. apply gpd_inv_unique.
  rewrite comp_assoc, <- (comp_assoc g⁻¹), gpd_inv_l, comp_id_l.
  apply gpd_inv_l.
Qed.

(** Inversion is a respectful map between the two hom-setoids. *)

(** 取逆是正向与反向 Hom 广集之间的保相等映射。 *)

Program Definition gpd_inv_resp (X Y : @Ob C)
  : HomSet X Y →r HomSet Y X
  :=
  {|func f := f⁻¹
  |}.

(** Each arrow gives an isomorphism of its endpoints. *)

(** 每条箭头给出其端点之间的同构。 *)

Definition gpd_arrow_iso {X Y : @Ob C} (f : Hom X Y)
  : X ≅ Y
  := (f; gpd_iso f).

End Groupoid.

Notation "f '⁻¹'" := (gpd_inv f)
  (at level 9) : hom_scope.

(** Opposite categories inherit the same inverses with swapped inverse laws.
    Enable this structure explicitly when working in the opposite. *)

(** 反范畴继承相同的逆并交换两条互逆定律；在反范畴中使用时显式启用此结构。 *)

Program Definition op_IsGpd (C : Cat) `{HC : !IsGpd C}
  : C^op ⦂ Gpd
  :=
  {|gpd_iso X Y f :=
      (@gpd_inv C HC Y X f; _)
  |}.
Next Obligation.
  split.
  - exact (@gpd_inv_r C HC Y X f).
  - exact (@gpd_inv_l C HC Y X f).
Defined.

(** Products of groupoids have componentwise inverses. *)

(** 群胚的乘积逐分量取逆。 *)

Program Definition ProdCat_IsGpd (C D : Cat)
    `{HC : !IsGpd C} `{HD : !IsGpd D}
  : (C ×C D) ⦂ Gpd
  :=
  {|gpd_iso X Y f := (((fst f)⁻¹, (snd f)⁻¹); _)
  |}.
Next Obligation.
  split; split; cbn; [apply gpd_inv_l | apply gpd_inv_l |
    apply gpd_inv_r | apply gpd_inv_r].
Defined.

(** The opposite groupoid reuses the opposite-category construction and
    swaps the original inverse laws; it does not rebuild the dual theory. *)

(** 反群胚复用反范畴构造并交换原有互逆定律，不另建对偶理论。 *)

Definition OpGpd (G : Gpd)
  : Gpd
  := GpdOfCat (G^op) (@op_IsGpd G (@isGpd G)).

(** The product groupoid inherits the componentwise inverses on the same
    product category. *)

(** 乘积群胚在同一乘积范畴上继承逐分量的逆。 *)

Definition ProdGpd (G H : Gpd)
  : Gpd
  := GpdOfCat (G ×C H)
      (@ProdCat_IsGpd G H (@isGpd G) (@isGpd H)).
