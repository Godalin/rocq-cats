From Cats Require Export
  Cat.Isomorphism.

(** * Groupoids

    A groupoid is an existing category in which every arrow has an inverse.
    The inverse laws use the specified hom-setoid equality. All further
    coherence follows from inverse uniqueness; no new category is bundled. *)

(** * 群胚

    群胚是每条箭头均有逆的已有范畴。互逆定律使用 Hom 广集指定的相等；其余
    相干性由逆的唯一性导出，不重新组合一个范畴。 *)

Class IsGroupoid (C : Cat)
  :=
  { groupoid_iso {X Y : @Ob C} (f : Hom X Y) : is_iso f }.

Notation "C '⦂' 'Gpd'" := (IsGroupoid C)
  (at level 50, no associativity) : type_scope.

Section Groupoid.
Context {C : Cat} `{HC : !IsGroupoid C}.

(** The computational inverse selected by the groupoid structure. *)

(** 群胚结构选取的可计算逆。 *)

Definition groupoid_inv {X Y : @Ob C} (f : Hom X Y)
  : Hom Y X
  := (groupoid_iso f).1.

Notation "f '⁻¹'" := (groupoid_inv f)
  (at level 9) : hom_scope.

(** Left inverse equation in the hom-setoid. *)

(** Hom 广集中的左逆方程。 *)

Lemma groupoid_inv_l {X Y : @Ob C} (f : Hom X Y)
  : f⁻¹ ∘ f ≈ id.
Proof. exact (fst (groupoid_iso f).2). Qed.

(** Right inverse equation in the hom-setoid. *)

(** Hom 广集中的右逆方程。 *)

Lemma groupoid_inv_r {X Y : @Ob C} (f : Hom X Y)
  : f ∘ f⁻¹ ≈ id.
Proof. exact (snd (groupoid_iso f).2). Qed.

(** Any left inverse agrees with the selected inverse. *)

(** 任意左逆都与选定逆相等。 *)

Lemma groupoid_inv_unique {X Y : @Ob C} (f : Hom X Y) (g : Hom Y X)
    (H : g ∘ f ≈ id)
  : g ≈ f⁻¹.
Proof. exact (inverse_unique f g f⁻¹ H (groupoid_inv_r f)). Qed.

(** Inversion respects the specified equality of arrows. *)

(** 取逆保持箭头指定的相等。 *)

Global Instance groupoid_inv_proper {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> @HomEq[Y, X]) (@groupoid_inv X Y).
Proof.
  intros f g H. apply groupoid_inv_unique.
  rewrite <- H. apply groupoid_inv_l.
Qed.

(** The inverse of an identity is the identity. *)

(** 恒等箭头的逆仍是恒等箭头。 *)

Lemma groupoid_inv_id {X : @Ob C}
  : (@id X)⁻¹ ≈ id.
Proof. symmetry. apply groupoid_inv_unique. apply comp_id_l. Qed.

(** Inversion is involutive up to the specified equality. *)

(** 连续取逆两次在指定相等下恢复原箭头。 *)

Lemma groupoid_inv_inv {X Y : @Ob C} (f : Hom X Y)
  : (f⁻¹)⁻¹ ≈ f.
Proof. symmetry. apply groupoid_inv_unique. apply groupoid_inv_r. Qed.

(** Inverting a composite reverses the order of its factors. *)

(** 复合的逆反转两个因子的次序。 *)

Lemma groupoid_inv_comp {X Y Z : @Ob C} (g : Hom Y Z) (f : Hom X Y)
  : (g ∘ f)⁻¹ ≈ f⁻¹ ∘ g⁻¹.
Proof.
  symmetry. apply groupoid_inv_unique.
  rewrite comp_assoc, <- (comp_assoc g⁻¹), groupoid_inv_l, comp_id_l.
  apply groupoid_inv_l.
Qed.

(** Inversion is a respectful map between the two hom-setoids. *)

(** 取逆是正向与反向 Hom 广集之间的保相等映射。 *)

Program Definition groupoid_inv_resp (X Y : @Ob C)
  : HomSet X Y →r HomSet Y X
  :=
  {|func f := f⁻¹
  |}.

(** Each arrow gives an isomorphism of its endpoints. *)

(** 每条箭头给出其端点之间的同构。 *)

Definition groupoid_arrow_iso {X Y : @Ob C} (f : Hom X Y)
  : X ≅ Y
  := (f; groupoid_iso f).

End Groupoid.

Notation "f '⁻¹'" := (groupoid_inv f)
  (at level 9) : hom_scope.

(** Opposite categories inherit the same inverses with swapped inverse laws.
    Enable this structure explicitly when working in the opposite. *)

(** 反范畴继承相同的逆并交换两条互逆定律；在反范畴中使用时显式启用此结构。 *)

Program Definition op_IsGroupoid (C : Cat) `{HC : !IsGroupoid C}
  : C^op ⦂ Gpd
  :=
  {|groupoid_iso X Y f :=
      (@groupoid_inv C HC Y X f; _)
  |}.
Next Obligation.
  split.
  - exact (@groupoid_inv_r C HC Y X f).
  - exact (@groupoid_inv_l C HC Y X f).
Defined.

(** Products of groupoids have componentwise inverses. *)

(** 群胚的乘积逐分量取逆。 *)

Program Definition ProdCat_IsGroupoid (C D : Cat)
    `{HC : !IsGroupoid C} `{HD : !IsGroupoid D}
  : (C ×C D) ⦂ Gpd
  :=
  {|groupoid_iso X Y f := (((fst f)⁻¹, (snd f)⁻¹); _)
  |}.
Next Obligation.
  split; split; cbn; [apply groupoid_inv_l | apply groupoid_inv_l |
    apply groupoid_inv_r | apply groupoid_inv_r].
Defined.
