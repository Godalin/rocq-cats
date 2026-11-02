From Cats.Set Require Export Morphism.

Declare Scope ob_scope.
Delimit Scope ob_scope with ob.
Open Scope ob_scope.

Declare Scope hom_scope.
Delimit Scope hom_scope with hom.
Open Scope hom_scope.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Open Scope cat_scope.



(** * Category *)

(** * 范畴 *)

(** Morphisms and their equivalence witnesses have independent sizes.
    Equivalence/properness laws may live in larger auxiliary universes. *)

(** 态射与其相等见证的大小独立；等价律和相容性定律可以位于更大的辅助宇宙。 *)

Class Cat@{o h p +}
  :=
  { Ob : Type@{o}
  ; HomSet : Ob → Ob → SetC@{h p}
  ; Hom (X Y : Ob) : Type@{h} := carrier (HomSet X Y)
  ; HomEq {X Y} : Hom X Y → Hom X Y → Type@{p}
  := carrier_equiv (HomSet X Y)

  ; id {X} : Hom X X

  ; comp {X Y Z} : Hom Y Z → Hom X Y → Hom X Z

  ; comp_proper {X Y Z}
    :: Proper (@HomEq Y Z ==> @HomEq X Y ==> @HomEq X Z) comp

  ; comp_id_r {X Y : Ob} (f : Hom X Y)
    : HomEq (comp f id) f

  ; comp_id_l {X Y : Ob} (f : Hom X Y)
    : HomEq (comp id f) f

  ; comp_assoc {X Y Z W}
      (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y)
    : HomEq (comp (comp f g) h) (comp f (comp g h))
  }.

(** Equality and its laws come from the hom-set, not from an independent
    relation field. [Hom] and [HomEq] are computed fields, so they retain the
    existing coercion interfaces without adding constructor arguments. *)

(** 相等及其定律来自 Hom 广集，不另设关系字段。[Hom] 与 [HomEq] 是计算字段，保
    留已有强制转换接口而不增加构造参数。 *)

Global Instance HomEq_Equivalence {C : Cat} {X Y : @Ob C}
  : Equivalence (@HomEq C X Y)
  := carrier_setoid (HomSet X Y).

(** The specified hom-setoid between two objects. *)

(** 两个对象间指定的 Hom 广集。 *)

Definition Hom_SetC {C : Cat} {X Y : @Ob C}
  : SetC
  := HomSet X Y.

Arguments HomEq {_ _%_ob _%_ob} _%_hom _%_hom.
Arguments comp_id_l {_ _ _} _.
Arguments comp_id_r {_ _ _} _.
Arguments comp_assoc {_ _ _ _ _} _ _ _.

Bind Scope ob_scope with Ob.
Bind Scope hom_scope with Hom.

Notation "'@Ob' C" := (@Ob C)
  (at level 35) : cat_scope.

Notation "'@Hom' C" := (@Hom C)
  (at level 35) : cat_scope.

Notation "'@HomEq[' X ',' Y  ']'" := (@HomEq _ X Y) : cat_scope.

Infix "≈" := HomEq
  (at level 50, no associativity) : cat_scope.

Notation "f '≈' g '⦂' 'Hom(' X ',' Y ')'" := (@HomEq _ X Y f g)
  (at level 50, no associativity, only printing,
    format "f  '≈'  g  '⦂'  'Hom(' X  ','  Y )") : cat_scope.

Notation "f '≉' g" := (¬ HomEq f g)
  (at level 50, no associativity) : cat_scope.

Notation "f '≉' g '⦂' 'Hom(' X ',' Y ')'" := (¬ @HomEq _ X Y f g)
  (at level 50, no associativity, only printing,
    format "f  '≉'  g  '⦂'  'Hom(' X  ','  Y )") : cat_scope.

Notation "'@id' X" := (@id _ X)
  (at level 35) : hom_scope.

Notation "f '∘' g" := (comp f g)
  (at level 40, left associativity) : hom_scope.

(** Category auto & eauto *)

(** 用于范畴目标的自动搜索策略。 *)

Ltac cato := auto with cat; try reflexivity.
Ltac cate := eauto with cat; try reflexivity.

(** Category auto rewriting, eagerly simplifies the goal (with β rules and
    simple η rules) *)

(** 范畴自动重写策略，主动化简目标，使用 β 律及简单 η 律。 *)

Ltac carw := autorewrite with cat using try reflexivity.

(** Category association rewriting *)

(** 调整复合结合方向的范畴重写策略。 *)

Ltac rw_assoc_r args := rewrite (comp_assoc args); cato.
Ltac rw_assoc_l args := rewrite <- (comp_assoc args); cato.

Tactic Notation "cacr" := rewrite comp_assoc; cato.
Tactic Notation "cacr" constr(t) := rw_assoc_r t.
Tactic Notation "cacl" := rewrite <- comp_assoc; cato.
Tactic Notation "cacl" constr(t) := rw_assoc_l t.

Hint Resolve comp_id_l : cat.
Hint Resolve comp_id_r : cat.

Hint Rewrite @comp_id_l : cat.
Hint Rewrite @comp_id_r : cat.



Section CatBasic.
Context {C : Cat} {X Y : Ob}.

(** Reverse the left identity equation. *)

(** 反向使用左单位方程。 *)

Theorem symm_id_l {x : Hom X Y}
  : x ≈ id ∘ x.
Proof. symmetry. cato. Qed.

(** Reverse the right identity equation. *)

(** 反向使用右单位方程。 *)

Theorem symm_id_r {x : Hom X Y}
  : x ≈ x ∘ id.
Proof. symmetry. cato. Qed.

End CatBasic.

Hint Resolve symm_id_l : cat.
Hint Resolve symm_id_r : cat.



(** ** Morphisms induced by object equality

    These are transported identities. Their laws use equality elimination,
    without identifying distinct equality witnesses. *)

(** ** 由对象原生相等诱导的态射

    这些态射是运输后的恒等态射；定律通过相等消去证明，不要求不同相等见证一致。 *)

Definition eq_to_hom {C : Cat} {X Y : @Ob C} (p : X = Y)
  : Hom X Y
  := match p with eq_refl => id end.

(** Compatibility with composition for [eq_to_hom]. *)

(** [eq_to_hom] 与复合的相容性。 *)

Lemma eq_to_hom_comp {C : Cat} {X Y Z : @Ob C} (p : X = Y) (q : Y = Z)
  : eq_to_hom (eq_trans p q) ≈ eq_to_hom q ∘ eq_to_hom p.
Proof. destruct p, q. simpl. symmetry. apply comp_id_l. Qed.

(** Transported identities along opposite native equalities cancel on the
    left. *)

(** 沿反向原生相等运输的恒等态射在左侧抵消。 *)

Lemma eq_to_hom_inv_l {C : Cat} {X Y : @Ob C} (p : X = Y)
  : eq_to_hom (eq_sym p) ∘ eq_to_hom p ≈ id.
Proof. destruct p. simpl. apply comp_id_l. Qed.

(** Transported identities along opposite native equalities cancel on the
    right. *)

(** 沿反向原生相等运输的恒等态射在右侧抵消。 *)

Lemma eq_to_hom_inv_r {C : Cat} {X Y : @Ob C} (p : X = Y)
  : eq_to_hom p ∘ eq_to_hom (eq_sym p) ≈ id.
Proof. destruct p. simpl. apply comp_id_l. Qed.



(** Precompose a morphism with a fixed arrow. *)

(** 将态射与固定箭头预合成。 *)

Definition comp_pre `{C : Cat} {X Y Z : Ob} (f : Hom X Y)
  := (λ g : Hom Y Z, g ∘ f).

(** Postcompose a morphism with a fixed arrow. *)

(** 将态射与固定箭头后合成。 *)

Definition comp_post `{C : Cat} {X Y Z : Ob} (f : Hom Y Z)
  := (λ g : Hom X Y, f ∘ g).

Arguments comp_pre {_ _ _ _} _ _ /.
Arguments comp_post {_ _ _ _} _ _ /.

Notation "f ^*" := (comp_pre f) (at level 35).
Notation "f _*" := (comp_post f) (at level 35).

(** Composition acts respectfully on either hom-set. *)

(** 固定任一侧的复合都是 Hom 广集之间的保相等映射。 *)

Program Canonical comp_l_resp {C : Cat} {X Y Z : Ob}
    {f : Hom Y Z}
  : HomSet X Y →r HomSet X Z
  :=
  {|func := f _*
  |}.

(** Precomposition as a respectful map of hom-setoids. *)

(** 预合成作为 Hom 广集间的保相等映射。 *)

Program Canonical comp_r_resp {C : Cat} {X Y Z : Ob}
    {f : Hom X Y}
  : HomSet Y Z →r HomSet X Z
  :=
  {|func := f ^*
  |}.
Next Obligation.
  intros g1 g2 Hg. unfold comp_pre. rewrite Hg. reflexivity.
Qed.



(** ** Dual Category *)

(** ** 对偶范畴 *)

(** Reverse homs and composition to form the opposite category. *)

(** 反转 Hom 与复合，构造反范畴。 *)

Program Definition op (C : Cat)
  : Cat
  :=
  {|Ob := Ob
  ; HomSet X Y := HomSet Y X
  ; id _ := id
  ; comp _ _ _ f g := comp g f
  |}.
Next Obligation.
  intros x x' Hx y y' Hy.
  rewrite Hx, Hy.
  reflexivity.
Qed.
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_id_r. Qed.
Next Obligation.
  symmetry. apply comp_assoc.
Qed.

Notation "C '^op'" := (op C)
  (at level 60).

(** View an object in the opposite category. *)

(** 将对象视为反范畴中的对象。 *)

Definition ob_op {C : Cat} (X : @Ob C)
  : (@Ob (C ^op))
  := X.

(** Transport in the opposite category uses the reversed object equality. *)

(** 反范畴中的运输使用反向对象相等。 *)

Lemma eq_to_hom_op {C : Cat} {X Y : @Ob C} (p : X = Y)
  : @eq_to_hom (C ^op) X Y p ≈ eq_to_hom (eq_sym p).
Proof. destruct p. reflexivity. Qed.



(** ** Prod Category *)

(** ** 乘积范畴 *)

(** The componentwise product of two categories. *)

(** 两个范畴的逐分量乘积。 *)

Program Definition ProdCat (C D : Cat)
  : Cat
  :=
  {|Ob := @Ob C * @Ob D
  ; HomSet X Y :=
      {|carrier := Hom (fst X) (fst Y) * Hom (snd X) (snd Y)
      ; carrier_equiv := ProdEq HomEq HomEq
      ; carrier_setoid := ProdEq_Equivalence _ _
      |}
  ; id _ := (id, id)
  ; comp _ _ _ f g := (fst f ∘ fst g, snd f ∘ snd g)
  |}.
Next Obligation. intros [fc fd] [gc gd] [H1c H1d].
  intros [hc hd] [jc jd] [H2c H2d]. split; simpl.
  rewrite H1c, H2c. reflexivity. rewrite H2d, H1d. reflexivity.
Qed.
Next Obligation. destruct f. simpl. split; apply comp_id_r. Qed.
Next Obligation. destruct f. simpl. split; apply comp_id_l. Qed.
Next Obligation. destruct f, g, h. simpl. split; apply comp_assoc. Qed.

Infix "×C" := ProdCat
  (at level 41).



Section Cat.
Context {C : Cat}.

(** ** Composition *)

(** ** 复合 *)

(** Postcomposition preserves the specified morphism equality. *)

(** 后合成保持指定态射相等。 *)

Proposition comp_l {X Y Z} (f : Hom Y Z) {x y : Hom X Y}
  : x ≈ y → f ∘ x ≈ f ∘ y.
Proof. intros Heq. rewrite Heq. cato. Qed.

(** Precomposition preserves the specified morphism equality. *)

(** 预合成保持指定态射相等。 *)

Proposition comp_r {X Y Z} (f : Hom X Y) {x y : Hom Y Z}
  : x ≈ y → x ∘ f ≈ y ∘ f.
Proof. intros Heq. rewrite Heq. cato. Qed.



(** ** Inversion & Isomorphism *)

(** ** 逆与同构 *)

(** The second arrow is a left inverse of the first. *)

(** 第二条箭头是第一条的左逆。 *)

Definition is_linv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := g ∘ f ≈ id.

(** The second arrow is a right inverse of the first. *)

(** 第二条箭头是第一条的右逆。 *)

Definition is_rinv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := f ∘ g ≈ id.

(** The two arrows are mutually inverse under specified hom equality. *)

(** 两条箭头在指定 Hom 相等下互逆。 *)

Definition is_inv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := is_linv_of f g ∧ is_rinv_of f g.

(** An arrow with a chosen inverse and both inverse equations. *)

(** 带选定逆及两条互逆方程的箭头。 *)

Definition is_iso {X Y} (f : Hom X Y)
  := ∃ g, is_inv_of f g.

(** An isomorphism retains its forward arrow, inverse and inverse laws. *)

(** 同构保留正向箭头、逆及互逆定律。 *)

Definition iso X Y
  := ∃ f : Hom X Y, is_iso f.

(** Interchange the two arrows of an inverse pair. *)

(** 交换互逆对中的两条箭头。 *)

Theorem is_inv_of_comm {X Y} (f : Hom X Y) (g : Hom Y X)
  : is_inv_of f g → is_inv_of g f.
Proof. intros [H1 H2]. split; auto. Qed.

End Cat.

Hint Unfold is_linv_of : cat.
Hint Unfold is_rinv_of : cat.
Hint Unfold is_inv_of : cat.

Arguments is_linv_of {_ _ _} _ _ /.
Arguments is_rinv_of {_ _ _} _ _ /.
Arguments is_inv_of {_ _ _} _ _ /.

Arguments iso {_} _%_ob _%_ob.

Notation "X '≅' Y" := (iso X Y)
  (at level 70, no associativity) : type_scope.

Notation "X '≅[' C ']' Y" := (@iso C X Y)
  (at level 70, no associativity,
    format "X  ≅[ C ]  Y") : type_scope.

Notation "f '⦂' X '≅' Y" := (@is_iso _ X Y f)
  (at level 50, no associativity,
    X at level 49, Y at level 49).

Tactic Notation "elim_iso" ident(f) :=
  let fi := fresh f "i" in
  let Hfif := fresh "H" fi f in
  let Hffi := fresh "H" f fi in
  intros (f & fi & Hfif & Hffi).



Section Iso.
Context {C : Cat}.

(** Every object is isomorphic to itself. *)

(** 每个对象都与自身同构。 *)

Theorem iso_refl {X}
  : X ≅ X.
Proof. exists id, id. cato. Qed.

(** Reverse an object isomorphism. *)

(** 反转对象同构。 *)

Theorem iso_symm {X Y}
  : X ≅ Y → Y ≅ X.
Proof.
  intros [f [fi [H1 H2]]]; simpl in *.
  exists fi, f. split; cato.
Qed.

(** Compose object isomorphisms. *)

(** 复合对象同构。 *)

Theorem iso_trans {X Y Z}
  : X ≅ Y → Y ≅ Z → X ≅ Z.
Proof.
  intros [f [fi [Hf Hfi]]] [g [gi [Hg Hgi]]]; simpl in *.
  exists (g ∘ f), (fi ∘ gi).
  split; simpl.
  - rewrite comp_assoc.
    rewrite <- (comp_assoc gi).
    rewrite Hg, comp_id_l. auto.
  - rewrite comp_assoc.
    rewrite <- (comp_assoc f).
    rewrite Hfi, comp_id_l. auto.
Qed.

(** [iso] is an equivalence relation. *)

(** [iso] 是等价关系。 *)

Global Instance iso_Equivalence
  : Equivalence iso.
Proof.
  split.
  - intros x. apply iso_refl.
  - intros x y. apply iso_symm.
  - intros x y z. apply iso_trans.
Qed.

End Iso.
