From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Terminal.

(** * Product Objects *)

(** * 积对象 *)

(** Every cone over the pair has a unique mediator to the candidate product. *)

(** 对象对上的每个锥到候选积都有唯一中介。 *)

Definition is_product {C : Cat} (X Y P : Ob)
    (p : Hom P X) (q : Hom P Y)
  := ∀ Z (f : Hom Z X) (g : Hom Z Y),
    ∃ h : Hom Z P, is_unique (λ h, p ∘ h ≈ f ∧ q ∘ h ≈ g) h.

(** Chosen binary products, their projections and universal properties. *)

(** 选定二元积、投影及其泛性质。 *)

Class HasProduct (C : Cat)
  :=
  { Prod : Ob → Ob → Ob
  ; π1 {X Y} : Hom (Prod X Y) X
  ; π2 {X Y} : Hom (Prod X Y) Y

  ; product_universal {X Y} : is_product X Y (Prod X Y) π1 π2
  }.

Arguments Prod {_ _} _%_ob _%_ob.
Arguments π1 {_ _ _ _}.
Arguments π2 {_ _ _ _}.
Arguments product_universal {_ _ _ _} _ _ _.

(** The Type-valued universal property supplies the chosen mediator. *)

(** Type 值泛性质给出选定中介。 *)

Definition pair {C : Cat} `{HP : !HasProduct C} {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : Hom Z (Prod X Y)
  := (product_universal Z f g).1.

Arguments pair {_ _ _ _ _} _ _.

(** Pairing is the unique arrow with the given two projections. *)

(** 配对是具有给定两个投影的唯一箭头。 *)

Theorem product_pair_unique {C : Cat} `{HP : !HasProduct C} {X Y Z}
    {f : Hom Z X} {g : Hom Z Y}
  : is_unique (λ h, π1 ∘ h ≈ f ∧ π2 ∘ h ≈ g) (pair f g).
Proof. exact (product_universal Z f g).2. Qed.

Arguments product_pair_unique {_ _ _ _} _ _ _.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance product_pair_proper {C : Cat} `{HP : !HasProduct C} {X Y Z}
  : Proper (@HomEq[Z,X] ==> @HomEq[Z,Y] ==> @HomEq[Z,Prod X Y]) pair.
Proof.
  intros f f' Hf g g' Hg.
  destruct (product_pair_unique Z f g) as [[H1 H2] _].
  apply (product_pair_unique Z f' g'). split.
  - transitivity f; assumption.
  - transitivity g; assumption.
Qed.

Notation "X '×' Y" := (Prod X Y)
  (at level 41, right associativity) : ob_scope.

Notation "'⟨' f ',' g '⟩'" := (pair f g)
  (format "'⟨' f  ','  g '⟩'") : hom_scope.

Notation "'@π1' X Y" := (@π1 _ _ _ X Y)
  (at level 35) : hom_scope.

Notation "'@π2' X Y" := (@π2 _ _ _ X Y)
  (at level 35) : hom_scope.



Section Product.
Context {C : Cat}.

Tactic Notation "elim_product" constr(H) "as" ident(h) :=
  let Hh1 := fresh "H" h "1" in
  let Hh2 := fresh "H" h "2" in
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & (Hh1 & Hh2) & Hh_unique).

Context {X Y P Q : Ob}.
Context {p1 : Hom P X} {p2 : Hom P Y}.
Context {q1 : Hom Q X} {q2 : Hom Q Y}.

(** Candidate binary products are isomorphic by their universal properties. *)

(** 候选二元积由泛性质彼此同构。 *)

Theorem product_unique
  : is_product X Y P p1 p2
  → is_product X Y Q q1 q2
  → P ≅ Q.
Proof.
  intros HP HQ.
  exists (HQ P p1 p2).1, (HP Q q1 q2).1.
  destruct (HP Q q1 q2) as [f [[Hf1 Hf2] Hf_unique]].
  destruct (HQ P p1 p2) as [g [[Hg1 Hg2] Hg_unique]].
  split; simpl.
  - destruct (HP P p1 p2) as [h [_ Hh_unique]].
    assert (Hid : id ≈ h).
    { apply Hh_unique; split; rewrite comp_id_r; reflexivity. }
    rewrite Hid. apply Hh_unique; split; rewrite <- comp_assoc.
    + rewrite Hf1, Hg1. reflexivity.
    + rewrite Hf2, Hg2. reflexivity.
  - destruct (HQ Q q1 q2) as [h [_ Hh_unique]].
    assert (Hid : id ≈ h).
    { apply Hh_unique; split; rewrite comp_id_r; reflexivity. }
    rewrite Hid. apply Hh_unique; split; rewrite <- comp_assoc.
    + rewrite Hg1, Hf1. reflexivity.
    + rewrite Hg2, Hf2. reflexivity.
Defined.

End Product.

Notation "P '⦂' '≅' X '×' Y 'with' p1 ',' p2"
  := (is_product X Y P p1 p2)
  (at level 50).



Section Product.
Context {C : Cat} `{HP : !HasProduct C}.

(** The first projection of a pairing is its first component. *)

(** 配对的第一投影是其第一分量。 *)

Proposition product_β1 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π1 ∘ ⟨f,g⟩ ≈ f.
Proof.
  pose (AP := product_pair_unique Z f g).
  destruct AP as [[H1 _] _].
  auto.
Qed.

(** The second projection of a pairing is its second component. *)

(** 配对的第二投影是其第二分量。 *)

Proposition product_β2 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π2 ∘ ⟨f,g⟩ ≈ g.
Proof.
  pose (AP := product_pair_unique Z f g).
  destruct AP as [[_ H2] _].
  auto.
Qed.

(** Precomposition distributes over pairing. *)

(** 预合成分配到配对的两个分量。 *)

Lemma product_comp_r {X Y Z W}
    (f : Hom Z X) (g : Hom Z Y) (h : Hom W Z)
  : ⟨f , g⟩ ∘ h ≈ ⟨f ∘ h , g ∘ h⟩.
Proof.
  apply product_pair_unique.
  split.
  - rewrite <- comp_assoc, product_β1. cato.
  - rewrite <- comp_assoc, product_β2. cato.
Qed.

(** Every map into a product is the pairing of its projections. *)

(** 指向积的每条映射都是其投影的配对。 *)

Lemma product_η {X Y Z} (h : Hom Z (X × Y))
  : h ≈ ⟨ π1 ∘ h , π2 ∘ h ⟩.
Proof.
  apply product_pair_unique; split; cato.
Qed.

(** Interchange the factors of a selected binary product by an isomorphism. *)

(** 通过同构交换选定二元积的因子。 *)

Lemma product_comm {X Y}
  : X × Y ≅ Y × X.
Proof.
  exists ⟨π2, π1⟩, ⟨π2, π1⟩.
  simpl. split.
  - rewrite product_comp_r.
    rewrite product_β1.
    rewrite product_β2.
    symmetry.
    apply product_pair_unique.
    split; cato.
  - rewrite product_comp_r.
    rewrite product_β1.
    rewrite product_β2.
    symmetry.
    apply product_pair_unique.
    split; cato.
Qed.

End Product.

Hint Resolve product_universal : cat.
Hint Resolve product_β1 : cat.
Hint Resolve product_β2 : cat.

Hint Rewrite @product_β1 : cat.
Hint Rewrite @product_β2 : cat.



Section Cross.
Context {C : Cat} `{H : !HasProduct C}.

(** Apply one arrow to each factor of a binary product. *)

(** 分别将一条箭头作用于二元积的各因子。 *)

Definition cross {X Y X' Y'} (f : Hom X X') (g : Hom Y Y')
  : Hom (X × Y) (X' × Y')
  := ⟨ f ∘ π1 , g ∘ π2 ⟩.

Opaque cross.

End Cross.

Notation "f '×' g" := (cross f g)
  (at level 41, right associativity) : hom_scope.



Section Cross.
Context {C : Cat} `{HP : !HasProduct C}.

(** A componentwise product map is determined by its two projections. *)

(** 逐分量积映射由两个投影确定。 *)

Lemma cross_η {X Y X' Y'} (f : Hom X X') (g : Hom Y Y')
  : f × g ≈ ⟨ f ∘ π1 , g ∘ π2 ⟩.
Proof. cato. Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance cross_proper {X Y X' Y'}
  : Proper (@HomEq[X, X'] ==> @HomEq[Y, Y'] ==>
      @HomEq[X × Y, X' × Y']) cross.
Proof.
  intros f f' Hf g g' Hg. rewrite !cross_η, Hf, Hg. reflexivity.
Qed.

(** Compatibility with identities for [cross]. *)

(** [cross] 与恒等的相容性。 *)

Lemma cross_id {X Y}
  : (@id X) × (@id Y) ≈ id.
Proof.
  rewrite cross_η, !comp_id_l. symmetry.
  apply product_pair_unique. split; apply comp_id_r.
Qed.

(** Compatibility with composition for [cross]. *)

(** [cross] 与复合的相容性。 *)

Lemma cross_comp {X Y X' Y' X'' Y''}
    (f' : Hom X' X'') (g' : Hom Y' Y'')
    (f : Hom X X') (g : Hom Y Y')
  : (f' ∘ f) × (g' ∘ g) ≈ (f' × g') ∘ (f × g).
Proof.
  rewrite !cross_η, product_comp_r.
  rewrite !comp_assoc, product_β1, product_β2.
  reflexivity.
Qed.

(** Independent actions on the two factors commute. *)

(** 两个因子上的独立作用彼此交换。 *)

Lemma cross_exchange {X X' Y Y'} (f : Hom X X') (g : Hom Y Y')
  : (id × g) ∘ (f × id) ≈ (f × id) ∘ (id × g).
Proof.
  rewrite <- !cross_comp, !comp_id_l, !comp_id_r. reflexivity.
Qed.

(** Postcomposition by a product map acts on both pairing components. *)

(** 积映射的后合成分别作用于配对的两个分量。 *)

Lemma product_comp_l {X Y X' Y' Z}
    (f : Hom Z X) (g : Hom Z Y) (f' : Hom X X') (g' : Hom Y Y')
  : (f' × g') ∘ ⟨f , g⟩ ≈ ⟨f' ∘ f , g' ∘ g⟩.
Proof.
  apply product_pair_unique.
  split.
  - rewrite <- comp_assoc.
    rewrite cross_η.
    rewrite product_β1.
    rewrite comp_assoc.
    rewrite product_β1.
    cato.
  - rewrite <- comp_assoc.
    rewrite cross_η.
    rewrite product_β2.
    rewrite comp_assoc.
    rewrite product_β2.
    cato.
Qed.

End Cross.



Section Product.
Context {C : Cat}.
Context `{HT : !HasTerminal C}.
Context `{HP : !HasProduct C}.

(** The product with a terminal object on the left is isomorphic to the
    object. *)

(** 左侧与终对象取积同构于原对象。 *)

Theorem term_prod_id_l {X}
  : 1 × X ≅ X.
Proof.
  exists π2, ⟨!,id⟩; simpl.
  split.
  - rewrite product_comp_r.
    rewrite term_η.
    rewrite comp_id_l.
    symmetry.
    apply product_pair_unique.
    split; cato.
  - cato.
Qed.

(** The product with a terminal object on the right is isomorphic to the
    object. *)

(** 右侧与终对象取积同构于原对象。 *)

Theorem term_prod_id_r {X}
  : X × 1 ≅ X.
Proof.
  rewrite product_comm.
  apply term_prod_id_l.
Qed.

(** The terminal arrow on the terminal object is its identity. *)

(** 终对象上的终箭头就是其恒等态射。 *)

Example term_1_1 {X}
  : (X × 1) × 1 ≅ X.
Proof.
  rewrite term_prod_id_r.
  rewrite term_prod_id_r.
  reflexivity.
Qed.

End Product.

(** The chosen product is functorial in both arguments. *)

(** 选定积在两个参数上都具有函子性。 *)

Program Definition ProductF {C : Cat} `{HP : !HasProduct C}
  : Functor (C ×C C) C
  :=
  {|F0 p := (fst p × snd p)%ob
  ; F1 X Y f := (fst f × snd f)%hom
  |}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg]. apply cross_proper; assumption.
Qed.
Next Obligation. apply cross_id. Qed.
Next Obligation. apply cross_comp. Qed.

(** The product functor with its right factor fixed. *)

(** 固定右因子的积函子。 *)

Definition ProductRF {C : Cat} `{HP : !HasProduct C} (X : @Ob C)
  : Functor C C
  := π1F ProductF X.

Notation "'(-×' X ')'" := (ProductRF X) : cat_scope.
