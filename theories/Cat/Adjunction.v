From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom.

(** * Adjunctions by Natural Hom Isomorphisms

    Both hom-functors inherit their functor laws from HomF. The chosen natural
    isomorphism supplies forward naturality; inverse naturality is derived by
    NatIso_inv. The ambient set levels are independent upper bounds, not
    identifications of the two categories' native hom levels. *)

(** * 以自然 Hom 同构定义伴随

    两个 Hom 函子的函子律来自 [HomF]。选定的自然同构给出正向自然性，
    [NatIso_inv] 导出逆向自然性。环境广集的宇宙仅为独立上界，不把两侧原有的
    Hom 大小等同。 *)

Class Adjunction@{u p +} {C D : Cat} (F : Functor C D) (G : Functor D C)
  :=
  { adjunction_hom : @NatIso _ SetCat@{u p _ _ _ _ _}
      (LeftHomF F) (RightHomF G) }.

Arguments adjunction_hom {_ _ _ _} _.
Infix "⊣" := Adjunction (at level 50, no associativity) : cat_scope.

Section Transposition.
Context {C D : Cat} {F : Functor C D} {G : Functor D C} (A : F ⊣ G).

(** The forward hom-setoid map of an adjunction. *)

(** 伴随 Hom 对应的正向保相等映射。 *)

Program Definition adjunct_resp@{s +} {X Y}
  : FunS_resp@{s _ _ _ _ _} (HomSet (F X) Y) (HomSet X (G Y))
  :=
  {|func f := lower ((adjunction_hom A).1 (X, Y) {|lower := f
                                                 |})
  |}.
Next Obligation.
  intros f g H.
  exact (lower (@func_proper _ _ ((adjunction_hom A).1 (X, Y))
    {|lower := f
    |} {|lower := g
       |} {|lower := H
          |})).
Defined.

(** The inverse hom-setoid map of an adjunction. *)

(** 伴随 Hom 对应的逆向保相等映射。 *)

Program Definition unadjunct_resp@{s +} {X Y}
  : FunS_resp@{s _ _ _ _ _} (HomSet X (G Y)) (HomSet (F X) Y)
  :=
  {|func g := lower (((adjunction_hom A).2 (X, Y)).1 {|lower := g
                                                     |})
  |}.
Next Obligation.
  intros f g H.
  exact (lower (@func_proper _ _ ((adjunction_hom A).2 (X, Y)).1
    {|lower := f
    |} {|lower := g
       |} {|lower := H
          |})).
Defined.

(** Transpose a morphism along the forward adjunction correspondence. *)

(** 沿伴随正向对应转置态射。 *)

Definition adjunct {X Y} (f : Hom (F X) Y)
  : Hom X (G Y)
  := adjunct_resp f.
(** Transpose a morphism along the inverse adjunction correspondence. *)

(** 沿伴随逆向对应转置态射。 *)

Definition unadjunct {X Y} (g : Hom X (G Y))
  : Hom (F X) Y
  := unadjunct_resp g.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance adjunct_proper {X Y}
  : Proper (@HomEq[F X, Y] ==> @HomEq[X, G Y]) adjunct.
Proof. apply func_proper. Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance unadjunct_proper {X Y}
  : Proper (@HomEq[X, G Y] ==> @HomEq[F X, Y]) unadjunct.
Proof. apply func_proper. Qed.

(** The forward and inverse transposes cancel on one hom-setoid. *)

(** 正向与逆向转置在一侧 Hom 广集上互相抵消。 *)

Theorem adjunction_β {X Y} (f : Hom (F X) Y)
  : unadjunct (adjunct f) ≈ f.
Proof.
  pose proof (fst ((adjunction_hom A).2 (X, Y)).2 {|lower := f
                                                  |}) as H.
  etransitivity.
  - exact (lower (@func_proper _ _ ((adjunction_hom A).2 (X, Y)).1
      {|lower := lower ((adjunction_hom A).1 (X, Y) {|lower := f
                                                    |})
      |}
      ((adjunction_hom A).1 (X, Y) {|lower := f
                                   |})
      {|lower := reflexivity _
      |})).
  - exact (lower H).
Qed.

(** The inverse and forward transposes cancel on the other hom-setoid. *)

(** 逆向与正向转置在另一侧 Hom 广集上互相抵消。 *)

Theorem adjunction_η {X Y} (g : Hom X (G Y))
  : adjunct (unadjunct g) ≈ g.
Proof.
  pose proof (snd ((adjunction_hom A).2 (X, Y)).2 {|lower := g
                                                  |}) as H.
  etransitivity.
  - exact (lower (@func_proper _ _ ((adjunction_hom A).1 (X, Y))
      {|lower := lower (((adjunction_hom A).2 (X, Y)).1 {|lower := g
                                                        |})
      |}
      (((adjunction_hom A).2 (X, Y)).1 {|lower := g
                                       |})
      {|lower := reflexivity _
      |})).
  - exact (lower H).
Qed.

(** The forward transpose is natural in both hom variables. *)

(** 正向转置在两个 Hom 变量上自然。 *)

Lemma adjunct_naturality {X X' : @Ob C} {Y Y' : @Ob D}
    (h : Hom X' X) (k : Hom Y Y')
    (f : Hom (F X) Y)
  : adjunct (k ∘ f ∘ fmap F h) ≈ fmap G k ∘ adjunct f ∘ h.
Proof.
  exact (lower (nt_naturality (adjunction_hom A).1
    (X := (X, Y)) (Y := (X', Y')) (h, k) {|lower := f
                                         |})).
Qed.

(** Compatibility with precomposition for [adjunct]. *)

(** [adjunct] 与预合成的相容性。 *)

Lemma adjunct_comp_r {X X' Y} (f : Hom (F X) Y) (h : Hom X' X)
  : adjunct (f ∘ fmap F h) ≈ adjunct f ∘ h.
Proof.
  pose proof (adjunct_naturality h id f) as H.
  rewrite (functor_id D C G), !comp_id_l in H. exact H.
Qed.

(** Compatibility with postcomposition for [adjunct]. *)

(** [adjunct] 与后合成的相容性。 *)

Lemma adjunct_comp_l {X Y Y'} (k : Hom Y Y') (f : Hom (F X) Y)
  : adjunct (k ∘ f) ≈ fmap G k ∘ adjunct f.
Proof.
  pose proof (adjunct_naturality id k f) as H.
  rewrite (functor_id C D F), !comp_id_r in H. exact H.
Qed.

(** The inverse transpose is natural in both hom variables. *)

(** 逆向转置在两个 Hom 变量上自然。 *)

Lemma unadjunct_naturality {X X' : @Ob C} {Y Y' : @Ob D}
    (h : Hom X' X) (k : Hom Y Y') (g : Hom X (G Y))
  : unadjunct (fmap G k ∘ g ∘ h) ≈ k ∘ unadjunct g ∘ fmap F h.
Proof.
  exact (lower (nt_naturality
    (NatIso_inv (adjunction_hom A).1 (adjunction_hom A).2)
    (X := (X, Y)) (Y := (X', Y')) (h, k) {|lower := g
                                         |})).
Qed.

(** Compatibility with precomposition for [unadjunct]. *)

(** [unadjunct] 与预合成的相容性。 *)

Lemma unadjunct_comp_r {X X' Y} (g : Hom X (G Y)) (h : Hom X' X)
  : unadjunct (g ∘ h) ≈ unadjunct g ∘ fmap F h.
Proof.
  pose proof (unadjunct_naturality h id g) as H.
  rewrite (functor_id D C G), !comp_id_l in H. exact H.
Qed.

(** Compatibility with postcomposition for [unadjunct]. *)

(** [unadjunct] 与后合成的相容性。 *)

Lemma unadjunct_comp_l {X Y Y'} (k : Hom Y Y') (g : Hom X (G Y))
  : unadjunct (fmap G k ∘ g) ≈ k ∘ unadjunct g.
Proof.
  pose proof (unadjunct_naturality id k g) as H.
  rewrite (functor_id C D F), !comp_id_r in H. exact H.
Qed.

(** An adjunction equation is equivalent to its inverse-transpose equation. *)

(** 伴随方程等价于其逆转置方程。 *)

Theorem adjunct_iff {X Y} (f : Hom (F X) Y) (g : Hom X (G Y))
  : adjunct f ≈ g ↔ f ≈ unadjunct g.
Proof.
  split; intros H.
  - rewrite <- (adjunction_β f), H. reflexivity.
  - rewrite H, adjunction_η. reflexivity.
Qed.

(** Unit and counit are transposed identities, with naturality inherited from
    the hom correspondence. They are not additional chosen fields. *)

(** 单位与余单位由恒等态射转置得到，其自然性来自 Hom 对应，不是额外选取的字段。 *)

Program Definition adjunction_unit
  : IdF ⇒ G ∘F F
  :=
  {|nt X := adjunct id
  |}.
Next Obligation.
  rewrite <- (adjunct_comp_r id f), comp_id_l.
  rewrite <- (adjunct_comp_l (fmap F f) id), comp_id_r. reflexivity.
Qed.

(** Inverse-transpose target identities to obtain the adjunction counit. *)

(** 逆转置目标端恒等态射得到伴随余单位。 *)

Program Definition adjunction_counit
  : F ∘F G ⇒ IdF
  :=
  {|nt Y := unadjunct id
  |}.
Next Obligation.
  rewrite <- (unadjunct_comp_r (@id (G Y)) (fmap G f)), comp_id_l.
  rewrite <- (unadjunct_comp_l f (@id (G X))), comp_id_r. reflexivity.
Qed.

(** The forward transpose is composition with the unit after applying the
    right adjoint. *)

(** 正向转置等于施加右伴随后与单位复合。 *)

Lemma adjunct_unit {X Y} (f : Hom (F X) Y)
  : adjunct f ≈ fmap G f ∘ adjunction_unit X.
Proof.
  change (adjunct f ≈ fmap G f ∘ adjunct (@id (F X))).
  rewrite <- (adjunct_comp_l f (@id (F X))), comp_id_r. reflexivity.
Qed.

(** The inverse transpose is composition with the counit after applying the
    left adjoint. *)

(** 逆向转置等于施加左伴随后与余单位复合。 *)

Lemma unadjunct_counit {X Y} (g : Hom X (G Y))
  : unadjunct g ≈ adjunction_counit Y ∘ fmap F g.
Proof.
  change (unadjunct g ≈ unadjunct (@id (G Y)) ∘ fmap F g).
  rewrite <- (unadjunct_comp_r (@id (G Y)) g), comp_id_l. reflexivity.
Qed.

(** The unit and counit satisfy the left triangle equation. *)

(** 单位与余单位满足左三角方程。 *)

Theorem adjunction_triangle_l (X : @Ob C)
  : adjunction_counit (F X) ∘ fmap F (adjunction_unit X) ≈ id.
Proof.
  transitivity (unadjunct (adjunct (@id (F X)))).
  - symmetry. apply unadjunct_counit.
  - apply adjunction_β.
Qed.

(** The unit and counit satisfy the right triangle equation. *)

(** 单位与余单位满足右三角方程。 *)

Theorem adjunction_triangle_r (Y : @Ob D)
  : fmap G (adjunction_counit Y) ∘ adjunction_unit (G Y) ≈ id.
Proof.
  transitivity (adjunct (unadjunct (@id (G Y)))).
  - symmetry. apply adjunct_unit.
  - apply adjunction_η.
Qed.

(** The unit is universal among arrows into images of the right adjoint. *)

(** 单位对指向右伴随像的箭头具有泛性质。 *)

Theorem adjunction_unit_universal {X Y} (g : Hom X (G Y))
  : is_unique (λ f, fmap G f ∘ adjunction_unit X ≈ g) (unadjunct g).
Proof.
  refine {|this := _
         ; that := _
         |}.
  - rewrite <- adjunct_unit. apply adjunction_η.
  - intros f H. apply (fst (adjunct_iff f g)). rewrite adjunct_unit. exact H.
Defined.

(** The counit is universal among arrows from images of the left adjoint. *)

(** 余单位对从左伴随像出发的箭头具有泛性质。 *)

Theorem adjunction_counit_universal {X Y} (f : Hom (F X) Y)
  : is_unique (λ g, adjunction_counit Y ∘ fmap F g ≈ f) (adjunct f).
Proof.
  refine {|this := _
         ; that := _
         |}.
  - rewrite <- unadjunct_counit. apply adjunction_β.
  - intros g H. symmetry. apply (snd (adjunct_iff f g)).
    rewrite unadjunct_counit. symmetry. exact H.
Defined.

End Transposition.

Notation "f '^♯[' A ']'" := (adjunct A f) (at level 35) : hom_scope.
Notation "g '^♭[' A ']'" := (unadjunct A g) (at level 35) : hom_scope.

(** ** Building the Natural Isomorphism from Native Hom Maps

    Only forward naturality needs to be supplied. The inverse laws are
    precisely the component isomorphism laws. *)

(** ** 由原生 Hom 映射构造自然同构

    只需给出正向自然性；两个互逆定律就是各分量的同构定律。 *)

Section HomCorrespondence.
Context {C D : Cat} (F : Functor C D) (G : Functor D C).
Context (φ : ∀ X Y, HomSet (F X) Y →r HomSet X (G Y)).
Context (ψ : ∀ X Y, HomSet X (G Y) →r HomSet (F X) Y).
Context (hom_β : ∀ X Y f, ψ X Y (φ X Y f) ≈ f).
Context (hom_η : ∀ X Y g, φ X Y (ψ X Y g) ≈ g).
Context (hom_comp_r : ∀ X X' Y (f : Hom (F X) Y) (h : Hom X' X),
  φ X' Y (f ∘ fmap F h) ≈ φ X Y f ∘ h).
Context (hom_comp_l : ∀ X Y Y' (k : Hom Y Y') (f : Hom (F X) Y),
  φ X Y' (k ∘ f) ≈ fmap G k ∘ φ X Y f).

(** Assemble a forward-natural family of hom maps into a natural
    transformation. *)

(** 将正向自然的 Hom 映射族组装为自然变换。 *)

Program Definition HomAdjunctN
  : LeftHomF F ⇒ RightHomF G
  :=
  {|nt X := (φ (fst X) (snd X))^↑S
  |}.
Next Obligation.
  intros [h]. constructor.
  change (φ (fst Y) (snd Y) (snd f ∘ h ∘ fmap F (fst f)) ≈
    fmap G (snd f) ∘ φ (fst X) (snd X) h ∘ fst f).
  rewrite hom_comp_r, hom_comp_l. reflexivity.
Defined.

(** Construct the adjunction from mutually inverse native hom maps. *)

(** 由互逆的原生 Hom 映射构造伴随。 *)

Definition AdjunctionFromHom
  : F ⊣ G.
Proof.
  refine {|adjunction_hom := (HomAdjunctN; _)
         |}.
  intros [X Y]. exists ((ψ X Y)^↑S). split; intros [f]; constructor;
    [apply hom_β | apply hom_η].
Defined.

(** The constructed adjunction retains the supplied forward hom map. *)

(** 构造的伴随保留给定正向 Hom 映射。 *)

Theorem adjunct_from_hom {X Y} (f : Hom (F X) Y)
  : f^♯[AdjunctionFromHom] ≈ φ X Y f.
Proof. reflexivity. Qed.

(** The constructed adjunction retains the supplied inverse hom map. *)

(** 构造的伴随保留给定逆向 Hom 映射。 *)

Theorem unadjunct_from_hom {X Y} (g : Hom X (G Y))
  : g^♭[AdjunctionFromHom] ≈ ψ X Y g.
Proof. reflexivity. Qed.

End HomCorrespondence.

(** The identity functor is adjoint to itself. *)

(** 恒等函子自伴随。 *)

Definition IdAdjunction (C : Cat)
  : (@IdF C) ⊣ IdF.
Proof.
  refine (AdjunctionFromHom IdF IdF (λ X Y, id_resp) (λ X Y, id_resp) _ _ _ _);
    intros; reflexivity.
Defined.

(** Compose two adjunctions using their hom correspondences. *)

(** 通过 Hom 对应复合两个伴随。 *)

Definition CompAdjunction {C D E : Cat}
    {F : Functor C D} {G : Functor D C}
    {L : Functor D E} {R : Functor E D} (B : L ⊣ R) (A : F ⊣ G)
  : (L ∘F F) ⊣ (G ∘F R).
Proof.
  refine (AdjunctionFromHom (L ∘F F) (G ∘F R)
    (λ X Y, adjunct_resp A ∘r adjunct_resp B)
    (λ X Y, unadjunct_resp B ∘r unadjunct_resp A) _ _ _ _).
  - intros X Y f.
    change (unadjunct B (unadjunct A (adjunct A (adjunct B f))) ≈ f).
    rewrite (adjunction_β A), (adjunction_β B). reflexivity.
  - intros X Y g.
    change (adjunct A (adjunct B (unadjunct B (unadjunct A g))) ≈ g).
    rewrite (adjunction_η B), (adjunction_η A). reflexivity.
  - intros X X' Y f h.
    change (adjunct A (adjunct B (f ∘ fmap L (fmap F h))) ≈
      adjunct A (adjunct B f) ∘ h).
    rewrite (adjunct_comp_r B f (fmap F h)), (adjunct_comp_r A (adjunct B f) h).
    reflexivity.
  - intros X Y Y' k f.
    change (adjunct A (adjunct B (k ∘ f)) ≈
      fmap G (fmap R k) ∘ adjunct A (adjunct B f)).
    rewrite (adjunct_comp_l B k f), (adjunct_comp_l A (fmap R k) (adjunct B f)).
    reflexivity.
Defined.
