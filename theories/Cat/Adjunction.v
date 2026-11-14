From Cats Require Import
  Cat.Core
  Cat.Functor.Core
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

Class Adj@{u p +} {C D : Cat} (F : Fct C D) (G : Fct D C)
  :=
  { adj_hom : @NatIso _ SetCat@{u p _ _ _ _ _}
      (LeftHomF F) (RightHomF G) }.

Arguments adj_hom {_ _ _ _} _.
Infix "⊣" := Adj (at level 50, no associativity) : cat_scope.

(** ** Transposition along an Adjunction

    Fix functors [F] and [G] and an adjunction [A : F ⊣ G]. Extract the two
    hom maps, their inverse and naturality laws, and the unit and counit. *)

(** ** 沿伴随转置态射

    固定函子 [F]、[G] 及伴随 [A : F ⊣ G]，提取两个 Hom 映射、互逆与自然性定律，以及单位和余单位。 *)

Section Transposition.
Context {C D : Cat} {F : Fct C D} {G : Fct D C} (A : F ⊣ G).

(** The forward hom-setoid map of an adjunction. *)

(** 伴随 Hom 对应的正向保相等映射。 *)

Program Definition adjunct_resp@{s +} {X Y}
  : FunS_resp@{s _ _ _ _ _} (HomSet (F X) Y) (HomSet X (G Y))
  :=
  {|func f := lower ((adj_hom A).1 (X, Y) {|lower := f
                                          |})
  |}.
Next Obligation.
  intros f g H.
  exact (lower (@func_proper _ _ ((adj_hom A).1 (X, Y))
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
  {|func g := lower (((adj_hom A).2 (X, Y)).1 {|lower := g
                                              |})
  |}.
Next Obligation.
  intros f g H.
  exact (lower (@func_proper _ _ ((adj_hom A).2 (X, Y)).1
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
  pose proof (fst ((adj_hom A).2 (X, Y)).2 {|lower := f
                                           |}) as H.
  etransitivity.
  - exact (lower (@func_proper _ _ ((adj_hom A).2 (X, Y)).1
      {|lower := lower ((adj_hom A).1 (X, Y) {|lower := f
                                             |})
      |}
      ((adj_hom A).1 (X, Y) {|lower := f
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
  pose proof (snd ((adj_hom A).2 (X, Y)).2 {|lower := g
                                           |}) as H.
  etransitivity.
  - exact (lower (@func_proper _ _ ((adj_hom A).1 (X, Y))
      {|lower := lower (((adj_hom A).2 (X, Y)).1 {|lower := g
                                                 |})
      |}
      (((adj_hom A).2 (X, Y)).1 {|lower := g
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
  exact (lower (nt_naturality (adj_hom A).1
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
    (NatIso_inv (adj_hom A).1 (adj_hom A).2)
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

Program Definition adj_unit
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

Program Definition adj_counit
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
  : adjunct f ≈ fmap G f ∘ adj_unit X.
Proof.
  change (adjunct f ≈ fmap G f ∘ adjunct (@id (F X))).
  rewrite <- (adjunct_comp_l f (@id (F X))), comp_id_r. reflexivity.
Qed.

(** The inverse transpose is composition with the counit after applying the
    left adjoint. *)

(** 逆向转置等于施加左伴随后与余单位复合。 *)

Lemma unadjunct_counit {X Y} (g : Hom X (G Y))
  : unadjunct g ≈ adj_counit Y ∘ fmap F g.
Proof.
  change (unadjunct g ≈ unadjunct (@id (G Y)) ∘ fmap F g).
  rewrite <- (unadjunct_comp_r (@id (G Y)) g), comp_id_l. reflexivity.
Qed.

(** The unit and counit satisfy the left triangle equation. *)

(** 单位与余单位满足左三角方程。 *)

Theorem adj_triangle_l (X : @Ob C)
  : adj_counit (F X) ∘ fmap F (adj_unit X) ≈ id.
Proof.
  transitivity (unadjunct (adjunct (@id (F X)))).
  - symmetry. apply unadjunct_counit.
  - apply adjunction_β.
Qed.

(** The unit and counit satisfy the right triangle equation. *)

(** 单位与余单位满足右三角方程。 *)

Theorem adj_triangle_r (Y : @Ob D)
  : fmap G (adj_counit Y) ∘ adj_unit (G Y) ≈ id.
Proof.
  transitivity (adjunct (unadjunct (@id (G Y)))).
  - symmetry. apply adjunct_unit.
  - apply adjunction_η.
Qed.

(** The unit is universal among arrows into images of the right adjoint. *)

(** 单位对指向右伴随像的箭头具有泛性质。 *)

Theorem adj_unit_universal {X Y} (g : Hom X (G Y))
  : is_unique (λ f, fmap G f ∘ adj_unit X ≈ g) (unadjunct g).
Proof.
  refine {|this := _
         ; that := _
         |}.
  - rewrite <- adjunct_unit. apply adjunction_η.
  - intros f H. apply (fst (adjunct_iff f g)). rewrite adjunct_unit. exact H.
Defined.

(** The counit is universal among arrows from images of the left adjoint. *)

(** 余单位对从左伴随像出发的箭头具有泛性质。 *)

Theorem adj_counit_universal {X Y} (f : Hom (F X) Y)
  : is_unique (λ g, adj_counit Y ∘ fmap F g ≈ f) (adjunct f).
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
Context {C D : Cat} (F : Fct C D) (G : Fct D C).
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

Definition AdjFromHom
  : F ⊣ G.
Proof.
  refine {|adj_hom := (HomAdjunctN; _)
         |}.
  intros [X Y]. exists ((ψ X Y)^↑S). split; intros [f]; constructor;
    [apply hom_β | apply hom_η].
Defined.

(** The constructed adjunction retains the supplied forward hom map. *)

(** 构造的伴随保留给定正向 Hom 映射。 *)

Theorem adjunct_from_hom {X Y} (f : Hom (F X) Y)
  : f^♯[AdjFromHom] ≈ φ X Y f.
Proof. reflexivity. Qed.

(** The constructed adjunction retains the supplied inverse hom map. *)

(** 构造的伴随保留给定逆向 Hom 映射。 *)

Theorem unadjunct_from_hom {X Y} (g : Hom X (G Y))
  : g^♭[AdjFromHom] ≈ ψ X Y g.
Proof. reflexivity. Qed.

End HomCorrespondence.

(** Taking opposites exchanges the adjoints. The forward hom map is the
    original inverse correspondence; its naturality is already derived. *)

(** 取反交换左右伴随；正向 Hom 映射为原来的逆对应，其自然性已经导出。 *)

Definition OpAdj {C D : Cat}
    {F : Fct C D} {G : Fct D C} (A : F ⊣ G)
  : G^opF ⊣ F^opF.
Proof.
  refine (AdjFromHom (G^opF) (F^opF)
    (λ X Y, unadjunct_resp A (X := Y) (Y := X))
    (λ X Y, adjunct_resp A (X := Y) (Y := X)) _ _ _ _).
  - intros X Y f. exact (@adjunction_η C D F G A Y X f).
  - intros X Y g. exact (@adjunction_β C D F G A Y X g).
  - intros X X' Y f h.
    exact (@unadjunct_comp_l C D F G A Y X X' h f).
  - intros X Y Y' k f.
    exact (@unadjunct_comp_r C D F G A Y Y' X f k).
Defined.

(** The forward transpose of the opposite adjunction is the original
    inverse transpose, including its computational arrow data. *)

(** 反伴随的正向转置是原伴随的逆向转置，并保留可计算箭头数据。 *)

Lemma adjunct_op {C D : Cat} {F : Fct C D} {G : Fct D C}
    (A : F ⊣ G) {X Y} (f : Hom X (G Y))
  : f^♯[OpAdj A] ≈ f^♭[A].
Proof. reflexivity. Qed.

(** The inverse transpose of the opposite adjunction is the original
    forward transpose. *)

(** 反伴随的逆向转置是原伴随的正向转置。 *)

Lemma unadjunct_op {C D : Cat} {F : Fct C D} {G : Fct D C}
    (A : F ⊣ G) {X Y} (f : Hom (F X) Y)
  : f^♭[OpAdj A] ≈ f^♯[A].
Proof. reflexivity. Qed.

(** The opposite adjunction's unit is the original counit at each object. *)

(** 反伴随的单位逐对象为原伴随的余单位。 *)

Lemma adj_op_unit {C D : Cat} {F : Fct C D} {G : Fct D C}
    (A : F ⊣ G) (Y : @Ob D)
  : adj_unit (OpAdj A) Y ≈ adj_counit A Y.
Proof. reflexivity. Qed.

(** The opposite adjunction's counit is the original unit at each object. *)

(** 反伴随的余单位逐对象为原伴随的单位。 *)

Lemma adj_op_counit {C D : Cat} {F : Fct C D} {G : Fct D C}
    (A : F ⊣ G) (X : @Ob C)
  : adj_counit (OpAdj A) X ≈ adj_unit A X.
Proof. reflexivity. Qed.

(** The identity functor is adjoint to itself. *)

(** 恒等函子自伴随。 *)

Definition IdAdj (C : Cat)
  : (@IdF C) ⊣ IdF.
Proof.
  refine (AdjFromHom IdF IdF (λ X Y, id_resp) (λ X Y, id_resp) _ _ _ _);
    intros; reflexivity.
Defined.

(** Compose two adjunctions using their hom correspondences. *)

(** 通过 Hom 对应复合两个伴随。 *)

Definition CompAdj {C D E : Cat}
    {F : Fct C D} {G : Fct D C}
    {L : Fct D E} {R : Fct E D} (B : L ⊣ R) (A : F ⊣ G)
  : (L ∘F F) ⊣ (G ∘F R).
Proof.
  refine (AdjFromHom (L ∘F F) (G ∘F R)
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
