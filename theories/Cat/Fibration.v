From Cats Require Import
  Cat.Core
  Cat.Functor.Core.

(** * Cartesian Morphisms

    A commuting triangle in the base lifts uniquely through the candidate
    morphism. Both the triangle and uniqueness use morphism equivalence. *)

(** * 笛卡尔态射

    基底中的交换三角形沿候选态射唯一提升；交换性和唯一性均使用指定态射相等。 *)

Definition is_cartesian {E B : Cat} (P : Fct E B)
    {X Y : @Ob E} (f : Hom X Y)
  := ∀ Z (g : Hom Z Y) (u : Hom (P Z) (P X)),
    fmap P f ∘ u ≈ fmap P g
    → ∃ h : Hom Z X, is_unique (λ h : Hom Z X, fmap P h ≈ u ∧ f ∘ h ≈ g) h.

Notation "f '⦂' 'Cart(' P ')'" := (is_cartesian P f)
  (at level 50, no associativity,
    format "f  ⦂  Cart( P )") : cat_scope.

(** The unique factor through a cartesian arrow over a specified base factor. *)

(** 位于指定基底分解上、经过笛卡尔箭头的唯一分解。 *)

Definition cartesian_factor {E B : Cat} {P : Fct E B}
    {X Y : @Ob E} {f : Hom X Y} (Hf : f ⦂ Cart(P))
    {Z : @Ob E} (g : Hom Z Y) (u : Hom (P Z) (P X))
    (H : fmap P f ∘ u ≈ fmap P g)
  : Hom Z X
  := (Hf Z g u H).1.

(** The chosen cartesian factor has its base, composite and uniqueness laws. *)

(** 选定笛卡尔分解满足基底、复合与唯一性定律。 *)

Theorem cartesian_factor_unique {E B : Cat} {P : Fct E B}
    {X Y : @Ob E} {f : Hom X Y} (Hf : f ⦂ Cart(P))
    {Z : @Ob E} (g : Hom Z Y) (u : Hom (P Z) (P X))
    (H : fmap P f ∘ u ≈ fmap P g)
  : is_unique (λ h : Hom Z X, fmap P h ≈ u ∧ f ∘ h ≈ g)
      (cartesian_factor Hf g u H).
Proof. exact (Hf Z g u H).2. Qed.

(** The cartesian factor lies over the prescribed base arrow. *)

(** 笛卡尔分解位于给定基底箭头之上。 *)

Theorem cartesian_factor_base {E B : Cat} {P : Fct E B}
    {X Y : @Ob E} {f : Hom X Y} (Hf : f ⦂ Cart(P))
    {Z : @Ob E} (g : Hom Z Y) (u : Hom (P Z) (P X))
    (H : fmap P f ∘ u ≈ fmap P g)
  : fmap P (cartesian_factor Hf g u H) ≈ u.
Proof. exact (fst (this _ _ (cartesian_factor_unique Hf g u H))). Qed.

(** Compatibility with composition for [cartesian_factor]. *)

(** [cartesian_factor] 与复合的相容性。 *)

Theorem cartesian_factor_comp {E B : Cat} {P : Fct E B}
    {X Y : @Ob E} {f : Hom X Y} (Hf : f ⦂ Cart(P))
    {Z : @Ob E} (g : Hom Z Y) (u : Hom (P Z) (P X))
    (H : fmap P f ∘ u ≈ fmap P g)
  : f ∘ cartesian_factor Hf g u H ≈ g.
Proof. exact (snd (this _ _ (cartesian_factor_unique Hf g u H))). Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Theorem cartesian_factor_proper {E B : Cat} {P : Fct E B}
    {X Y : @Ob E} {f : Hom X Y} (Hf : f ⦂ Cart(P))
    {Z : @Ob E} {g g' : Hom Z Y} {u u' : Hom (P Z) (P X)}
    (H : fmap P f ∘ u ≈ fmap P g) (H' : fmap P f ∘ u' ≈ fmap P g')
  : g ≈ g' → u ≈ u'
    → cartesian_factor Hf g u H ≈ cartesian_factor Hf g' u' H'.
Proof.
  intros Hg Hu. apply (that _ _ (cartesian_factor_unique Hf g' u' H')). split.
  - transitivity u; [apply cartesian_factor_base | exact Hu].
  - transitivity g; [apply cartesian_factor_comp | exact Hg].
Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Definition cartesian_proper {E B : Cat} {P : Fct E B}
    {X Y : @Ob E} {f f' : Hom X Y} (Hff' : f ≈ f')
    (Hf : f ⦂ Cart(P))
  : f' ⦂ Cart(P).
Proof.
  intros Z g u H.
  assert (H' : fmap P f ∘ u ≈ fmap P g) by (rewrite Hff'; exact H).
  destruct (Hf Z g u H') as [h [[Hh_base Hh_comp] Hh_unique]].
  exists h. split.
  - split. exact Hh_base. rewrite <- Hff'. exact Hh_comp.
  - intros k [Hk_base Hk_comp]. apply Hh_unique. split. exact Hk_base.
    rewrite Hff'. exact Hk_comp.
Defined.

(** Every identity arrow is cartesian. *)

(** 每条恒等箭头都是笛卡尔的。 *)

Definition cartesian_id {E B : Cat} (P : Fct E B) (X : @Ob E)
  : (@id X) ⦂ Cart(P).
Proof.
  intros Z g u H. rewrite functor_id, comp_id_l in H.
  exists g. split.
  - split; [symmetry; exact H | apply comp_id_l].
  - intros h [_ Hh]. rewrite comp_id_l in Hh. exact Hh.
Defined.

(** A composite of cartesian arrows is cartesian. *)

(** 笛卡尔箭头的复合仍为笛卡尔箭头。 *)

Definition cartesian_comp {E B : Cat} {P : Fct E B}
    {X Y W : @Ob E} {f : Hom X Y} {g : Hom Y W}
    (Hg : g ⦂ Cart(P)) (Hf : f ⦂ Cart(P))
  : (g ∘ f) ⦂ Cart(P).
Proof.
  intros Z q u H.
  assert (Hgq : fmap P g ∘ (fmap P f ∘ u) ≈ fmap P q).
  { rewrite <- comp_assoc, <- functor_comp. exact H. }
  destruct (Hg Z q (fmap P f ∘ u) Hgq) as [v [[Hv_base Hv_comp] Hv_unique]].
  assert (Hfv : fmap P f ∘ u ≈ fmap P v) by (symmetry; exact Hv_base).
  destruct (Hf Z v u Hfv) as [h [[Hh_base Hh_comp] Hh_unique]].
  exists h. split.
  - split. exact Hh_base. rewrite comp_assoc, Hh_comp. exact Hv_comp.
  - intros k [Hk_base Hk_comp]. apply Hh_unique. split. exact Hk_base.
    apply Hv_unique. split.
    + rewrite functor_comp, Hk_base. reflexivity.
    + rewrite <- comp_assoc. exact Hk_comp.
Defined.

(** Equality of both the base factors and their composites determines the
    mediating morphism. This is the cancellation supplied by cartesianness. *)

(** 基底分解及其复合都相等时，中介态射相等；这就是笛卡尔性给出的消去性质。 *)

Theorem cartesian_cancel {E B : Cat} {P : Fct E B}
    {X Y : @Ob E} {f : Hom X Y} (Hf : f ⦂ Cart(P))
    {Z : @Ob E} {h k : Hom Z X}
  : fmap P h ≈ fmap P k → f ∘ h ≈ f ∘ k → h ≈ k.
Proof.
  intros Hbase Hcomp.
  assert (H : fmap P f ∘ fmap P k ≈ fmap P (f ∘ k)).
  { symmetry. apply functor_comp. }
  destruct (Hf Z (f ∘ k) (fmap P k) H) as [t [_ Ht]].
  transitivity t.
  - apply Ht. split; assumption.
  - symmetry. apply Ht. split; reflexivity.
Qed.

(** Cartesian lifts connected by an isomorphism in the base are isomorphic.
    The comparison in the base is supplied as data, without identifying
    objects. *)

(** 通过基底同构连接的笛卡尔提升彼此同构；基底比较作为数据给出，不把对象等同。 *)

Definition cartesian_factor_is_iso {E B : Cat} {P : Fct E B}
    {X X' Y : @Ob E} {f : Hom X Y} {g : Hom X' Y}
    (Hf : f ⦂ Cart(P)) (Hg : g ⦂ Cart(P))
    (u : Hom (P X) (P X')) (Hu : is_iso u)
    (H : fmap P g ∘ u ≈ fmap P f)
  : is_iso (cartesian_factor Hg f u H).
Proof.
  destruct Hu as [ui [Hui Hu]].
  assert (H' : fmap P f ∘ ui ≈ fmap P g).
  { rewrite <- H, comp_assoc, Hu, comp_id_r. reflexivity. }
  exists (cartesian_factor Hf g ui H'). split.
  - apply (cartesian_cancel Hf).
    + rewrite functor_comp. transitivity (ui ∘ u).
      * apply comp_proper; apply cartesian_factor_base.
      * transitivity (@id (P X)); [exact Hui | symmetry; apply functor_id].
    + etransitivity; [symmetry; apply comp_assoc |].
      etransitivity.
      * apply comp_proper; [apply cartesian_factor_comp | reflexivity].
      * etransitivity; [apply cartesian_factor_comp | symmetry; apply comp_id_r].
  - apply (cartesian_cancel Hg).
    + rewrite functor_comp. transitivity (u ∘ ui).
      * apply comp_proper; apply cartesian_factor_base.
      * transitivity (@id (P X')); [exact Hu | symmetry; apply functor_id].
    + etransitivity; [symmetry; apply comp_assoc |].
      etransitivity.
      * apply comp_proper; [apply cartesian_factor_comp | reflexivity].
      * etransitivity; [apply cartesian_factor_comp | symmetry; apply comp_id_r].
Defined.

(** Cartesian lifts of the same base arrow and codomain have isomorphic
    domains. *)

(** 同一基底箭头和余域的笛卡尔提升具有同构的定义域。 *)

Definition cartesian_unique {E B : Cat} {P : Fct E B}
    {X X' Y : @Ob E} {f : Hom X Y} {g : Hom X' Y}
    (Hf : f ⦂ Cart(P)) (Hg : g ⦂ Cart(P))
    (u : Hom (P X) (P X')) (Hu : is_iso u)
    (H : fmap P g ∘ u ≈ fmap P f)
  : X ≅ X'
  := (cartesian_factor Hg f u H; cartesian_factor_is_iso Hf Hg u Hu H).

(** ** Chosen Cartesian Lifts

    The base-object identification is explicit data. No equality between its
    witnesses and no strict identity or composition law for lifts is assumed. *)

(** ** 选定笛卡尔提升

    基底对象的识别作为显式数据保留；不要求其见证相等，也不预设提升的严格恒等律
    或复合律。 *)

Class HasCartesianLift {E B : Cat} (P : Fct E B)
  :=
  { CartesianLift {Y : @Ob E} {X : @Ob B} (f : Hom X (P Y)) : @Ob E
  ; cartesian_lift_base {Y X} (f : Hom X (P Y)) : P (CartesianLift f) = X
  ; cartesian_lift {Y X} (f : Hom X (P Y)) : Hom (CartesianLift f) Y
  ; cartesian_lift_comm {Y X} (f : Hom X (P Y))
    : fmap P (cartesian_lift f) ≈ f ∘ eq_to_hom (cartesian_lift_base f)
  ; cartesian_lift_universal {Y X} (f : Hom X (P Y))
    : cartesian_lift f ⦂ Cart(P)
  }.

Arguments CartesianLift {_ _ _ _ _ _} _.
Arguments cartesian_lift_base {_ _ _ _ _ _} _.
Arguments cartesian_lift {_ _ _ _ _ _} _.
Arguments cartesian_lift_comm {_ _ _ _ _ _} _.
Arguments cartesian_lift_universal {_ _ _ _ _ _} _.

Notation "f '^*[' P ']' Y" := (@CartesianLift _ _ P _ Y _ f)
  (at level 35, no associativity, format "f  ^*[ P ]  Y") : cat_scope.
