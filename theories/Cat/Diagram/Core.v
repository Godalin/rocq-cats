From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Diagrams, Constant Diagrams and Cones *)

(** * 图式、常图式与锥 *)

(** The diagram with fixed value and identity morphism action. *)

(** 取固定对象为值、将态射送到恒等的常图式。 *)

Program Definition ConstF (J : Cat) {C : Cat} (X : @Ob C)
  : Fct J C
  :=
  {|F0 j := X
  ; F1 j k f := id
  |}.
Next Obligation. intros f g H. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. symmetry. apply comp_id_l. Qed.

(** Send an object or arrow to its constant diagram or transformation. *)

(** 将对象和箭头送到对应常图式及常自然变换。 *)

Program Definition DiagF (J C : Cat)
  : Fct C (FctCat J C)
  :=
  {|F0 X := ConstF J X
  ; F1 X Y f :=
      {|nt j := f
      |}
  |}.
Next Obligation. carw. Qed.
Next Obligation. intros f g H j. exact H. Qed.
Next Obligation. intros j. reflexivity. Qed.
Next Obligation. intros j. reflexivity. Qed.

Notation "'Δ[' J ',' C ']'" := (DiagF J C) : cat_scope.

(** A cone is a natural transformation from a constant diagram. *)

(** 锥是从常图式出发的自然变换。 *)

Definition Cone {J C : Cat} (D : Fct J C) (X : @Ob C)
  := ConstF J X ⇒ D.
Notation "X '⇒Δ' D" := (Cone D X)
  (at level 50, no associativity) : cat_scope.

(** Every cone leg factors through a preceding leg along a diagram arrow. *)

(** 每条锥腿沿图式箭头经过前一条锥腿分解。 *)

Lemma cone_naturality {J C : Cat} {D : Fct J C} {X}
    (κ : X ⇒Δ D) {i j : @Ob J} (f : Hom i j)
  : κ j ≈ fmap D f ∘ κ i.
Proof.
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_r in H. exact H.
Qed.

(** Precompose every cone leg with the given apex map. *)

(** 将每条锥腿与给定顶点映射预合成。 *)

Definition cone_comp {J C : Cat} {D : Fct J C} {X Y : @Ob C}
    (κ : X ⇒Δ D) (f : Hom Y X)
  : Y ⇒Δ D
  := κ ∘Nv fmap (DiagF J C) f.

Infix "∘Cone" := cone_comp (at level 40, left associativity) : cat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance cone_comp_proper {J C : Cat} {D : Fct J C} {X Y : @Ob C}
  : Proper (NatEq ==> @HomEq[Y, X] ==> NatEq) (@cone_comp J C D X Y).
Proof. intros κ μ H f g K j. cbn. rewrite (H j), K. reflexivity. Qed.

(** Compatibility with identities for [cone_comp]. *)

(** [cone_comp] 与恒等的相容性。 *)

Lemma cone_comp_id {J C : Cat} {D : Fct J C} {X} (κ : X ⇒Δ D)
  : κ ∘Cone id ≈N κ.
Proof. intros j. apply comp_id_r. Qed.

(** Associativity law for [cone_comp]. *)

(** [cone_comp] 结合律。 *)

Lemma cone_comp_assoc {J C : Cat} {D : Fct J C} {X Y Z}
    (κ : X ⇒Δ D) (f : Hom Y X) (g : Hom Z Y)
  : (κ ∘Cone f) ∘Cone g ≈N κ ∘Cone (f ∘ g).
Proof. intros j. apply comp_assoc. Qed.

(** Apply a functor to the apex and every leg of a cone. *)

(** 将函子作用于锥的顶点及每条腿。 *)

Program Definition MapCone {J C E : Cat} (F : Fct C E)
    {D : Fct J C} {X : @Ob C} (κ : X ⇒Δ D)
  : F X ⇒Δ (F ∘F D)
  :=
  {|nt j := fmap F (κ j)
  |}.
Next Obligation.
  rewrite comp_id_r, <- (functor_comp C E F).
  apply functor_fmap_proper.
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_r in H. exact H.
Qed.

(** Cone morphisms compare the apex maps, retaining commutativity witnesses
    without comparing those witnesses. *)

(** 锥态射只比较顶点映射，保留交换性见证而不比较见证本身。 *)

Definition ConeOb {J C : Cat} (D : Fct J C)
  := ∃ X : @Ob C, X ⇒Δ D.
(** An apex map making all cone triangles commute. *)

(** 使所有锥三角形交换的顶点映射。 *)

Definition ConeMap {J C : Cat} {D : Fct J C} (κ μ : ConeOb D)
  := ∃ f : Hom κ.1 μ.1, μ.2 ∘Cone f ≈N κ.2.

(** The category of cones, comparing morphisms by their apex maps. *)

(** 以顶点映射相等比较态射的锥范畴。 *)

Program Definition ConeCat {J C : Cat} (D : Fct J C)
  : Cat
  :=
  {|Ob := ConeOb D
  ; HomSet κ μ :=
      {|carrier := ConeMap κ μ
      ; carrier_equiv f g := f.1 ≈ g.1
      |}
  ; id κ := (id; _)
  ; comp κ μ ν g f := (g.1 ∘ f.1; _)
  |}.
Next Obligation.
  split.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h H K. transitivity g.1; assumption.
Defined.
Next Obligation. apply cone_comp_id. Defined.
Next Obligation.
  rewrite <- cone_comp_assoc, g.2, f.2. reflexivity.
Defined.
Next Obligation. intros f f' H g g' K. cbn in *. rewrite H, K. reflexivity. Qed.
Next Obligation. apply comp_id_r. Qed.
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_assoc. Qed.

(** Forget a cone to its apex and a cone morphism to its apex map. *)

(** 将锥及锥态射分别忘却为顶点及顶点映射。 *)

Program Definition ConeApexF {J C : Cat} (D : Fct J C)
  : Fct (ConeCat D) C
  :=
  {|F0 κ := κ.1
  ; F1 κ μ f := f.1
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
