From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Wedges of Mixed-Variance Bifunctors *)

(** * 混合变元双函子的楔 *)

(** A wedge has a fixed apex and diagonal legs. For an arrow [f : X → Y],
    the two legs agree after mapping into [F (X,Y)]. This special case of
    dinaturality suffices for ends; no composition of arbitrary dinatural
    transformations is assumed. *)

(** 楔具有固定顶点及对角腿。对于箭头 [f : X → Y]，两条腿映射到 [F (X,Y)] 后
    相等。这种特殊的双自然性足以定义 end，不假定任意双自然变换可复合。 *)

Class Wedge {C D : Cat} (F : Fct ((C^op) ×C C) D) (W : @Ob D)
  :=
  (** The primary view is the family of arrows to diagonal values. *)

  (** 主视图是指向对角值的箭头族。 *)

  { wedge_leg (X : @Ob C) :> Hom W (F (X, X))

  (** The covariant and contravariant actions agree on the two legs. *)

  (** 协变和逆变作用将两条腿映成相等的箭头。 *)

  ; wedge_comm {X Y : @Ob C} (f : Hom X Y)
    : fmap F (X := (X, X)) (Y := (X, Y)) (id, f) ∘ wedge_leg X
      ≈ fmap F (X := (Y, Y)) (Y := (X, Y)) (f, id) ∘ wedge_leg Y
  }.

Arguments wedge_leg {_ _ _ _} _ _.
Arguments wedge_comm {_ _ _ _} _ {_ _} _.

(** Compare only the legs, using the specified equality in the codomain. *)

(** 仅用值域的指定相等比较各条腿。 *)

Definition WedgeEq {C D : Cat} {F : Fct ((C^op) ×C C) D} {W}
    (κ μ : Wedge F W)
  := ∀ X, κ X ≈ μ X.

Infix "≈W" := WedgeEq (at level 50, no associativity) : cat_scope.

(** Pointwise equality of wedge legs is an equivalence relation. *)

(** 楔腿的逐点相等是等价关系。 *)

Global Instance WedgeEq_Equivalence {C D F W}
  : Equivalence (@WedgeEq C D F W).
Proof.
  split.
  - intros κ X. reflexivity.
  - intros κ μ H X. symmetry. exact (H X).
  - intros κ μ ν H K X. transitivity (μ X); [apply H | apply K].
Defined.

(** Precompose all legs by an apex map. *)

(** 用顶点映射预合成全部腿。 *)

Program Definition wedge_comp {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {W V : @Ob D}
    (κ : Wedge F W) (f : Hom V W)
  : Wedge F V
  :=
  {|wedge_leg X := κ X ∘ f
  |}.
Next Obligation.
  rewrite <- !comp_assoc, (wedge_comm κ f0). reflexivity.
Qed.

Infix "∘Wedge" := wedge_comp
  (at level 40, left associativity) : cat_scope.

(** Precomposition respects both wedge equality and arrow equality. *)

(** 预合成保持楔相等和箭头相等。 *)

Global Instance wedge_comp_proper {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {W V : @Ob D}
  : Proper (WedgeEq ==> @HomEq[V, W] ==> WedgeEq)
      (@wedge_comp C D F W V).
Proof. intros κ μ H f g K X. cbn. rewrite (H X), K. reflexivity. Qed.

(** Precomposing by the identity recovers the original wedge. *)

(** 用恒等预合成恢复原楔。 *)

Lemma wedge_comp_id {C D : Cat} {F : Fct ((C^op) ×C C) D} {W}
    (κ : Wedge F W)
  : κ ∘Wedge id ≈W κ.
Proof. intros X. apply comp_id_r. Qed.

(** Successive precomposition agrees with composition of the apex maps. *)

(** 连续预合成与顶点映射的复合相容。 *)

Lemma wedge_comp_assoc {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {W V U}
    (κ : Wedge F W) (f : Hom V W) (g : Hom U V)
  : (κ ∘Wedge f) ∘Wedge g ≈W κ ∘Wedge (f ∘ g).
Proof. intros X. apply comp_assoc. Qed.

(** An ordinary natural transformation maps wedges to wedges. Only its
    naturality and the original wedge equation are needed. *)

(** 普通自然变换将楔映为楔，仅需其自然性及原楔方程。 *)

Program Definition wedge_map {C D : Cat}
    {F G : Fct ((C^op) ×C C) D} {W} (α : F ⇒ G)
    (κ : Wedge F W)
  : Wedge G W
  :=
  {|wedge_leg X := α (X, X) ∘ κ X
  |}.
Next Obligation.
  rewrite <- !comp_assoc, <- !nt_naturality, !comp_assoc,
    (wedge_comm κ f). reflexivity.
Qed.

(** Mapping wedges respects the transformation and every leg. *)

(** 映射楔保持自然变换及每条腿的相等。 *)

Global Instance wedge_map_proper {C D : Cat}
    {F G : Fct ((C^op) ×C C) D} {W}
  : Proper (NatEq ==> WedgeEq ==> WedgeEq) (@wedge_map C D F G W).
Proof.
  intros α β H κ μ K X. cbn. rewrite (H (X, X)), (K X). reflexivity.
Qed.

(** Objects of the wedge category retain the apex and its wedge. *)

(** 楔范畴的对象保留顶点及其楔。 *)

Definition WedgeOb {C D : Cat} (F : Fct ((C^op) ×C C) D)
  := ∃ W : @Ob D, Wedge F W.

(** A wedge morphism retains an apex map and commuting triangles. *)

(** 楔态射保留顶点映射及交换三角形。 *)

Definition WedgeMap {C D : Cat} {F : Fct ((C^op) ×C C) D}
    (κ μ : WedgeOb F)
  := ∃ f : Hom κ.1 μ.1, μ.2 ∘Wedge f ≈W κ.2.

(** Wedge morphisms are compared by their apex maps, without equality of
    the retained commutativity witnesses. *)

(** 楔态射按顶点映射比较，不比较保留的交换性见证。 *)

Program Definition WedgeCat {C D : Cat} (F : Fct ((C^op) ×C C) D)
  : Cat
  :=
  {|Ob := WedgeOb F
  ; HomSet κ μ :=
      {|carrier := WedgeMap κ μ
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
Next Obligation. apply wedge_comp_id. Defined.
Next Obligation.
  rewrite <- wedge_comp_assoc, g.2, f.2. reflexivity.
Defined.
Next Obligation. intros f f' H g g' K. cbn in *. rewrite H, K. reflexivity. Qed.
Next Obligation. apply comp_id_r. Qed.
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_assoc. Qed.

(** Forget the wedge and retain its apex and apex maps. *)

(** 忘掉楔，保留顶点及顶点映射。 *)

Program Definition WedgeApexF {C D : Cat} (F : Fct ((C^op) ×C C) D)
  : Fct (WedgeCat F) D
  :=
  {|F0 κ := κ.1
  ; F1 κ μ f := f.1
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
