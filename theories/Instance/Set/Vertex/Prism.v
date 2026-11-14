From Cats Require Export
  Instance.Set.Vertex.Functor
  Cat.Diagram.Prism.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Prisms Respect Specified Vertex Transport

    Fix label setoids [X], [Y], object actions [T], [U], two
    transport-preserving functors [F], [G] and a transformation [α : F ⇒ G].
    The following lemmas compare prism arrows and labelled diagrams.
    Naturality along the chosen transport arrows makes an ordinary natural
    transformation compatible with labelled-diagram equality. No additional
    equality of its component family is required. *)

(** * 棱柱保持指定顶点运输

    固定标签广集 [X]、[Y]，对象作用 [T]、[U]，两个保运输函子 [F]、[G]
    以及自然变换 [α : F ⇒ G]。接下来的引理比较棱柱箭头与带标签图式。
    沿选定运输箭头的自然性，使普通自然变换与带标签图式相等相容，
    无须额外要求其分量族具有原生相等。 *)

Section Prisms.
Context {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (α : F ⇒ G).

(** The prism carries a source transport square to a target transport
    square, for any parallel witnesses of the endpoint labels. *)

(** 棱柱将源运输方块送到目标运输方块，允许端点标签使用任意平行相等见证。 *)

Lemma vertex_prism_square {x x' y y' : X} {i j : Ordinal 1}
    (p : x ≈S x') (q : y ≈S y')
    (f : (@Hom (VertexCat T)) x y)
    (g : (@Hom (VertexCat T)) x' y') (a : (@Hom [Ord 1]) i j)
    (r : (NaturalPrismF α (x, i) : Y) ≈S
      NaturalPrismF α (x', i))
    (s : (NaturalPrismF α (y, j) : Y) ≈S
      NaturalPrismF α (y', j))
    (H : T⟦q⟧Ob ∘ f ≈ g ∘ T⟦p⟧Ob)
  : U⟦s⟧Ob ∘
      fmap (NaturalPrismF α) (X := (x, i)) (Y := (y, j)) (f, a) ≈
      fmap (NaturalPrismF α) (X := (x', i)) (Y := (y', j)) (g, a) ∘
        U⟦r⟧Ob.
Proof.
  assert (K : ∀ A : T →ᵥ U,
    fmap A T⟦q⟧Ob ∘ fmap A f ≈ fmap A g ∘ fmap A T⟦p⟧Ob).
  { intros A. transitivity (fmap A (T⟦q⟧Ob ∘ f)).
    - symmetry. exact (@functor_comp _ _ A x y y' T⟦q⟧Ob f).
    - transitivity (fmap A (g ∘ T⟦p⟧Ob)).
      + exact (@functor_fmap_proper _ _ A x y' _ _ H).
      + exact (@functor_comp _ _ A x x' y' g T⟦p⟧Ob). }
  destruct i as [[] | [[] | []]], j as [[] | [[] | []]];
    cbn in *; try solve [destruct a].
  - rewrite <- (vertex_functor_transport_witness F p r),
      <- (vertex_functor_transport_witness F q s), !comp_id_r.
    exact (K F).
  - rewrite <- (vertex_functor_transport_witness F p r),
      <- (vertex_functor_transport_witness G q s).
    change (@HomEq (VertexCat U) (F x) (G y')
      (fmap G T⟦q⟧Ob ∘ (fmap G f ∘ α x))
      ((fmap G g ∘ α x') ∘ fmap F T⟦p⟧Ob)).
    rewrite comp_assoc, (nt_naturality α T⟦p⟧Ob), <- !comp_assoc.
    apply (@comp_r (VertexCat U)).
    exact (K G).
  - rewrite <- (vertex_functor_transport_witness G p r),
      <- (vertex_functor_transport_witness G q s), !comp_id_r.
    exact (K G).
Defined.

(** With time fixed, equal source diagrams give equal prism diagrams.
    At a changing time edge the transport square is naturality of [α]. *)

(** 固定时间时，相等的源图式给出相等的棱柱图式；时间改变的边上，
    运输方块来自 [α] 的自然性。 *)

Lemma vertex_prism_diagram_proper {J : Cat}
    (θ : Fct J [Ord 1]) (P Q : Fct J (VertexCat T))
    (H : VertexDiagramEq T P Q)
  : VertexDiagramEq U (PrismDiagramF α P θ) (PrismDiagramF α Q θ).
Proof.
  destruct H as [e H].
  assert (d : ∀ i, (PrismDiagramF α P θ i : Y) ≈S
    PrismDiagramF α Q θ i).
  { intros i. cbn. destruct (θ i) as [[] | [[] | []]]; cbn.
    - exact (vertex_functor_ob_proper F _ _ (e i)).
    - exact (vertex_functor_ob_proper G _ _ (e i)). }
  exists d.
  intros i j a.
  exact (vertex_prism_square (e i) (e j) (fmap P a) (fmap Q a)
    (fmap θ a) (d i) (d j) (H i j a)).
Defined.

End Prisms.

(** Equal natural transformations give the same labelled prism, with
    fixed boundary functors and specified equality of the actual arrows. *)

(** 固定边界函子时，相等自然变换给出相等的带标签棱柱，实际箭头按指定相等比较。 *)

Lemma vertex_prism_transformation_eq {X Y : SetC} {C D J : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (α β : F ⇒ G) (H : α ≈N β)
    (P : Fct J (VertexCat T)) (θ : Fct J [Ord 1])
  : VertexDiagramEq U (PrismDiagramF α P θ) (PrismDiagramF β P θ).
Proof.
  exists (λ i, reflexivity (_ : Y)). intros i j a.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  exact (natural_prism_map_proper α β H (fmap P a) (fmap θ a)).
Defined.

(** Changing only the concrete time positions preserves a prism arrow;
    parallel time arrows compare in the thin ordinal category. *)

(** 只改变具体时间位置保持棱柱箭头；平行时间箭头在薄序数范畴中比较。 *)

Lemma vertex_prism_time_square {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (α : F ⇒ G) {x y : X}
    {i i' j j' : Ordinal 1} (e : i = i') (d : j = j')
    (f : (@Hom (VertexCat T)) x y)
    (a : (@Hom [Ord 1]) i j) (b : (@Hom [Ord 1]) i' j')
    (r : (NaturalPrismF α (x, i) : Y) ≈S NaturalPrismF α (x, i'))
    (s : (NaturalPrismF α (y, j) : Y) ≈S NaturalPrismF α (y, j'))
  : U⟦s⟧Ob ∘
      fmap (NaturalPrismF α) (X := (x, i)) (Y := (y, j)) (f, a) ≈
      fmap (NaturalPrismF α) (X := (x, i')) (Y := (y, j')) (f, b) ∘
        U⟦r⟧Ob.
Proof.
  destruct e, d. rewrite !vertex_transport_id, comp_id_l, comp_id_r.
  exact (@functor_fmap_proper _ _ (NaturalPrismF α) (x, i) (y, j)
    (f, a) (f, b) (reflexivity f, tt)).
Defined.

(** Pointwise equal time positions give equal labelled prisms. Equality
    of ordinal arrows uses their specified thin equality, not record equality. *)

(** 时间位置逐点相等给出相等的带标签棱柱；序数箭头按指定薄相等比较，
    不比较记录的原生相等。 *)

Lemma vertex_prism_time_eq {X Y : SetC} {C D J : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (α : F ⇒ G) (P : Fct J (VertexCat T))
    (θ φ : Fct J [Ord 1]) (H : ∀ i, θ i = φ i)
  : VertexDiagramEq U (PrismDiagramF α P θ) (PrismDiagramF α P φ).
Proof.
  assert (d : ∀ i, (PrismDiagramF α P θ i : Y) ≈S
    PrismDiagramF α P φ i).
  { intros i. cbn. rewrite (H i). reflexivity. }
  exists d. intros i j a.
  exact (vertex_prism_time_square α (H i) (H j) (fmap P a)
    (fmap θ a) (fmap φ a) (d i) (d j)).
Defined.

(** At either constant time, a prism restricts to its corresponding functor. *)

(** 在任一恒定时间处，棱柱限制为相应的端点函子。 *)

Lemma vertex_prism_endpoint {X Y : SetC} {C D J : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (α : F ⇒ G) (P : Fct J (VertexCat T))
    (b : bool)
  : VertexDiagramEq U
      (PrismDiagramF α P
        (ConstF J (C := [Ord 1])
          (if b then fin_next fin_first else fin_first)))
      ((if b then G else F) ∘F P).
Proof.
  destruct b; exists (λ i, reflexivity (_ : Y)); intros i j a;
    cbn; rewrite !vertex_transport_id; cbn;
    repeat first [rewrite comp_id_l | rewrite comp_id_r];
    reflexivity.
Defined.

(** For the identity transformation the arrow part ignores time. This
    statement allows arbitrary parallel reflexive transport witnesses. *)

(** 对恒等自然变换，箭头部分与时间无关；此陈述允许任意平行自反运输见证。 *)

Lemma vertex_prism_id_square {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    (F : T →ᵥ U) {x y : X} {i j : Ordinal 1}
    (f : (@Hom (VertexCat T)) x y) (a : (@Hom [Ord 1]) i j)
    (r : (NaturalPrismF (F := F) idN (x, i) : Y) ≈S F x)
    (s : (NaturalPrismF (F := F) idN (y, j) : Y) ≈S F y)
  : U⟦s⟧Ob ∘ fmap (NaturalPrismF (F := F) idN)
      (X := (x, i)) (Y := (y, j)) (f, a) ≈ fmap F f ∘ U⟦r⟧Ob.
Proof.
  destruct i as [[] | [[] | []]], j as [[] | [[] | []]];
    cbn in *; try solve [destruct a];
    rewrite !vertex_transport_id; cbn;
    repeat first [rewrite comp_id_l | rewrite comp_id_r];
    reflexivity.
Defined.

(** An identity transformation gives the time-independent labelled diagram. *)

(** 恒等自然变换给出与时间无关的带标签图式。 *)

Lemma vertex_prism_id {X Y : SetC} {C D J : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    (F : T →ᵥ U) (P : Fct J (VertexCat T))
    (θ : Fct J [Ord 1])
  : VertexDiagramEq U (PrismDiagramF (F := F) idN P θ) (F ∘F P).
Proof.
  assert (d : ∀ i, (PrismDiagramF (F := F) idN P θ i : Y) ≈S F (P i)).
  { intros i. cbn. destruct (θ i) as [[] | [[] | []]]; reflexivity. }
  exists d. intros i j a.
  exact (vertex_prism_id_square F (fmap P a) (fmap θ a) (d i) (d j)).
Defined.
