From Cats Require Export
  Instance.Set.Vertex.Functor
  Instance.Set.Product.
From Cats Require Import
  Cat.Core
  Cat.Functor.Product
  Cat.Product.Core
  Instance.Set.Isomorphism.

(** * Products of Vertex Presentations

    Labels, arrows and specified transport are paired componentwise.
    The diagram correspondence works for every source category, before
    specializing to ordinal diagrams and the vertex nerve. *)

(** * 顶点呈现的积

    标签、箭头和指定运输逐分量配对。图式对应适用于任意源范畴，然后才特化
    到序数图式及顶点 nerve。 *)

(** The product presentation uses the given transports in each factor. *)

(** 积呈现在每个因子中使用给定的运输。 *)

Program Definition VertexProductObjectsF
    {X : SetC} {Y : SetC} {C : Cat} {D : Cat}
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D)
  : Functor (EqGpd (X ×S Y)) (C ×C D)
  := PairF (T ∘F EqGpdF ({|func := fst
                          |} : (X ×S Y) →r X))
      (U ∘F EqGpdF ({|func := snd
                    |} : (X ×S Y) →r Y)).
Next Obligation. intros [x y] [x' y'] [p q]. exact p. Defined.
Next Obligation. intros [x y] [x' y'] [p q]. exact q. Defined.

(** ** Splitting and Pairing Product Diagrams

    Fix presentations [T] and [U] into [C] and [D]. Construct the projection
    and pairing functors for their product presentation and compare diagram
    setoids by an isomorphism. *)

(** ** 积图式的分拆与配对

    固定取值于 [C]、[D] 的呈现 [T]、[U]，为积呈现构造投影与配对函子，并以同构比较图式广集。 *)

Section Product.
Context {X : SetC} {Y : SetC} {C : Cat} {D : Cat}
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D).

(** Projection preserves labels and their specified transports. *)

(** 投影保持标签及其指定运输。 *)

Program Definition VertexFstF
  : VertexProductObjectsF T U →ᵥ T
  :=
  {|vertex_functor := FstF (VertexCat T) (VertexCat U) ∘F
      InducedProductF X Y T U
  |}.
Next Obligation. intros [x y] [x' y'] [p q]. exact p. Defined.
Next Obligation. apply vertex_transport_witness_independent. Defined.

(** The second projection likewise preserves transport. *)

(** 第二投影同样保持运输。 *)

Program Definition VertexSndF
  : VertexProductObjectsF T U →ᵥ U
  :=
  {|vertex_functor := SndF (VertexCat T) (VertexCat U) ∘F
      InducedProductF X Y T U
  |}.
Next Obligation. intros [x y] [x' y'] [p q]. exact q. Defined.
Next Obligation. apply vertex_transport_witness_independent. Defined.

(** Pair compatible presentation maps by pairing their underlying functors. *)

(** 通过配对底层函子，配对同源呈现映射。 *)

Program Definition VertexPairF {Z : SetC} {E : Cat}
    {V : Functor (EqGpd Z) E} (F : V →ᵥ T) (G : V →ᵥ U)
  : V →ᵥ VertexProductObjectsF T U
  :=
  {|vertex_functor := InducedProductInvF X Y T U ∘F PairF F G
  |}.
Next Obligation.
  intros x y p. split; apply vertex_functor_ob_proper; exact p.
Defined.
Next Obligation. split; apply vertex_functor_transport_witness. Defined.

(** Split a labelled diagram by respectful postcomposition with projections. *)

(** 通过与投影作保相等后复合，拆分带标签图式。 *)

Program Definition vertex_diagram_product_split_resp (J : Cat)
  : VertexDiagramS (VertexProductObjectsF T U) J →r
      (VertexDiagramS T J ×S VertexDiagramS U J)
  :=
  {|func F := (vertex_diagram_postcomp_resp VertexFstF F,
      vertex_diagram_postcomp_resp VertexSndF F)
  |}.
Next Obligation.
  intros F G H. split.
  - exact (@func_proper _ _ (vertex_diagram_postcomp_resp VertexFstF) F G H).
  - exact (@func_proper _ _ (vertex_diagram_postcomp_resp VertexSndF) F G H).
Defined.

(** Pair arbitrary labelled diagrams, with paired equality witnesses. *)

(** 配对任意带标签图式，并配对其相等见证。 *)

Program Definition vertex_diagram_product_pair_resp (J : Cat)
  : (VertexDiagramS T J ×S VertexDiagramS U J) →r
      VertexDiagramS (VertexProductObjectsF T U) J
  :=
  {|func FG := InducedProductInvF X Y T U ∘F PairF (fst FG) (snd FG)
  |}.
Next Obligation.
  intros [F G] [F' G'] [[e H] [d K]].
  exists (λ i, (e i, d i)). intros i j f.
  split; [exact (H i j f) | exact (K i j f)].
Defined.

(** Native diagram splitting and pairing are mutually inverse in labelled
    equality. No equality of functions or functor laws is needed. *)

(** 原生图式的拆分及配对在带标签相等下互逆，无需函数或函子定律的相等。 *)

Definition vertex_diagram_product_iso (J : Cat)
  : VertexDiagramS (VertexProductObjectsF T U) J ≅[SetCat]
      (VertexDiagramS T J ×S VertexDiagramS U J).
Proof.
  exists (vertex_diagram_product_split_resp J),
    (vertex_diagram_product_pair_resp J). split.
  - intros F.
    assert (e : ∀ i, ((fst (F i), snd (F i)) : X ×S Y) ≈S F i).
    { intros i. destruct (F i). split; reflexivity. }
    pose (e1 := λ i, vertex_functor_ob_proper VertexFstF _ _ (e i)).
    pose (e2 := λ i, vertex_functor_ob_proper VertexSndF _ _ (e i)).
    exists e. intros i j f. split.
    + change (T⟦e1 j⟧Ob ∘ fst (fmap F f) ≈
        fst (fmap F f) ∘ T⟦e1 i⟧Ob).
      rewrite !vertex_transport_id. transitivity (fst (fmap F f)).
      * exact (@comp_id_l C _ _ (fst (fmap F f))).
      * symmetry. exact (@comp_id_r C _ _ (fst (fmap F f))).
    + change (U⟦e2 j⟧Ob ∘ snd (fmap F f) ≈
        snd (fmap F f) ∘ U⟦e2 i⟧Ob).
      rewrite !vertex_transport_id. transitivity (snd (fmap F f)).
      * exact (@comp_id_l D _ _ (snd (fmap F f))).
      * symmetry. exact (@comp_id_r D _ _ (snd (fmap F f))).
  - intros [F G]. split.
    + exists (λ i, reflexivity (F i : X)). intros i j f.
      rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
    + exists (λ i, reflexivity (G i : Y)). intros i j f.
      rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Pairing preserves prescribed comparisons in both presentation maps. *)

(** 配对保持两个呈现映射的指定比较。 *)

Global Instance vertex_pair_proper {Z : SetC} {E : Cat}
    {V : Functor (EqGpd Z) E}
  : Proper (VertexFunctorEq ==> VertexFunctorEq ==> VertexFunctorEq)
      (VertexPairF (V := V)).
Proof.
  intros F F' H G G' K.
  exact (@func_proper _ _
    (vertex_diagram_product_pair_resp (VertexCat V))
    ((F : Functor (VertexCat V) (VertexCat T)),
     (G : Functor (VertexCat V) (VertexCat U)))
    ((F' : Functor (VertexCat V) (VertexCat T)),
     (G' : Functor (VertexCat V) (VertexCat U))) (H, K)).
Defined.

End Product.

(** Independent presentation maps act on both factors. *)

(** 独立呈现映射作用于两个因子。 *)

Definition VertexProductF
    {X : SetC} {Y : SetC} {X' : SetC} {Y' : SetC}
    {C : Cat} {D : Cat} {C' : Cat} {D' : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
    {T' : Functor (EqGpd X') C'} {U' : Functor (EqGpd Y') D'}
    (F : T →ᵥ T') (G : U →ᵥ U')
  : VertexProductObjectsF T U →ᵥ VertexProductObjectsF T' U'
  := VertexPairF T' U' (F ∘Fᵥ VertexFstF T U) (G ∘Fᵥ VertexSndF T U).

(** Independent products preserve comparison of both factors. *)

(** 独立积保持两个因子的比较。 *)

Global Instance vertex_product_proper
    {X : SetC} {Y : SetC} {X' : SetC} {Y' : SetC}
    {C : Cat} {D : Cat} {C' : Cat} {D' : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
    {T' : Functor (EqGpd X') C'} {U' : Functor (EqGpd Y') D'}
  : Proper (VertexFunctorEq ==> VertexFunctorEq ==> VertexFunctorEq)
      (@VertexProductF X Y X' Y' C D C' D' T U T' U').
Proof.
  intros F F' H G G' K. apply vertex_pair_proper;
    apply vertex_comp_proper; try reflexivity; assumption.
Defined.
