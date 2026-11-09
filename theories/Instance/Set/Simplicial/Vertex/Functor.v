From Cats Require Export
  Instance.Set.Vertex.Functor
  Instance.Set.Simplicial.Vertex.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Yoneda.

(** * The Vertex Nerve on Transport-Preserving Functors

    Postcomposition acts degreewise on labelled diagrams. Preservation of
    transport makes this action respectful; associativity gives naturality
    with respect to every simplex operator. *)

(** * 顶点 nerve 在保运输函子上的作用

    后复合逐维作用于带标签图式。保持运输保证此作用保相等；结合律给出它对每个
    单纯算子的自然性。 *)

(** A transport-preserving functor induces a simplicial map. Both nerves
    use common value sizes; their native object and hom sizes stay separate. *)

(** 保运输函子诱导单纯映射。两个 nerve 使用共同值大小，其原生对象及 Hom 大小
    仍保持独立。 *)

Program Definition VertexNerveN@{u p +} {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D} (F : T →ᵥ U)
  : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U)
  :=
  {|nt n := (vertex_diagram_postcomp_resp (J := [Ord n]) F)^↑S
  |}.
Next Obligation.
  intros [P]. refine {|lower := _
                     |}.
  exists (λ i, reflexivity (F (P (f i)) : Y)). intros i j a.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Prescribed natural-isomorphism comparisons induce equal simplicial
    maps, in pointwise specified simplex equality. *)

(** 指定自然同构比较诱导相等的单纯映射，其相等为逐点指定单形相等。 *)

Global Instance vertex_nerve_proper@{u p +}
    {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
  : Proper (VertexFunctorEq ==>
      @NatEq _ _
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(U)))
      (@VertexNerveN X Y C D T U).
Proof.
  intros F G H n [P]. refine {|lower := _
                            |}.
  exact (vertex_diagram_postcomp_proper F G H P).
Defined.

(** The forward map for the future full-faithfulness comparison is a
    respectful map between the native hom-setoids. No inverse is claimed. *)

(** 后续全忠实比较的前向映射是原生态射广集间的保相等映射；此处尚未断言其逆。 *)

Program Definition vertex_nerve_resp@{u p +} {X Y : SetC} {C D : Cat}
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D)
  : VertexFunctorS T U →r Nat_SetS
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(U))
  :=
  {|func := VertexNerveN
  |}.

(** Identity functors induce identity simplicial maps. *)

(** 恒等函子诱导恒等单纯映射。 *)

Lemma vertex_nerve_id@{u p +} {X : SetC} {C : Cat}
    (T : Functor (EqGpd X) C)
  : (VertexNerveN (VertexIdF T) :
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ _) ≈N idN.
Proof.
  intros n [P]. refine {|lower := _
                       |}.
  exists (λ i, reflexivity (P i : X)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Composition of transport-preserving functors induces vertical
    composition of simplicial maps, with no equality of functor records. *)

(** 保运输函子的复合诱导单纯映射的垂直复合，不要求函子记录相等。 *)

Lemma vertex_nerve_comp@{u p +} {X Y Z : SetC} {C D E : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
    {V : Functor (EqGpd Z) E} (G : U →ᵥ V) (F : T →ᵥ U)
  : (VertexNerveN (G ∘Fᵥ F) :
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(V)) ≈N
      (VertexNerveN G ∘Nv VertexNerveN F).
Proof.
  intros n [P]. refine {|lower := _
                       |}.
  exists (λ i, reflexivity (G (F (P i)) : Z)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.
