From Cats Require Export
  Instance.Set.Vertex.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Functors Preserving Specified Vertex Transport

    A morphism between object presentations is an ordinary functor whose
    object map respects the object setoids and whose arrow map preserves
    their specified transports. Its comparison uses transport squares,
    inherited from labelled diagrams, with no equality of proof fields. *)

(** * 保持指定顶点运输的函子

    对象呈现之间的态射是普通函子，要求对象映射保持对象广集的相等，箭头映射
    保持其指定运输。其比较从带标签图式继承运输方块，不比较证明字段的相等。 *)

(** Expose one underlying functor. Object respectfulness retains equality
    witnesses; the transport law compares arrows in the target hom-setoid. *)

(** 暴露唯一底层函子。对象保相等性保留相等见证；运输律在目标 Hom 广集中比较箭头。 *)

Record VtxFct {X Y : SetC} {C D : Cat}
    (T : Fct (EqGpd X) C) (U : Fct (EqGpd Y) D)
  :=
  { vertex_functor :> Fct (VertexCat T) (VertexCat U)
  ; vertex_functor_ob_proper
    :: Proper (carrier_equiv X ==> carrier_equiv Y) vertex_functor
  ; vertex_functor_transport {x y : X} (p : x ≈S y)
    : fmap vertex_functor T⟦p⟧Ob ≈
        U⟦vertex_functor_ob_proper x y p⟧Ob
  }.

Arguments vertex_functor {_ _ _ _ _ _} _.
Arguments vertex_functor_ob_proper {_ _ _ _ _ _} _ _ _ _.
Arguments vertex_functor_transport {_ _ _ _ _ _} _ {_ _} _.

Notation "T '→ᵥ' U" := (VtxFct T U)
  (at level 99, right associativity) : type_scope.

(** The respectful object-map view is explicit, so the functor remains
    the unique coercion and no competing function path is introduced. *)

(** 保相等对象映射的视图保持显式，从而函子仍为唯一强制转换，不引入竞争函数路径。 *)

Program Definition vertex_functor_ob_resp {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D} (F : T →ᵥ U)
  : X →r Y
  :=
  {|func := F
  ; func_proper := vertex_functor_ob_proper F
  |}.

(** The transport equation holds for every parallel target witness. *)

(** 运输方程对任意平行目标见证均成立。 *)

Lemma vertex_functor_transport_witness {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D} (F : T →ᵥ U)
    {x y : X} (p : x ≈S y) (q : (F x : Y) ≈S F y)
  : fmap F T⟦p⟧Ob ≈ U⟦q⟧Ob.
Proof.
  transitivity U⟦vertex_functor_ob_proper F x y p⟧Ob.
  - exact (vertex_functor_transport F p).
  - apply vertex_transport_witness_independent.
Defined.

(** Identity preserves the specified transport without selecting new data. *)

(** 恒等函子保持指定运输，无需选取新数据。 *)

Program Canonical VertexIdF {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : T →ᵥ T
  :=
  {|vertex_functor := IdF
  |}.
Next Obligation. intros x y p. exact p. Defined.
Next Obligation. apply vertex_transport_witness_independent. Defined.

(** Composition combines ordinary functors and their respectful object
    maps; its transport law follows from the two original laws. *)

(** 复合结合普通函子及其保相等对象映射；运输律由原来的两条运输律导出。 *)

Program Canonical VertexCompF {X Y Z : SetC} {C D E : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {V : Fct (EqGpd Z) E} (G : U →ᵥ V) (F : T →ᵥ U)
  : T →ᵥ V
  :=
  {|vertex_functor := G ∘F F
  |}.
Next Obligation.
  intros x y p.
  exact (vertex_functor_ob_proper G _ _ (vertex_functor_ob_proper F x y p)).
Defined.
Next Obligation.
  transitivity (fmap G U⟦vertex_functor_ob_proper F x y p⟧Ob).
  - apply functor_fmap_proper. exact (vertex_functor_transport F p).
  - apply vertex_functor_transport_witness.
Defined.

Infix "∘Fᵥ" := VertexCompF (at level 40) : cat_scope.

(** Functors compare by the target's specified vertex transports. This
    records a natural isomorphism with prescribed components, and does not
    identify arbitrary naturally isomorphic functors with different labels. *)

(** 函子通过目标的指定顶点运输比较，即分量为指定运输的自然同构；此比较不识别
    标签不同的任意自然同构函子。 *)

Definition VtxFctEq {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    (F G : T →ᵥ U)
  : Type
  := VertexDiagramEq U F G.

(** Equivalence laws are inherited from labelled-diagram comparison. *)

(** 等价律继承带标签图式的比较。 *)

Global Instance VtxFctEq_Equivalence {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
  : Equivalence (@VtxFctEq X Y C D T U).
Proof.
  unfold VtxFctEq. split.
  - intros F. reflexivity.
  - intros F G H. symmetry. exact H.
  - intros F G H K L. transitivity G; assumption.
Defined.

(** The native hom-setoid retains independent carrier and equality sizes. *)

(** 原生态射广集保留相互独立的载体及相等大小。 *)

Program Canonical VtxFctS {X Y : SetC} {C D : Cat}
    (T : Fct (EqGpd X) C) (U : Fct (EqGpd Y) D)
  : SetC
  :=
  {|carrier := T →ᵥ U
  ; carrier_equiv := VtxFctEq
  ; carrier_setoid := VtxFctEq_Equivalence
  |}.

(** Forgetting the prescribed components gives an ordinary natural
    isomorphism of the underlying functors. *)

(** 忘却分量的指定条件，得到底层函子之间的普通自然同构。 *)

Definition vertex_functor_iso {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {F G : T →ᵥ U} (H : VtxFctEq F G)
  : F ≅N G
  := vertex_diagram_iso U H.

(** Postcomposition sends labelled diagrams to labelled diagrams. Its
    respectfulness is precisely where preservation of transport is needed. *)

(** 后复合将带标签图式送到带标签图式；其保相等性正是需要保持运输的地方。 *)

Program Definition vertex_diagram_postcomp_resp {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {J : Cat} (F : T →ᵥ U)
  : VertexDiagramS T J →r VertexDiagramS U J
  :=
  {|func P := F ∘F P
  |}.
Next Obligation.
  intros P Q [e H].
  exists (λ j, vertex_functor_ob_proper F _ _ (e j)).
  intros i j f.
  change (U⟦vertex_functor_ob_proper F _ _ (e j)⟧Ob ∘
      fmap F (fmap P f) ≈
    fmap F (fmap Q f) ∘ U⟦vertex_functor_ob_proper F _ _ (e i)⟧Ob).
  rewrite <- !vertex_functor_transport, <- !functor_comp.
  apply functor_fmap_proper. exact (H i j f).
Defined.

(** Equal functors induce pointwise equal postcomposition maps. *)

(** 相等函子诱导逐点相等的后复合映射。 *)

Global Instance vertex_diagram_postcomp_proper {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D} {J : Cat}
  : Proper (VtxFctEq ==> FunEq)
      (@vertex_diagram_postcomp_resp X Y C D T U J).
Proof.
  intros F G H P.
  exact (@func_proper _ _ (vertex_diagram_precomp_resp U P) F G H).
Defined.

(** Composition respects comparisons in both arguments, using restriction
    for the outer functor and respectful postcomposition for the inner one. *)

(** 复合保持两个参数的比较：外函子使用限制，内函子使用保相等后复合。 *)

Global Instance vertex_comp_proper {X Y Z : SetC} {C D E : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {V : Fct (EqGpd Z) E}
  : Proper (VtxFctEq ==> VtxFctEq ==> VtxFctEq)
      (@VertexCompF X Y Z C D E T U V).
Proof.
  intros G G' H F F' K. unfold VtxFctEq.
  transitivity (G' ∘F F).
  - exact (@func_proper _ _ (vertex_diagram_precomp_resp V F) G G' H).
  - exact (@func_proper _ _ (vertex_diagram_postcomp_resp G') F F' K).
Defined.

(** The left unit law uses identity transports, without record equality. *)

(** 左单位律使用恒等运输，不要求记录相等。 *)

Lemma vertex_comp_id_l {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D} (F : T →ᵥ U)
  : VtxFctEq (VertexIdF U ∘Fᵥ F) F.
Proof.
  exists (λ x, reflexivity (F x : Y)). intros x y f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** The right unit law likewise compares the underlying labelled diagrams. *)

(** 右单位律同样比较底层带标签图式。 *)

Lemma vertex_comp_id_r {X Y : SetC} {C D : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D} (F : T →ᵥ U)
  : VtxFctEq (F ∘Fᵥ VertexIdF T) F.
Proof.
  exists (λ x, reflexivity (F x : Y)). intros x y f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Associativity preserves the prescribed vertex labels and arrow maps. *)

(** 结合律保持指定顶点标签及箭头映射。 *)

Lemma vertex_comp_assoc {W X Y Z : SetC} {B C D E : Cat}
    {S : Fct (EqGpd W) B} {T : Fct (EqGpd X) C}
    {U : Fct (EqGpd Y) D} {V : Fct (EqGpd Z) E}
    (H : U →ᵥ V) (G : T →ᵥ U) (F : S →ᵥ T)
  : VtxFctEq ((H ∘Fᵥ G) ∘Fᵥ F) (H ∘Fᵥ (G ∘Fᵥ F)).
Proof.
  exists (λ x, reflexivity (H (G (F x)) : Z)). intros x y f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.
