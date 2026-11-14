From Cats Require Export
  Cat.Induced
  Instance.Set.Groupoid.
From Cats Require Import
  Instance.Set.Functor.

(** * Diagrams with Specified Vertex Transport

    An object action [T : Fct (EqGpd X) C] selects objects of C and
    coherent transport along the specified equality of X. Diagrams take
    values in the induced category on X. Their equality requires squares
    with these transports, rather than arbitrary vertex isomorphisms.
    This is an equality of vertex-labelled data, not a replacement for
    natural-isomorphism comparison of general functors. *)

(** * 具有指定顶点运输的图式

    对象作用 [T : Fct (EqGpd X) C] 选定 C 中的对象，并沿 X 的指定相等
    提供相干运输。图式取值于 X 上的诱导范畴；其相等要求指定运输构成交换方块，
    不允许任意顶点同构。这是带顶点标签的数据相等，不替代一般函子的自然同构比较。 *)

Section VertexObjects.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C).

(** The underlying category retains X as its objects and C's hom-setoids. *)

(** 底层范畴以 X 为对象，并保留 C 的 Hom 广集。 *)

Definition VertexCat
  : Cat
  := InducedCat X T.

(** Object equality acts by the chosen functor, with no native equality
    requirement on objects or on equality witnesses. *)

(** 对象相等通过选定函子作用，不要求对象或相等见证的原生相等。 *)

Definition vertex_transport {x y : X} (p : x ≈S y)
  : (@Hom VertexCat) x y
  := fmap T p.

End VertexObjects.

Notation "T '⟦' p '⟧Ob'" := (vertex_transport T p)
  (at level 8, left associativity) : hom_scope.

(** ** Equality of Labelled Vertex Diagrams

    Fix the presentation [T] and its coherent transport along equality in [X].
    Use these transports to compare labelled diagrams and prove their equality
    and comparison laws. *)

(** ** 带标签顶点图式的相等

    固定呈现 [T] 及其沿 [X] 中相等的相干运输，用这些运输比较带标签图式，并证明相等与比较的定律。 *)

Section VertexDiagrams.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C).

(** Parallel equality witnesses have equal transport arrows. *)

(** 平行相等见证的运输箭头相等。 *)

Lemma vertex_transport_witness_independent {x y : X} (p q : x ≈S y)
  : T⟦p⟧Ob ≈ T⟦q⟧Ob.
Proof. exact (@functor_fmap_proper _ _ T x y p q tt). Defined.

(** Every reflexive witness acts as an identity. *)

(** 每个自反见证均作用为恒等。 *)

Lemma vertex_transport_id {x : X} (p : x ≈S x)
  : T⟦p⟧Ob ≈ id.
Proof.
  transitivity (fmap T (@Cats.Cat.Core.id (EqGpd X) x)).
  - apply vertex_transport_witness_independent.
  - exact (@functor_id _ _ T x).
Defined.

(** Any composite witness gives the composite of its transports. *)

(** 任意复合见证的运输等于运输的复合。 *)

Lemma vertex_transport_comp {x y z : X}
    (p : x ≈S y) (q : y ≈S z) (r : x ≈S z)
  : T⟦r⟧Ob ≈ T⟦q⟧Ob ∘ T⟦p⟧Ob.
Proof.
  transitivity (fmap T (@comp (EqGpd X) x y z q p)).
  - apply vertex_transport_witness_independent.
  - exact (@functor_comp _ _ T x y z q p).
Defined.

(** Opposite equality witnesses give inverse transports. *)

(** 反向相等见证给出互逆运输。 *)

Lemma vertex_transport_inv {x y : X} (p : x ≈S y) (q : y ≈S x)
  : T⟦q⟧Ob ∘ T⟦p⟧Ob ≈ id.
Proof.
  transitivity T⟦transitivity p q⟧Ob.
  - symmetry. apply vertex_transport_comp.
  - apply vertex_transport_id.
Defined.

(** Equality consists of vertex equalities and commutative arrow squares.
    Its witnesses remain Type-valued; no proof fields are compared. *)

(** 相等由顶点相等和箭头交换方块组成；见证保留在 Type 中，不比较证明字段。 *)

Definition VertexDiagramEq {J : Cat} (F G : Fct J (VertexCat T))
  : Type
  := ∃ e : ∀ j, (F j : X) ≈S G j,
      ∀ i j (f : (@Hom J) i j),
        T⟦e j⟧Ob ∘ fmap F f ≈ fmap G f ∘ T⟦e i⟧Ob.

(** Vertex-diagram equality is an equivalence by coherent transport. *)

(** 指定运输的相干性使顶点图式相等构成等价关系。 *)

Global Instance VertexDiagramEq_Equivalence {J : Cat}
  : Equivalence (@VertexDiagramEq J).
Proof.
  split.
  - intros F. exists (λ j, reflexivity (F j : X)). intros i j f.
    rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
  - intros F G [e H].
    assert (p : ∀ j, (G j : X) ≈S F j).
    { intros j. symmetry. exact (e j). }
    exists p. intros i j f.
    transitivity (T⟦p j⟧Ob ∘ (fmap G f ∘ T⟦e i⟧Ob) ∘ T⟦p i⟧Ob).
    + rewrite !comp_assoc, vertex_transport_inv, comp_id_r.
      reflexivity.
    + rewrite <- (H i j f), <- !comp_assoc, vertex_transport_inv,
        comp_id_l. reflexivity.
  - intros F G H [e E] [d D].
    assert (r : ∀ j, (F j : X) ≈S H j).
    { intros j. transitivity (G j : X); [exact (e j) | exact (d j)]. }
    exists r. intros i j f.
    rewrite (vertex_transport_comp (e j) (d j) (r j)), comp_assoc,
      (E i j f), <- comp_assoc, (D i j f), comp_assoc.
    apply comp_proper; [reflexivity |].
    symmetry. apply vertex_transport_comp.
Defined.

(** A natural comparison represents labelled equality when its components
    are the specified vertex transports. *)

(** 自然比较的分量若等于指定顶点运输，就给出带标签的相等。 *)

Definition vertex_diagram_comparison {J : Cat}
    {F G : Fct J (VertexCat T)} (e : ∀ j, (F j : X) ≈S G j)
    (α : F ⇒ G) (H : ∀ j, α j ≈ T⟦e j⟧Ob)
  : VertexDiagramEq F G.
Proof.
  exists e. intros i j f. rewrite <- (H i), <- (H j).
  apply nt_naturality.
Defined.

(** Labelled diagrams form a setoid. Objects, homs, and the two equality
    relations keep their own native universe levels. *)

(** 带标签的图式组成广集；对象、Hom 以及两种相等关系保留各自的原生宇宙层级。 *)

Program Definition VertexDiagramS (J : Cat)
  : SetC
  :=
  {|carrier := Fct J (VertexCat T)
  ; carrier_equiv := VertexDiagramEq
  ; carrier_setoid := VertexDiagramEq_Equivalence
  |}.

(** Forgetting vertex labels yields an ordinary natural isomorphism. *)

(** 忘却顶点标签得到通常的自然同构。 *)

Program Definition vertex_diagram_iso {J : Cat}
    {F G : Fct J (VertexCat T)} (e : VertexDiagramEq F G)
  : F ≅N G
  := ({|nt j := T⟦e.1 j⟧Ob
      |}; _).
Next Obligation. exact (e.2 _ _ f). Defined.
Next Obligation.
  intros j. assert (p : (G j : X) ≈S F j) by (symmetry; exact (e.1 j)).
  exists T⟦p⟧Ob.
  split; apply vertex_transport_inv.
Defined.

(** Restriction preserves vertex equalities and their squares. *)

(** 限制保留顶点相等及其交换方块。 *)

Program Definition vertex_diagram_precomp_resp {I J : Cat}
    (Q : Fct I J)
  : VertexDiagramS J →r VertexDiagramS I
  :=
  {|func F := F ∘F Q
  |}.
Next Obligation.
  intros F G [e H]. exists (λ i, e (Q i)).
  intros i j f. exact (H (Q i) (Q j) (fmap Q f)).
Defined.

(** Forgetting labels is respectful into the ambient functor setoid. *)

(** 忘却标签保持进入环境函子广集的相等。 *)

Program Definition vertex_diagram_forget_resp {J : Cat}
  : VertexDiagramS J →r FctS J C
  :=
  {|func F := InducedInclusionF X T ∘F F
  |}.
Next Obligation.
  intros F G e. apply CompF_proper; [reflexivity |].
  exact (vertex_diagram_iso e).
Defined.

End VertexDiagrams.
