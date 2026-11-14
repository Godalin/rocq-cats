From Cats Require Export
  Cat.Shape.Discrete
  Cat.Diagram.Free.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Discrete Diagrams *)

(** * 离散图式 *)

(** Assign objects to a graph with no generating edges. *)

(** 为无生成边的图赋予对象。 *)

Program Definition DiscreteGraphMap {C : Cat} {V : Type} (D : V → @Ob C)
  : DiscreteGraph V →G UnderlyingGraph C
  :=
  {|vertex_map := D
  ; edge_map x y :=
      {|func e := match e with end
      |}
  |}.
Next Obligation. intros []. Qed.

(** Extend an object family to a discrete diagram. *)

(** 将对象族延拓为离散图式。 *)

Definition DiscreteF {C : Cat} {V : Type} (D : V → @Ob C)
  : Fct (DiscreteCat V) C
  := FreeF (DiscreteGraphMap D).

(** Every discrete diagram is naturally isomorphic to the canonical diagram
    on its object family. The comparison has identity components. *)

(** 每个离散图式都自然同构于其对象族的规范图式；比较的分量为恒等。 *)

Definition discrete_functor_nat_iso {C : Cat} {I : Type}
    (D : Fct (DiscreteCat I) C)
  : DiscreteF (λ i, D i) ≅N D.
Proof.
  exists (@FreeN (DiscreteGraph I) C (DiscreteF (λ i, D i)) D
    (λ _, id) (λ x y e, match e with end)).
  intros i. exists id. split; apply comp_id_l.
Defined.

(** An arbitrary family of legs gives a cone on a discrete diagram. *)

(** 任意锥腿族给出离散图式上的锥。 *)

Definition DiscreteCone {C : Cat} {V : Type} {D : Fct (DiscreteCat V) C}
    {X : @Ob C} (κ : ∀ v, Hom X (D v))
  : X ⇒Δ D.
Proof. refine (FreeCone κ _). intros x y []. Defined.

(** False is the left endpoint and true is the right endpoint. *)

(** [false] 是左端点，[true] 是右端点。 *)

Definition PairDiagram {C : Cat} (X Y : @Ob C)
  : Fct PairShape C
  := DiscreteF (λ b : bool, if b then Y else X).

Notation "'⟨' X ',' Y '⟩D'" := (PairDiagram X Y) : cat_scope.

(** The cone determined by two maps with a common domain. *)

(** 由两条同定义域映射确定的锥。 *)

Definition PairCone {C : Cat} {X Y P : @Ob C} (p : Hom P X) (q : Hom P Y)
  : P ⇒Δ ⟨X, Y⟩D
  := @DiscreteCone C bool (PairDiagram X Y) P
    (λ b : bool, if b as v return Hom P (if v then Y else X)
    then q else p).

Notation "'⟨' p ',' q '⟩Cone'" := (PairCone p q) : cat_scope.

(** * Empty and Single-Object Diagrams *)

(** * 空图式与单对象图式 *)

(** The diagram on the empty shape. *)

(** 空形状上的图式。 *)

Definition EmptyDiagram (C : Cat)
  : Fct EmptyShape C
  := DiscreteF (λ x : Empty_set, match x with end).

(** The cone with no legs on an empty diagram. *)

(** 空图式上没有锥腿的锥。 *)

Definition EmptyCone {C : Cat} {D : Fct EmptyShape C} (X : @Ob C)
  : X ⇒Δ D
  := DiscreteCone (λ x : Empty_set, match x with end).

(** The discrete one-object diagram with the specified value. *)

(** 取指定值的离散单对象图式。 *)

Definition PointDiagram {C : Cat} (X : @Ob C)
  : Fct PointShape C
  := DiscreteF (λ _ : unit, X).
