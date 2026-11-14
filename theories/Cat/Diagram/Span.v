From Cats Require Export
  Cat.Shape.Core
  Cat.Diagram.Free.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Cospan Diagrams *)

(** * 余跨度图式 *)

(** Assign the two source objects and the common target to cospan vertices. *)

(** 将两个源对象及共同目标赋给余跨度顶点。 *)

Definition CospanOb {C : Cat} (X Y Z : @Ob C) (v : CospanVertex)
  : @Ob C
  := match v with
  | cospan_left => X
  | cospan_right => Y
  | cospan_tip => Z
  end.

(** Assign each cospan generator its corresponding arrow respectfully. *)

(** 将余跨度生成边保相等地送到对应箭头。 *)

Program Definition cospan_edge_resp {C : Cat} {X Y Z : @Ob C}
    (f : Hom X Z) (g : Hom Y Z) (x y : CospanVertex)
  : @EdgeSet CospanGraph x y →r HomSet (CospanOb X Y Z x) (CospanOb X Y Z y)
  :=
  {|func e := _
  |}.
Next Obligation.
  destruct x, y; cbn in *; destruct e; assumption.
Defined.
Next Obligation.
  intros e e' H. destruct x, y; cbn in *; destruct e, e'; reflexivity.
Defined.

(** The graph interpretation of a pair of arrows with common target. *)

(** 共同目标的两条箭头对应的图解释。 *)

Program Definition CospanGraphMap {C : Cat} {X Y Z : @Ob C}
    (f : Hom X Z) (g : Hom Y Z)
  : CospanGraph →G UnderlyingGraph C
  :=
  {|vertex_map := CospanOb X Y Z
  ; edge_map x y := cospan_edge_resp f g x y
  |}.

(** Extend a cospan interpretation to its free diagram. *)

(** 将余跨度解释延拓为自由图式。 *)

Definition CospanDiagram {C : Cat} {X Y Z : @Ob C} (f : Hom X Z) (g : Hom Y Z)
  : Fct CospanShape C
  := FreeF (CospanGraphMap f g).

Notation "'⟨' f '→←' g '⟩D'" := (CospanDiagram f g) : cat_scope.

(** Build a cone on any cospan diagram from a commuting pair of legs. *)

(** 用交换的两条锥腿构造任意余跨度图式上的锥。 *)

Definition CospanConeOver {C : Cat} {D : Fct CospanShape C} {P : @Ob C}
    (p : Hom P (D cospan_left)) (q : Hom P (D cospan_right))
    (H : fmap D (path_edge cospan_l) ∘ p ≈ fmap D (path_edge cospan_r) ∘ q)
  : P ⇒Δ D.
Proof.
  refine (@FreeCone CospanGraph C D P
    (λ v, match v as w return Hom P (D w) with
    | cospan_left => p
    | cospan_right => q
    | cospan_tip => fmap D (path_edge cospan_l) ∘ p
    end) _).
  intros x y e. destruct x, y; cbn in *; destruct e.
  - reflexivity.
  - symmetry. exact H.
Defined.

(** A pullback cone on the diagram of the given cospan. *)

(** 给定余跨度图式上的拉回候选锥。 *)

Definition CospanCone {C : Cat} {X Y Z P : @Ob C}
    {f : Hom X Z} {g : Hom Y Z} (p : Hom P X) (q : Hom P Y)
    (H : f ∘ p ≈ g ∘ q)
  : P ⇒Δ ⟨f →← g⟩D
  := @CospanConeOver C (CospanDiagram f g) P p q H.

(** The two outer legs of a cospan cone have equal composites. *)

(** 余跨度锥的两条外侧锥腿具有相等复合。 *)

Lemma cospan_cone_comm {C : Cat} {D : Fct CospanShape C} {P : @Ob C}
    (κ : P ⇒Δ D)
  : fmap D (path_edge cospan_l) ∘ κ cospan_left ≈
      fmap D (path_edge cospan_r) ∘ κ cospan_right.
Proof.
  transitivity (κ cospan_tip).
  - exact (free_cone_edge κ cospan_l).
  - symmetry. exact (free_cone_edge κ cospan_r).
Qed.

(** * Spans by Duality *)

(** * 通过对偶构造跨度 *)

(** Obtain a span diagram by taking the opposite of a cospan diagram. *)

(** 对余跨度图式取反得到跨度图式。 *)

Definition SpanDiagram {C : Cat} {X Y Z : @Ob C} (f : Hom Z X) (g : Hom Z Y)
  : Fct SpanShape C
  := FromDoubleOpF ∘F (CospanDiagram (C := C^op) f g)^opF.

Notation "'⟨' f '←→' g '⟩D'" := (SpanDiagram f g) : cat_scope.
