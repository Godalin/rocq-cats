From Cats Require Export
  Cat.Diagram.Dual
  Cat.Diagram.Discrete
  Cat.Diagram.Arrow
  Cat.Diagram.Span.

From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** A family of outgoing legs on a discrete diagram needs no generating
    naturality equations. *)

(** 离散图式上的出发锥腿族不需要生成边自然性方程。 *)

Definition DiscreteCocone {C : Cat} {I : Type}
    {D : Functor (DiscreteCat I) C} {X : @Ob C}
    (κ : ∀ i, Hom (D i) X)
  : D ⇒∇ X
  := CoconeOfN (@FreeN (DiscreteGraph I) C D
      (ConstF (DiscreteCat I) X) κ (λ x y e, match e with end)).

(** * Ordinary Diagrams for Dual Universal Constructions *)

(** * 对偶泛构造的通常图式 *)

(** The empty diagram of opposite shape is the dual of the original empty
    diagram in the opposite category. *)

(** 反空形状的图式就是原反范畴空图式的对偶。 *)

Definition EmptyCodiagram (C : Cat)
  : Functor (EmptyShape^op) C
  := DualDiagram (EmptyDiagram (C^op)).

(** The empty cocone is the original empty cone read in the dual interface. *)

(** 空余锥就是将原空锥读入对偶接口。 *)

Definition EmptyCocone {C : Cat} (X : @Ob C)
  : EmptyCodiagram C ⇒∇ X
  := DualCone (@EmptyCone (C^op) (EmptyDiagram (C^op)) X).

(** A pair of objects gives the dual of the original discrete-pair diagram.
    False remains the first object and true the second. *)

(** 对象对给出原离散二点图式的对偶；[false] 仍为第一对象，[true] 为第二对象。 *)

Definition PairCodiagram {C : Cat} (X Y : @Ob C)
  : Functor (PairShape^op) C
  := DualDiagram (@PairDiagram (C^op) X Y).

Notation "'⟨' X ',' Y '⟩CoD'" := (PairCodiagram X Y) : cat_scope.

(** Two arrows to a common codomain form a cocone through opposite pairing. *)

(** 两条同余域箭头通过反范畴配对构成余锥。 *)

Definition PairCocone {C : Cat} {X Y S : @Ob C}
    (i : Hom X S) (j : Hom Y S)
  : ⟨X, Y⟩CoD ⇒∇ S
  := DualCone (@PairCone (C^op) X Y S i j).

Notation "'⟨' i ',' j '⟩Cocone'" := (PairCocone i j) : cat_scope.

(** Reverse the original parallel diagram in the opposite category. The
    source is [true] and the common target is [false]. *)

(** 反转原反范畴中的平行箭头图式；[true] 是源，[false] 是共同目标。 *)

Definition ParallelCodiagram {C : Cat} {X Y : @Ob C} (f g : Hom X Y)
  : Functor (ParallelShape^op) C
  := DualDiagram (@ParallelDiagram (C^op) Y X f g).

Notation "'⟨' f '⇉' g '⟩CoD'" := (ParallelCodiagram f g) : cat_scope.

(** A coequalizing arrow supplies the original opposite parallel cone. *)

(** 余等化箭头给出原反范畴中的平行箭头锥。 *)

Definition ParallelCocone {C : Cat} {X Y Q : @Ob C} {f g : Hom X Y}
    (q : Hom Y Q) (H : q ∘ f ≈ q ∘ g)
  : ⟨f ⇉ g⟩CoD ⇒∇ Q
  := DualCone (@ParallelCone (C^op) Y X Q f g q H).

(** A commuting pair of maps out of a span is the dual of the original
    cospan cone, retaining both leg maps. *)

(** 从跨度出发的交换映射对就是原余跨度锥的对偶，保留两条腿的映射。 *)

Definition SpanCocone {C : Cat} {X Y Z P : @Ob C}
    {f : Hom Z X} {g : Hom Z Y} (i : Hom X P) (j : Hom Y P)
    (H : i ∘ f ≈ j ∘ g)
  : ⟨f ←→ g⟩D ⇒∇ P
  := DualCone (@CospanCone (C^op) X Y Z P f g i j H).
