From Cats Require Export Cat.Diagram.Shape.
From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Functor.Uncurry.

(** * Empty and Single-Object Diagrams *)
Definition EmptyDiagram (C : Cat) : Functor EmptyShape C :=
  DiscreteF (λ x : Empty_set, match x with end).

Definition PointDiagram {C : Cat} (X : @Ob C) : Functor PointShape C :=
  DiscreteF (λ _ : unit, X).

(** * The Walking Arrow *)
Program Definition ArrowDiagram {C : Cat} {X Y : @Ob C} (f : Hom X Y)
  : Functor ArrowShape C :=
  {| F0 b := if b then Y else X
   ; F1 x y e := _ |}.
Next Obligation.
  destruct x, y; cbn in *; destruct e.
  - exact id.
  - exact f.
  - exact id.
Defined.
Next Obligation. intros u v H. destruct X0, Y0; cbn in *; destruct u, v; reflexivity. Defined.
Next Obligation. destruct X0; reflexivity. Defined.
Next Obligation.
  destruct X0, Y0, Z; cbn in *; destruct f0, g; cbn; carw.
Defined.

Notation "'⟨' f '⟩D'" := (ArrowDiagram f) : cat_scope.

Program Definition ArrowN {C : Cat} {F G : Functor ArrowShape C}
    (a : Hom (F false) (G false)) (b : Hom (F true) (G true))
    (H : b ∘ fmap F arrow_step ≈ fmap G arrow_step ∘ a) : F ⇒ G :=
  {| nt x := if x as v return Hom (F v) (G v) then b else a |}.
Next Obligation.
  destruct X, Y; cbn in *; destruct f.
  - change (b ∘ fmap F (@Cat.Core.id ArrowShape true) ≈
      fmap G (@Cat.Core.id ArrowShape true) ∘ b).
    rewrite !functor_id. carw.
  - exact H.
  - change (a ∘ fmap F (@Cat.Core.id ArrowShape false) ≈
      fmap G (@Cat.Core.id ArrowShape false) ∘ a).
    rewrite !functor_id. carw.
Defined.

Global Instance ArrowDiagram_proper {C : Cat} {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> NatIso) (@ArrowDiagram C X Y).
Proof.
  intros f g Hfg.
  unshelve refine ((@ArrowN C (ArrowDiagram f) (ArrowDiagram g) id id _); _).
  - cbn. carw. exact Hfg.
  - intros []; exists id; split; apply comp_id_l.
Defined.

Definition ArrowCone {C : Cat} {X Y P : @Ob C} (f : Hom X Y) (p : Hom P X)
  : P ⇒Δ ⟨f⟩D :=
  @ArrowN C (ConstF ArrowShape P) (ArrowDiagram f) p (f ∘ p) (comp_id_r _).

(** * Spans by Duality *)
Definition SpanDiagram {C : Cat} {X Y Z : @Ob C} (f : Hom Z X) (g : Hom Z Y)
  : Functor SpanShape C := FromDoubleOpF ∘F OpF (CospanDiagram (C := C^op) f g).

Notation "'⟨' f '←→' g '⟩D'" := (SpanDiagram f g) : cat_scope.

(** * Parallel Pairs *)
Program Definition ParallelGraphMap {C : Cat} {X Y : @Ob C} (f g : Hom X Y)
  : ParallelGraph →G UnderlyingGraph C :=
  {| vertex_map b := if b then Y else X
   ; edge_map x y := {| func e := _ |} |}.
Next Obligation.
  destruct x, y; cbn in *; try solve [destruct e].
  exact (if e then g else f).
Defined.
Next Obligation.
  intros e e' H. destruct x, y; cbn in *; try solve [destruct e].
  destruct H. reflexivity.
Defined.

Definition ParallelDiagram {C : Cat} {X Y : @Ob C} (f g : Hom X Y)
  : Functor ParallelShape C := FreeF (ParallelGraphMap f g).

Notation "'⟨' f '⇉' g '⟩D'" := (ParallelDiagram f g) : cat_scope.

Global Instance ParallelDiagram_proper {C : Cat} {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> @HomEq[X, Y] ==> NatIso) (@ParallelDiagram C X Y).
Proof.
  intros f f' Hf g g' Hg.
  unshelve refine ((@FreeN ParallelGraph C (ParallelDiagram f g)
    (ParallelDiagram f' g') (λ _, id) _); _).
  - intros x y e. destruct x, y; cbn in *; try solve [destruct e].
    destruct e; cbn; carw; assumption.
  - intros b. exists id. split; apply comp_id_l.
Defined.

Definition ParallelCone {C : Cat} {X Y P : @Ob C} {f g : Hom X Y}
    (p : Hom P X) (H : f ∘ p ≈ g ∘ p) : P ⇒Δ ⟨f ⇉ g⟩D.
Proof.
  refine (@FreeCone ParallelGraph C (ParallelDiagram f g) P
    (λ b, if b as v return Hom P (if v then Y else X) then f ∘ p else p) _).
  intros x y e. destruct x, y; cbn in *; try solve [destruct e].
  destruct e; [symmetry; exact H | reflexivity].
Defined.

Lemma parallel_cone_comm {C : Cat} {X Y P : @Ob C} {f g : Hom X Y}
    (κ : P ⇒Δ ⟨f ⇉ g⟩D) : f ∘ κ false ≈ g ∘ κ false.
Proof.
  transitivity (κ true).
  - exact (free_cone_edge κ parallel_l).
  - symmetry. exact (free_cone_edge κ parallel_r).
Qed.

(** * Commuting Squares

    The square is a product of walking arrows. Uncurrying packages its
    commuting equation as the naturality of a transformation of arrows. *)
Definition SquareDiagram {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g) : Functor SquareShape C :=
  (ArrowDiagram (C := Fct ArrowShape C)
    (@ArrowN C (ArrowDiagram f) (ArrowDiagram k) g h H))^uncF.

Notation "'⟨' f ',' g ';' h ',' k '|' H '⟩□'" := (SquareDiagram f g h k H) : cat_scope.

Lemma square_diagram_top {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g) : fmap (SquareDiagram f g h k H) square_top ≈ f.
Proof. cbn. apply comp_id_r. Qed.

Lemma square_diagram_left {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g) : fmap (SquareDiagram f g h k H) square_left ≈ g.
Proof. cbn. apply comp_id_l. Qed.

Lemma square_diagram_right {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g) : fmap (SquareDiagram f g h k H) square_right ≈ h.
Proof. cbn. apply comp_id_l. Qed.

Lemma square_diagram_bottom {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g) : fmap (SquareDiagram f g h k H) square_bottom ≈ k.
Proof. cbn. apply comp_id_r. Qed.

(** * The Walking Isomorphism *)
Program Definition IsoDiagram {C : Cat} {X Y : @Ob C} (i : X ≅[C] Y)
  : Functor IsoShape C :=
  {| F0 b := if b then Y else X; F1 x y e := _ |}.
Next Obligation.
  destruct x, y.
  - exact id.
  - exact i.2.1.
  - exact i.1.
  - exact id.
Defined.
Next Obligation. intros [] [] _. destruct X0, Y0; reflexivity. Defined.
Next Obligation. destruct X0; reflexivity. Defined.
Next Obligation.
  destruct X0, Y0, Z; cbn in *; carw; symmetry;
    first [exact (fst i.2.2) | exact (snd i.2.2)].
Defined.

Notation "'⟨' i '⟩≅D'" := (IsoDiagram i) : cat_scope.
