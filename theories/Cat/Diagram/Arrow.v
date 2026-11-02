From Cats Require Export
  Cat.Shape
  Cat.Diagram.Free.
From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural.

(** * The Walking Arrow *)
Program Definition ArrowDiagram {C : Cat} {X Y : @Ob C} (f : Hom X Y)
  : Functor ArrowShape C
  := {| F0 b := if b then Y else X
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
    (H : b ∘ fmap F arrow_step ≈ fmap G arrow_step ∘ a)
  : F ⇒ G
  := {| nt x := if x as v return Hom (F v) (G v) then b else a |}.
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
  : P ⇒Δ ⟨f⟩D
  := @ArrowN C (ConstF ArrowShape P) (ArrowDiagram f) p (f ∘ p) (comp_id_r _).

(** * Parallel Pairs *)
Program Definition ParallelGraphMap {C : Cat} {X Y : @Ob C} (f g : Hom X Y)
  : ParallelGraph →G UnderlyingGraph C
  := {| vertex_map b := if b then Y else X
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
  : Functor ParallelShape C
  := FreeF (ParallelGraphMap f g).

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

Definition ParallelConeOver {C : Cat} {D : Functor ParallelShape C} {P : @Ob C}
    (p : Hom P (D false))
    (H : fmap D (path_edge parallel_l) ∘ p ≈ fmap D (path_edge parallel_r) ∘ p)
  : P ⇒Δ D.
Proof.
  refine (@FreeCone ParallelGraph C D P
    (λ b, if b as v return Hom P (D v)
      then fmap D (path_edge parallel_l) ∘ p else p) _).
  intros x y e. destruct x, y; cbn in *; try solve [destruct e].
  destruct e; [symmetry; exact H | reflexivity].
Defined.

Definition ParallelCone {C : Cat} {X Y P : @Ob C} {f g : Hom X Y}
    (p : Hom P X) (H : f ∘ p ≈ g ∘ p)
  : P ⇒Δ ⟨f ⇉ g⟩D
  := @ParallelConeOver C (ParallelDiagram f g) P p H.

Lemma parallel_cone_comm {C : Cat} {D : Functor ParallelShape C} {P : @Ob C}
    (κ : P ⇒Δ D)
  : fmap D (path_edge parallel_l) ∘ κ false ≈
      fmap D (path_edge parallel_r) ∘ κ false.
Proof.
  transitivity (κ true).
  - exact (free_cone_edge κ parallel_l).
  - symmetry. exact (free_cone_edge κ parallel_r).
Qed.

(** * The Walking Isomorphism *)
Program Definition IsoDiagram {C : Cat} {X Y : @Ob C} (i : X ≅[C] Y)
  : Functor IsoShape C
  := {| F0 b := if b then Y else X; F1 x y e := _ |}.
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
