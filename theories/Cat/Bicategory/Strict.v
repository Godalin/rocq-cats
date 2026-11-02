From Cats Require Import Cat.Core.
From Cats Require Export Cat.Bicategory.

Local Open Scope bicat_scope.

Notation "f '≈₁[' R ']' g" := (R f g)
  (at level 50, no associativity, only parsing) : bicat_scope.

(** * Strictness relative to a 1-cell setoid

    [Cell2Eq] compares parallel 2-cells, not their endpoints. Strictness
    therefore specifies a separate equivalence of 1-cells, with coherent
    comparison 2-cells. Every equality loop must act as an identity; the
    comparison cannot be an arbitrary chosen isomorphism.

    This is strictness in the specified setoid presentation, not a claim of
    native equality of 1-cells or a strictification of every bicategory. *)

(** * 相对于一胞广集的严格性

    [Cell2Eq] 比较平行二胞，不比较端点。因此另行指定一胞等价与相干的比较二胞；
    每个相等环路的作用必须等于恒等，不能随意选择同构。这是在指定广集表示下的严
    格性，不是原生一胞相等，也不声称任意双范畴都已严格化。 *)

Class IsStrictTwoCat (K : Bicat)
    (Cell1Eq : ∀ X Y : ObB K, crelation (Cell1 X Y))
    (cell1_eq_to_cell2 : ∀ X Y (f g : Cell1 X Y),
      f ≈₁[Cell1Eq X Y] g → f ⇒₂ g)
  :=
  { Cell1Eq_Equivalence X Y :: Equivalence (Cell1Eq X Y)
  ; comp1_proper X Y Z
      :: Proper (Cell1Eq Y Z ==> Cell1Eq X Y ==> Cell1Eq X Z)
          (@comp1 K X Y Z)
  ; cell1_eq_to_cell2_id X Y (f : Cell1 X Y) (p : f ≈₁[Cell1Eq X Y] f)
      : cell1_eq_to_cell2 X Y f f p ≈₂ 𝟙₂ f
  ; cell1_eq_to_cell2_comp X Y (f g h : Cell1 X Y)
      (p : f ≈₁[Cell1Eq X Y] g) (q : g ≈₁[Cell1Eq X Y] h)
      (r : f ≈₁[Cell1Eq X Y] h)
      : cell1_eq_to_cell2 X Y f h r ≈₂
          (cell1_eq_to_cell2 X Y g h q ∘₂ cell1_eq_to_cell2 X Y f g p)
  ; cell1_eq_to_cell2_hcomp X Y Z (g g' : Cell1 Y Z) (f f' : Cell1 X Y)
      (p : g ≈₁[Cell1Eq Y Z] g') (q : f ≈₁[Cell1Eq X Y] f')
      (r : (g ∘₁ f) ≈₁[Cell1Eq X Z] (g' ∘₁ f'))
      : cell1_eq_to_cell2 X Z (g ∘₁ f) (g' ∘₁ f') r ≈₂
          (cell1_eq_to_cell2 Y Z g g' p ⋆ cell1_eq_to_cell2 X Y f f' q)
  ; comp1_id_l X Y (f : Cell1 X Y) : (𝟙₁ Y ∘₁ f) ≈₁[Cell1Eq X Y] f
  ; comp1_id_r X Y (f : Cell1 X Y) : (f ∘₁ 𝟙₁ X) ≈₁[Cell1Eq X Y] f
  ; comp1_assoc W X Y Z (h : Cell1 Y Z) (g : Cell1 X Y) (f : Cell1 W X)
      : ((h ∘₁ g) ∘₁ f) ≈₁[Cell1Eq W Z] (h ∘₁ (g ∘₁ f))
  ; left_unitor_strict X Y (f : Cell1 X Y)
      : left_unitor f ≈₂ cell1_eq_to_cell2 X Y _ _ (comp1_id_l X Y f)
  ; right_unitor_strict X Y (f : Cell1 X Y)
      : right_unitor f ≈₂ cell1_eq_to_cell2 X Y _ _ (comp1_id_r X Y f)
  ; associator_strict W X Y Z (h : Cell1 Y Z) (g : Cell1 X Y) (f : Cell1 W X)
      : associator h g f ≈₂
          cell1_eq_to_cell2 W Z _ _ (comp1_assoc W X Y Z h g f)
  }.

Section StrictTwoCat.
Context {K : Bicat}
    {R : ∀ X Y : ObB K, crelation (Cell1 X Y)}
    {cmp : ∀ X Y (f g : Cell1 X Y), f ≈₁[R X Y] g → f ⇒₂ g}
    {S : IsStrictTwoCat K R cmp}.
Local Existing Instance S.

(** Equality witnesses need not be equal. Only their action is equivalent. *)

(** 相等见证本身不必相等，只要求其作用等价。 *)

Theorem cell1_eq_to_cell2_unique {X Y} {f g : Cell1 X Y}
    (p q : f ≈₁[R X Y] g)
  : cmp X Y f g p ≈₂ cmp X Y f g q.
Proof.
  transitivity (cmp X Y f g q ∘₂ cmp X Y f f (reflexivity f)).
  - apply cell1_eq_to_cell2_comp.
  - transitivity (cmp X Y f g q ∘₂ 𝟙₂ f).
    + apply comp2_v_proper; [reflexivity | apply cell1_eq_to_cell2_id].
    + apply comp2_v_id_r.
Qed.

(** The two-cell induced by designated one-cell equality is invertible. *)

(** 指定一胞相等诱导的二胞可逆。 *)

Definition cell1_eq_to_cell2_iso {X Y} {f g : Cell1 X Y}
    (p : f ≈₁[R X Y] g)
  : is_iso (cmp X Y f g p).
Proof.
  exists (cmp X Y g f (symmetry p)). split;
    unfold is_linv_of, is_rinv_of.
  - transitivity (cmp X Y f f (reflexivity f)).
    + symmetry. apply cell1_eq_to_cell2_comp.
    + apply cell1_eq_to_cell2_id.
  - transitivity (cmp X Y g g (reflexivity g)).
    + symmetry. apply cell1_eq_to_cell2_comp.
    + apply cell1_eq_to_cell2_id.
Defined.

(** ** Transport of 2-cell Endpoints *)

(** ** 二胞端点的运输 *)

(** Change both endpoints of a two-cell using designated one-cell equalities. *)

(** 用指定一胞相等改变二胞的两个端点。 *)

Definition cell2_transport {X Y} {f f' g g' : Cell1 X Y}
    (p : f ≈₁[R X Y] f') (q : g ≈₁[R X Y] g') (α : f ⇒₂ g)
  : f' ⇒₂ g'
  := cmp X Y g g' q ∘₂ α ∘₂ cmp X Y f' f (symmetry p).

Local Notation "α '⟦' p ',' q '⟧₂'" := (cell2_transport p q α)
  (at level 8, left associativity) : bicat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance cell2_transport_proper {X Y} {f f' g g' : Cell1 X Y}
    (p : f ≈₁[R X Y] f') (q : g ≈₁[R X Y] g')
  : Proper (Cell2Eq ==> Cell2Eq) (cell2_transport p q).
Proof.
  intros α β H. unfold cell2_transport.
  apply comp2_v_proper; [reflexivity |].
  apply comp2_v_proper; [exact H | reflexivity].
Qed.

(** Changing equality witnesses leaves the resulting action equal. *)

(** 改变相等见证后，所得作用仍然相等。 *)

Theorem cell2_transport_witness_independent {X Y} {f f' g g' : Cell1 X Y}
    (p p' : f ≈₁[R X Y] f') (q q' : g ≈₁[R X Y] g') (α : f ⇒₂ g)
  : α⟦p, q⟧₂ ≈₂ α⟦p', q'⟧₂.
Proof.
  unfold cell2_transport. apply comp2_v_proper.
  - apply cell1_eq_to_cell2_unique.
  - apply comp2_v_proper; [reflexivity | apply cell1_eq_to_cell2_unique].
Qed.

(** Compatibility with identities for [cell2_transport]. *)

(** [cell2_transport] 与恒等的相容性。 *)

Theorem cell2_transport_id {X Y} {f g : Cell1 X Y}
    (p : f ≈₁[R X Y] f) (q : g ≈₁[R X Y] g) (α : f ⇒₂ g)
  : α⟦p, q⟧₂ ≈₂ α.
Proof.
  unfold cell2_transport. rewrite !cell1_eq_to_cell2_id.
  rewrite comp2_v_id_l, comp2_v_id_r. reflexivity.
Qed.

(** Compatibility with composition for [cell2_transport]. *)

(** [cell2_transport] 与复合的相容性。 *)

Theorem cell2_transport_comp {X Y} {f f' f'' g g' g'' : Cell1 X Y}
    (p : f ≈₁[R X Y] f') (p' : f' ≈₁[R X Y] f'') (r : f ≈₁[R X Y] f'')
    (q : g ≈₁[R X Y] g') (q' : g' ≈₁[R X Y] g'') (s : g ≈₁[R X Y] g'')
    (α : f ⇒₂ g)
  : α⟦p, q⟧₂⟦p', q'⟧₂ ≈₂ α⟦r, s⟧₂.
Proof.
  unfold cell2_transport. symmetry.
  transitivity ((cmp X Y g' g'' q' ∘₂ cmp X Y g g' q) ∘₂
    α ∘₂ (cmp X Y f' f (symmetry p) ∘₂ cmp X Y f'' f' (symmetry p'))).
  - apply comp2_v_proper.
    + apply cell1_eq_to_cell2_comp.
    + apply comp2_v_proper; [reflexivity | apply cell1_eq_to_cell2_comp].
  - rewrite !comp2_v_assoc. reflexivity.
Qed.

(** Transporting along inverse endpoint equalities recovers the two-cell. *)

(** 沿逆端点相等运输，恢复原二胞。 *)

Theorem cell2_transport_inv {X Y} {f f' g g' : Cell1 X Y}
    (p : f ≈₁[R X Y] f') (q : g ≈₁[R X Y] g') (α : f ⇒₂ g)
  : α⟦p, q⟧₂⟦symmetry p, symmetry q⟧₂ ≈₂ α.
Proof.
  transitivity (α⟦reflexivity f, reflexivity g⟧₂).
  - apply cell2_transport_comp.
  - apply cell2_transport_id.
Qed.

(** Compatibility with vertical composition for [cell2_transport]. *)

(** [cell2_transport] 与垂直复合的相容性。 *)

Theorem cell2_transport_comp_v {X Y} {f f' g g' h h' : Cell1 X Y}
    (p : f ≈₁[R X Y] f') (q : g ≈₁[R X Y] g') (r : h ≈₁[R X Y] h')
    (β : g ⇒₂ h) (α : f ⇒₂ g)
  : (β ∘₂ α)⟦p, r⟧₂ ≈₂ (β⟦q, r⟧₂ ∘₂ α⟦p, q⟧₂).
Proof.
  unfold cell2_transport. symmetry. rewrite !comp2_v_assoc.
  rewrite <- (comp2_v_assoc (cmp X Y g' g (symmetry q)) (cmp X Y g g' q)
    (α ∘₂ cmp X Y f' f (symmetry p))).
  pose proof (fst (cell1_eq_to_cell2_iso q).2) as Hq.
  change ((cmp X Y g' g (symmetry q) ∘₂ cmp X Y g g' q) ≈₂ 𝟙₂ g) in Hq.
  rewrite Hq, comp2_v_id_l. reflexivity.
Qed.

(** Compatibility with horizontal composition for [cell2_transport]. *)

(** [cell2_transport] 与水平复合的相容性。 *)

Theorem cell2_transport_comp_h {X Y Z}
    {f0 f0' f1 f1' : Cell1 X Y} {g0 g0' g1 g1' : Cell1 Y Z}
    (p0 : f0 ≈₁[R X Y] f0') (p1 : f1 ≈₁[R X Y] f1')
    (q0 : g0 ≈₁[R Y Z] g0') (q1 : g1 ≈₁[R Y Z] g1')
    (β : g0 ⇒₂ g1) (α : f0 ⇒₂ f1)
  : (β ⋆ α)⟦comp1_proper X Y Z _ _ q0 _ _ p0,
      comp1_proper X Y Z _ _ q1 _ _ p1⟧₂ ≈₂
      (β⟦q0, q1⟧₂ ⋆ α⟦p0, p1⟧₂).
Proof.
  unfold cell2_transport.
  transitivity ((cmp Y Z g1 g1' q1 ⋆ cmp X Y f1 f1' p1) ∘₂
    (β ⋆ α) ∘₂ (cmp Y Z g0' g0 (symmetry q0) ⋆
      cmp X Y f0' f0 (symmetry p0))).
  - apply comp2_v_proper.
    + apply cell1_eq_to_cell2_hcomp.
    + apply comp2_v_proper; [reflexivity | apply cell1_eq_to_cell2_hcomp].
  - rewrite <- !comp2_interchange. reflexivity.
Qed.

End StrictTwoCat.

Notation "α '⟦' p ',' q '⟧₂'" := (cell2_transport p q α)
  (at level 8, left associativity) : bicat_scope.
