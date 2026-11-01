From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Pullback
  Cat.Fibration Cat.Comprehension Cat.Arrow.
From Cats Require Import DTT.CwF DTT.ContextPullback.
From Cats Require Import Instance.Set.Fam Instance.Set.FamCat.

(** * Comprehension from a CwF

    Objects are contexts with a type. Morphisms are commuting squares of
    their display projections, retaining both maps and the commutativity
    witness. Equality compares the maps, not the witness. *)

Definition ContextType {C : Cat} (T : Functor (C^op) FamCat) :=
  ∃ Γ : @Ob C, Ty T Γ.

Section ContextMaps.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Record ContextMap (X Y : ContextType T) :=
  { context_map_base : Hom X.1 Y.1
  ; context_map_ext : Hom (X.1 ▹[T] X.2) (Y.1 ▹[T] Y.2)
  ; context_map_comm : context_proj T Y.2 ∘ context_map_ext ≈
      context_map_base ∘ context_proj T X.2
  }.

Arguments context_map_base {_ _} _.
Arguments context_map_ext {_ _} _.
Arguments context_map_comm {_ _} _.

Definition ContextMapEq {X Y : ContextType T} (f g : ContextMap X Y) :=
  context_map_base f ≈ context_map_base g ∧ context_map_ext f ≈ context_map_ext g.

Global Instance ContextMapEq_Equivalence {X Y : ContextType T}
  : Equivalence (@ContextMapEq X Y).
Proof.
  split.
  - intros f. split; reflexivity.
  - intros f g [Hb He]. split; symmetry; assumption.
  - intros f g h [Hb He] [Kb Ke]. split.
    + transitivity (context_map_base g); assumption.
    + transitivity (context_map_ext g); assumption.
Defined.

Program Definition context_map_id (X : ContextType T) : ContextMap X X :=
  {| context_map_base := id; context_map_ext := id |}.
Next Obligation. rewrite comp_id_r, comp_id_l. reflexivity. Defined.

Program Definition context_map_comp {X Y Z : ContextType T}
    (g : ContextMap Y Z) (f : ContextMap X Y) : ContextMap X Z :=
  {| context_map_base := context_map_base g ∘ context_map_base f
   ; context_map_ext := context_map_ext g ∘ context_map_ext f |}.
Next Obligation.
  rewrite <- comp_assoc, (context_map_comm g), comp_assoc, (context_map_comm f),
    <- comp_assoc. reflexivity.
Defined.

End ContextMaps.

Arguments context_map_base {_ _ _ _ _} _.
Arguments context_map_ext {_ _ _ _ _} _.
Arguments context_map_comm {_ _ _ _ _} _.

Notation "g '∘Ctx[' T ']' f" := (context_map_comp T g f)
  (at level 40, left associativity, format "g  ∘Ctx[ T ]  f") : cat_scope.

Section ContextCategory.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Program Definition ContextTypeCat : Cat :=
  {| Ob := ContextType T
   ; HomSet X Y :=
       {| carrier := ContextMap T X Y
        ; carrier_equiv := ContextMapEq T
        ; carrier_setoid := ContextMapEq_Equivalence T |}
   ; id := context_map_id T
   ; comp X Y Z := context_map_comp T |}.
Next Obligation.
  intros g g' [Hb He] f f' [Kb Ke]. split; apply comp_proper; assumption.
Defined.
Next Obligation. split; apply comp_id_r. Defined.
Next Obligation. split; apply comp_id_l. Defined.
Next Obligation. split; apply comp_assoc. Defined.

Program Definition CwFBaseF : Functor ContextTypeCat C :=
  {| F0 X := X.1; F1 X Y := context_map_base |}.
Next Obligation. intros f g H. exact (fst H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

Program Definition CwFExtF : Functor ContextTypeCat C :=
  {| F0 X := X.1 ▹[T] X.2; F1 X Y := context_map_ext |}.
Next Obligation. intros f g H. exact (snd H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

Program Definition CwFProjectionN : CwFExtF => CwFBaseF :=
  {| nt X := context_proj T X.2 |}.
Next Obligation. apply context_map_comm. Defined.

End ContextCategory.

Definition ReindexContextType {C : Cat} (T : Functor (C^op) FamCat)
    (Y : ContextType T) {Γ : @Ob C} (σ : Hom Γ Y.1) : ContextType T :=
  (Γ; Y.2[σ]Ty[T]).

Notation "Y '[' σ ']Ctx[' T ']'" := (ReindexContextType T Y σ)
  (at level 8, left associativity, format "Y [ σ ]Ctx[ T ]") : cat_scope.

Section ContextComprehension.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Program Definition context_type_reindex (Y : ContextType T) {Γ : @Ob C}
    (σ : Hom Γ Y.1) : ContextMap T Y[σ]Ctx[T] Y :=
  {| context_map_base := σ; context_map_ext := σ^+[T, Y.2] |}.
Next Obligation. apply context_lift_proj. Defined.

(** A pullback display square is cartesian in the total category. *)
Definition context_map_pullback_cartesian {X Y : ContextType T} (f : ContextMap T X Y)
    (HP : is_pullback (context_map_base f) (context_proj T Y.2)
      (X.1 ▹[T] X.2) (context_proj T X.2) (context_map_ext f))
  : f ⦂ cartesian(CwFBaseF T).
Proof.
  intros Z g u H.
  assert (Hcone : context_map_base f ∘ (u ∘ context_proj T Z.2) ≈
      context_proj T Y.2 ∘ context_map_ext g).
  { rewrite <- comp_assoc, H. symmetry. apply context_map_comm. }
  destruct (snd HP (Z.1 ▹[T] Z.2) (u ∘ context_proj T Z.2) (context_map_ext g) Hcone)
    as [h [[Hbase Hext] Hunique]].
  pose (k := ({| context_map_base := u; context_map_ext := h; context_map_comm := Hbase |}
    : ContextMap T Z X)).
  exists k. refine {| this := _; that := _ |}.
  - split; [reflexivity | split; assumption].
  - intros l [Hlbase [_ Hlext]]. split; [exact Hlbase |].
    apply Hunique. split.
    + transitivity (context_map_base l ∘ context_proj T Z.2).
      * apply context_map_comm.
      * rewrite Hlbase. reflexivity.
    + exact Hlext.
Defined.

Definition context_type_reindex_cartesian (Y : ContextType T) {Γ : @Ob C}
    (σ : Hom Γ Y.1) : context_type_reindex Y σ ⦂ cartesian(CwFBaseF T) :=
  context_map_pullback_cartesian (context_type_reindex Y σ) (context_lift_pullback T σ Y.2).

(** Enable the chosen lifts explicitly; their base identification is reflexive. *)
Program Definition CwFBaseF_HasCartesianLift : HasCartesianLift (CwFBaseF T) :=
  {| CartesianLift Y Γ σ := Y[σ]Ctx[T]
   ; cartesian_lift_base Y Γ σ := eq_refl
   ; cartesian_lift Y Γ σ := context_type_reindex Y σ |}.
Next Obligation. symmetry. apply comp_id_r. Defined.
Next Obligation. apply context_type_reindex_cartesian. Defined.

(** Any cartesian square is isomorphic to the chosen display pullback. *)
Definition cwf_comprehension_universal : is_comprehension (CwFProjectionN T).
Proof.
  intros X Y f Hf. pose (σ := context_map_base f).
  assert (H : fmap (CwFBaseF T) (context_type_reindex Y σ) ∘ id ≈ fmap (CwFBaseF T) f).
  { apply comp_id_r. }
  pose (k := cartesian_factor (context_type_reindex_cartesian Y σ) f id H).
  assert (Hiso : @is_iso (ContextTypeCat T) _ _ k).
  { apply (cartesian_factor_is_iso Hf (context_type_reindex_cartesian Y σ) id).
    exists id. split; apply comp_id_l. }
  pose proof (cartesian_factor_base (context_type_reindex_cartesian Y σ) f id H) as Hbase.
  pose proof (cartesian_factor_comp (context_type_reindex_cartesian Y σ) f id H) as Hcomp.
  change (context_map_base k ≈ id) in Hbase.
  eapply (pullback_iso (C := C) (p1 := context_proj T Y.2[σ]Ty[T])
    (p2 := σ^+[T, Y.2]) (fmap (CwFExtF T) k) (functor_is_iso (CwFExtF T) k Hiso)).
  - transitivity (context_map_base k ∘ context_proj T X.2).
    + exact (context_map_comm k).
    + rewrite Hbase, comp_id_l. reflexivity.
  - exact (snd Hcomp).
  - apply context_lift_pullback.
Defined.

Program Definition CwFComprehension : Comprehension (CwFBaseF T) :=
  {| comprehension_lifts := CwFBaseF_HasCartesianLift
   ; ExtF := CwFExtF T
   ; projectionN := CwFProjectionN T
   ; comprehension_universal := cwf_comprehension_universal |}.

Theorem context_map_cartesian_iff_pullback {X Y : ContextType T} (f : ContextMap T X Y)
  : f ⦂ cartesian(CwFBaseF T) ↔
    is_pullback (context_map_base f) (context_proj T Y.2)
      (X.1 ▹[T] X.2) (context_proj T X.2) (context_map_ext f).
Proof.
  split.
  - exact (cwf_comprehension_universal X Y f).
  - apply context_map_pullback_cartesian.
Defined.

End ContextComprehension.

Section FullComprehension.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Definition CwFComprehensionF : Functor (ContextTypeCat T) (Arr C) :=
  ComprehensionF (CwFComprehension T).

Program Definition context_map_from_arrow {X Y : ContextType T}
    (f : Hom (CwFComprehensionF X) (CwFComprehensionF Y)) : ContextMap T X Y :=
  {| context_map_base := arrow_bottom f
   ; context_map_ext := arrow_top f
   ; context_map_comm := arrow_comm f |}.

Theorem cwf_comprehension_fully_faithful : is_fully_faithful CwFComprehensionF.
Proof.
  split.
  - intros X Y f. exists (context_map_from_arrow f). split; reflexivity.
  - intros X Y f g [He Hb]. split; assumption.
Defined.

End FullComprehension.
