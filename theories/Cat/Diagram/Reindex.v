From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Diagram.

(** * Changing the Shape of a Cone *)

(** * 改变锥的形状 *)

(** Evaluate a cone on image objects to obtain a cone on the composite
    diagram. *)

(** 在像对象上求值锥，得到复合图式上的锥。 *)

Program Definition RestrictCone {I J C : Cat} (Q : Functor I J)
    {D : Functor J C} {X} (κ : X ⇒Δ D)
  : X ⇒Δ (D ∘F Q)
  :=
  {|nt i := κ (Q i)
  |}.
Next Obligation.
  rewrite comp_id_r. apply cone_naturality.
Qed.

Notation "κ '∘Δ' Q" := (RestrictCone Q κ)
  (at level 40, left associativity) : cat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance cone_restrict_proper {I J C : Cat} (Q : Functor I J)
    {D : Functor J C} {X}
  : Proper (NatEq ==> NatEq) (@RestrictCone I J C Q D X).
Proof. intros κ μ H i. exact (H (Q i)). Qed.

(** Restricting a cone commutes with precomposition at its apex. *)

(** 限制锥与顶点预合成交换。 *)

Lemma cone_restrict_comp {I J C : Cat} (Q : Functor I J)
    {D : Functor J C} {X Y} (κ : X ⇒Δ D) (f : Hom Y X)
  : (κ ∘Cone f) ∘Δ Q ≈N (κ ∘Δ Q) ∘Cone f.
Proof. intros i. reflexivity. Qed.

(** Essential surjectivity alone detects equality of cones. Fullness will be
    needed to extend arbitrary cones on the restricted diagram. *)

(** 仅本质满就足以检测锥相等；延拓限制图式上的任意锥时才需要满性。 *)

Lemma cone_restrict_reflects {I J C : Cat} {Q : Functor I J}
    (HQ : is_essentially_surjective Q) {D : Functor J C} {X}
    (κ μ : X ⇒Δ D)
  : κ ∘Δ Q ≈N μ ∘Δ Q → κ ≈N μ.
Proof.
  intros H j. destruct (HQ j) as [i e].
  rewrite (cone_naturality κ e.1), (cone_naturality μ e.1).
  apply comp_l. exact (H i).
Qed.

Section ConeExtension.
Context {I J C : Cat} {Q : Functor I J}.
Context (HF : is_full Q) (HQ : is_essentially_surjective Q).
Context {D : Functor J C}.

(** Use the selected representative isomorphism to transport a source cone
    leg. *)

(** 用选定代表同构将源形状上的锥腿送到目标对象。 *)

Definition cone_extend_leg {X} (κ : X ⇒Δ (D ∘F Q)) (j : @Ob J)
  : Hom X (D j)
  := fmap D (HQ j).2.1 ∘ κ (HQ j).1.

(** Any arrow to [j] gives the same extended leg. Its preimage is used only in
    the proof; the computed leg uses the chosen object isomorphism. *)

(** 任意指向 [j] 的箭头都给出相同的延拓锥腿。原像只用于证明，计算出的锥腿仅使
    用选定的对象同构。 *)

Lemma cone_extend_leg_comm {X} (κ : X ⇒Δ (D ∘F Q))
    {i : @Ob I} {j : @Ob J} (f : Hom (Q i) j)
  : fmap D f ∘ κ i ≈ cone_extend_leg κ j.
Proof.
  destruct (HF i (HQ j).1 ((HQ j).2.2.1 ∘ f)) as [g Hg].
  unfold cone_extend_leg. symmetry.
  rewrite (cone_naturality κ g).
  change (fmap D (HQ j).2.1 ∘ (fmap D (fmap Q g) ∘ κ i) ≈
    fmap D f ∘ κ i).
  rewrite <- comp_assoc, <- functor_comp.
  apply comp_r. apply functor_fmap_proper.
  rewrite Hg, <- comp_assoc, (snd (HQ j).2.2.2), comp_id_l.
  reflexivity.
Qed.

(** Extend a restricted cone using fullness and selected object
    representatives. *)

(** 使用满性及选定对象代表延拓限制图式上的锥。 *)

Program Definition ExtendCone {X} (κ : X ⇒Δ (D ∘F Q))
  : X ⇒Δ D
  :=
  {|nt j := cone_extend_leg κ j
  |}.
Next Obligation.
  rewrite comp_id_r. unfold cone_extend_leg at 2.
  rewrite <- comp_assoc, <- functor_comp.
  symmetry. apply cone_extend_leg_comm.
Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance cone_extend_proper {X}
  : Proper (NatEq ==> NatEq) (@ExtendCone X).
Proof.
  intros κ μ H j. cbn. unfold cone_extend_leg.
  apply comp_l. apply H.
Qed.

(** Extending a cone commutes with precomposition at its apex. *)

(** 延拓锥与顶点预合成交换。 *)

Lemma cone_extend_comp {X Y} (κ : X ⇒Δ (D ∘F Q)) (f : Hom Y X)
  : ExtendCone (κ ∘Cone f) ≈N ExtendCone κ ∘Cone f.
Proof. intros j. symmetry. apply comp_assoc. Qed.

(** Extending a restricted cone recovers the original cone pointwise. *)

(** 延拓限制后的锥，逐点恢复原锥。 *)

Lemma cone_extend_restrict {X} (κ : X ⇒Δ D)
  : ExtendCone (κ ∘Δ Q) ≈N κ.
Proof. intros j. symmetry. apply (cone_naturality κ (HQ j).2.1). Qed.

(** Restricting an extended cone recovers every source leg. *)

(** 限制延拓后的锥，恢复源形状上的每条锥腿。 *)

Lemma cone_restrict_extend {X} (κ : X ⇒Δ (D ∘F Q))
  : ExtendCone κ ∘Δ Q ≈N κ.
Proof.
  intros i. symmetry.
  transitivity (fmap D (@id (Q i)) ∘ κ i).
  - rewrite functor_id, comp_id_l. reflexivity.
  - apply cone_extend_leg_comm.
Qed.

End ConeExtension.

