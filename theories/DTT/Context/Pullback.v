From Cats Require Import Cat.Core Cat.Functor Cat.Pullback.
From Cats Require Import DTT.CwF DTT.Context.Extension DTT.Context.Conversion.
From Cats Require Import Instance.Set.Fam.Core Instance.Set.Fam.Cat.

(** * Substitution Lifts and Pullbacks of Display Projections *)

Section ContextLiftMap.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Definition context_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
  : Hom (Δ ▹[T] A[σ]Ty[T]) (Γ ▹[T] A) :=
  ⟨σ ∘ context_proj T A[σ]Ty[T];
    ty_sub_comp T σ (context_proj T A[σ]Ty[T]) A
      ▸[T] context_var T A[σ]Ty[T]⟩[T, A].

End ContextLiftMap.

Notation "σ '^+[' T ',' A ']'" := (context_lift T σ A)
  (at level 35, format "σ ^+[ T ,  A ]") : cat_scope.

Section ContextLift.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

Definition context_lift_proj {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
  : context_proj T A ∘ σ^+[T, A] ≈ σ ∘ context_proj T A[σ]Ty[T] :=
  context_pair_β1 T A (σ ∘ context_proj T A[σ]Ty[T])
    (ty_sub_comp T σ (context_proj T A[σ]Ty[T]) A ▸[T] context_var T A[σ]Ty[T]).

Theorem context_lift_var {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
  : ty_sub_comm T A (context_proj T A) (σ^+[T, A]) (context_lift_proj σ A)
      ▸[T] (context_var T A)[σ^+[T, A]]Tm[T] ≈S
    ty_sub_comp T σ (context_proj T A[σ]Ty[T]) A ▸[T] context_var T A[σ]Ty[T].
Proof. apply context_pair_β2. Qed.

Theorem context_lift_pair {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (τ : Hom Θ Δ) (t : Tm T Θ A[σ]Ty[T][τ]Ty[T])
  : σ^+[T, A] ∘ ⟨τ; t⟩[T, A[σ]Ty[T]] ≈
    ⟨σ ∘ τ; ty_sub_comp T σ τ A ▸[T] t⟩[T, A].
Proof.
  pose (p := context_proj T A[σ]Ty[T]).
  pose (q := context_var T A[σ]Ty[T]).
  pose (k := ⟨τ; t⟩[T, A[σ]Ty[T]]).
  pose (Hτ := context_pair_β1 T A[σ]Ty[T] τ t).
  assert (H : (σ ∘ p) ∘ k ≈ σ ∘ τ).
  { unfold p, k. rewrite comp_assoc, Hτ. reflexivity. }
  transitivity ⟨(σ ∘ p) ∘ k;
    ty_sub_comp T (σ ∘ p) k A ▸[T]
      (ty_sub_comp T σ p A ▸[T] q)[k]Tm[T]⟩[T, A].
  - apply context_pair_comp.
  - apply (context_pair_equiv T A H).
    transitivity (ty_sub_equiv T H A ▸[T]
      (ty_sub_comp T (σ ∘ p) k A ▸[T]
        ((ty_sub_comp T σ p A)[k]Eq[T] ▸[T] q[k]Tm[T]))).
    + apply func_proper. apply func_proper. apply tm_sub_conv.
    + transitivity (transitivity (ty_sub_comp T σ p A)[k]Eq[T]
        (transitivity (ty_sub_comp T (σ ∘ p) k A) (ty_sub_equiv T H A))
        ▸[T] q[k]Tm[T]).
      * transitivity (ty_sub_equiv T H A ▸[T]
          (transitivity (ty_sub_comp T σ p A)[k]Eq[T]
            (ty_sub_comp T (σ ∘ p) k A) ▸[T] q[k]Tm[T])).
        -- apply func_proper. symmetry. apply tm_conv_comp.
        -- symmetry. apply tm_conv_comp.
      * transitivity (ty_sub_comp T σ τ A ▸[T]
          (ty_sub_comm T A[σ]Ty[T] p k Hτ ▸[T] q[k]Tm[T])).
        -- apply tm_conv_comp.
        -- apply func_proper. apply context_pair_β2.
Qed.

Theorem context_lift_pair_inj {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (τ : Hom Θ Δ) (t u : Tm T Θ A[σ]Ty[T][τ]Ty[T])
  : σ^+[T, A] ∘ ⟨τ; t⟩[T, A[σ]Ty[T]] ≈
      σ^+[T, A] ∘ ⟨τ; u⟩[T, A[σ]Ty[T]] → t ≈S u.
Proof.
  intros H. apply (tm_conv_inj T (ty_sub_comp T σ τ A)).
  apply (context_pair_inj T A (σ ∘ τ)).
  transitivity (σ^+[T, A] ∘ ⟨τ; t⟩[T, A[σ]Ty[T]]).
  - symmetry. apply context_lift_pair.
  - transitivity (σ^+[T, A] ∘ ⟨τ; u⟩[T, A[σ]Ty[T]]).
    + exact H.
    + apply context_lift_pair.
Qed.

(** The comparison maps align the sources of lifts of equal, identity,
    and composite substitutions. All equations use the specified hom equality. *)
Theorem context_lift_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ} (H : σ ≈ σ') (A : Ty T Γ)
  : σ^+[T, A] ≈ σ'^+[T, A] ∘ (ty_sub_equiv T H A)^Ext[T].
Proof.
  pose (p := context_proj T A[σ]Ty[T]). pose (q := context_var T A[σ]Ty[T]).
  pose (Hp := @comp_proper C _ _ _ σ σ' H p p (reflexivity p)).
  transitivity ⟨σ' ∘ p;
    ty_sub_comp T σ' p A ▸[T] ((ty_sub_equiv T H A)[p]Eq[T] ▸[T] q)⟩[T, A].
  - apply (context_pair_equiv T A Hp).
    transitivity (transitivity (ty_sub_comp T σ p A) (ty_sub_equiv T Hp A) ▸[T] q).
    + symmetry. apply tm_conv_comp.
    + apply tm_conv_comp.
  - symmetry. apply context_lift_pair.
Qed.

Theorem context_lift_id {Γ : @Ob C} (A : Ty T Γ)
  : id^+[T, A] ≈ (ty_sub_id T A)^Ext[T].
Proof.
  apply (context_pair_equiv T A (comp_id_l (context_proj T A[id]Ty[T]))).
  symmetry. apply tm_conv_comp.
Qed.

Theorem context_lift_comp {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (τ : Hom Θ Δ) (A : Ty T Γ)
  : σ^+[T, A] ∘ τ^+[T, A[σ]Ty[T]] ≈
    (σ ∘ τ)^+[T, A] ∘ (ty_sub_comp T σ τ A)^Ext[T].
Proof.
  pose (p := context_proj T A[σ]Ty[T][τ]Ty[T]).
  pose (q := context_var T A[σ]Ty[T][τ]Ty[T]).
  pose (H := symmetry (comp_assoc σ τ p)).
  transitivity ⟨σ ∘ (τ ∘ p); ty_sub_comp T σ (τ ∘ p) A ▸[T]
    (ty_sub_comp T τ p A[σ]Ty[T] ▸[T] q)⟩[T, A].
  - apply context_lift_pair.
  - transitivity ⟨(σ ∘ τ) ∘ p; ty_sub_comp T (σ ∘ τ) p A ▸[T]
      ((ty_sub_comp T σ τ A)[p]Eq[T] ▸[T] q)⟩[T, A].
    + apply (context_pair_equiv T A H).
      transitivity (ty_sub_equiv T H A ▸[T]
        (transitivity (ty_sub_comp T τ p A[σ]Ty[T])
          (ty_sub_comp T σ (τ ∘ p) A) ▸[T] q)).
      * apply func_proper. symmetry. apply tm_conv_comp.
      * transitivity (transitivity (ty_sub_comp T τ p A[σ]Ty[T])
          (transitivity (ty_sub_comp T σ (τ ∘ p) A) (ty_sub_equiv T H A)) ▸[T] q).
        -- symmetry. apply tm_conv_comp.
        -- apply tm_conv_comp.
    + symmetry. apply context_lift_pair.
Qed.

(** Only display projections need pullbacks; no global HasPullback is used.
    The universal mediator is pairing after reversing the type comparison. *)
Definition context_lift_pullback {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
  : is_pullback σ (context_proj T A) (Δ ▹[T] A[σ]Ty[T])
      (context_proj T A[σ]Ty[T]) (σ^+[T, A]).
Proof.
  split.
  - symmetry. apply context_lift_proj.
  - intros Θ u v H.
    pose (w := ty_sub_comm T A (context_proj T A) v (symmetry H)
      ▸[T] (context_var T A)[v]Tm[T]).
    pose (t := symmetry (ty_sub_comp T σ u A) ▸[T] w).
    assert (Hfactor : σ^+[T, A] ∘ ⟨u; t⟩[T, A[σ]Ty[T]] ≈ v).
    { transitivity ⟨σ ∘ u; ty_sub_comp T σ u A ▸[T] t⟩[T, A].
      - apply context_lift_pair.
      - symmetry. apply context_pair_unique. exists (symmetry H).
        change (w ≈S ty_sub_comp T σ u A ▸[T] t).
        symmetry. exact (transpS_inv (Tm T Θ) (symmetry (ty_sub_comp T σ u A))
          (ty_sub_comp T σ u A) w). }
    exists ⟨u; t⟩[T, A[σ]Ty[T]]. refine {| this := _; that := _ |}.
    + split; [apply context_pair_β1 | exact Hfactor].
    + intros h [Hbase Hlift].
      pose (s := ty_sub_comm T A[σ]Ty[T] (context_proj T A[σ]Ty[T]) h Hbase
        ▸[T] (context_var T A[σ]Ty[T])[h]Tm[T]).
      pose (Kh := context_pair_η_base T A[σ]Ty[T] h u Hbase).
      transitivity ⟨u; s⟩[T, A[σ]Ty[T]].
      * exact Kh.
      * apply context_pair_proper. apply (context_lift_pair_inj σ A u).
        transitivity v.
        -- transitivity (σ^+[T, A] ∘ h).
           ++ apply comp_l. symmetry. exact Kh.
           ++ exact Hlift.
        -- symmetry. exact Hfactor.
Defined.

Definition context_lift_factor {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (u : Hom Θ Δ) (v : Hom Θ (Γ ▹[T] A))
    (H : σ ∘ u ≈ context_proj T A ∘ v) : Hom Θ (Δ ▹[T] A[σ]Ty[T]) :=
  (snd (context_lift_pullback σ A) Θ u v H).1.

Theorem context_lift_factor_unique {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (u : Hom Θ Δ) (v : Hom Θ (Γ ▹[T] A)) (H : σ ∘ u ≈ context_proj T A ∘ v)
  : is_unique (λ h, context_proj T A[σ]Ty[T] ∘ h ≈ u ∧ σ^+[T, A] ∘ h ≈ v)
      (context_lift_factor σ A u v H).
Proof. exact (snd (context_lift_pullback σ A) Θ u v H).2. Defined.

Definition context_lift_factor_β1 {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (u : Hom Θ Δ) (v : Hom Θ (Γ ▹[T] A)) (H : σ ∘ u ≈ context_proj T A ∘ v)
  : context_proj T A[σ]Ty[T] ∘ context_lift_factor σ A u v H ≈ u :=
  fst (@this _ _ _ _ _ (context_lift_factor_unique σ A u v H)).

Theorem context_lift_factor_β2 {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (u : Hom Θ Δ) (v : Hom Θ (Γ ▹[T] A)) (H : σ ∘ u ≈ context_proj T A ∘ v)
  : σ^+[T, A] ∘ context_lift_factor σ A u v H ≈ v.
Proof. exact (snd (@this _ _ _ _ _ (context_lift_factor_unique σ A u v H))). Qed.

Theorem context_lift_factor_η {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (u : Hom Θ Δ) (v : Hom Θ (Γ ▹[T] A)) (H : σ ∘ u ≈ context_proj T A ∘ v)
    (h : Hom Θ (Δ ▹[T] A[σ]Ty[T]))
  : context_proj T A[σ]Ty[T] ∘ h ≈ u → σ^+[T, A] ∘ h ≈ v
    → h ≈ context_lift_factor σ A u v H.
Proof.
  intros Hbase Hlift. apply (@that _ _ _ _ _ (context_lift_factor_unique σ A u v H)).
  split; assumption.
Qed.

Theorem context_lift_factor_proper {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
    (u u' : Hom Θ Δ) (v v' : Hom Θ (Γ ▹[T] A))
    (H : σ ∘ u ≈ context_proj T A ∘ v) (H' : σ ∘ u' ≈ context_proj T A ∘ v')
  : u ≈ u' → v ≈ v' → context_lift_factor σ A u v H ≈ context_lift_factor σ A u' v' H'.
Proof.
  intros Hu Hv. apply context_lift_factor_η.
  - transitivity u; [apply context_lift_factor_β1 | exact Hu].
  - transitivity v; [apply context_lift_factor_β2 | exact Hv].
Qed.

Theorem context_lift_factor_witness_independent {Γ Δ Θ : @Ob C}
    (σ : Hom Δ Γ) (A : Ty T Γ) (u : Hom Θ Δ) (v : Hom Θ (Γ ▹[T] A))
    (H H' : σ ∘ u ≈ context_proj T A ∘ v)
  : context_lift_factor σ A u v H ≈ context_lift_factor σ A u v H'.
Proof. apply context_lift_factor_proper; reflexivity. Qed.

End ContextLift.
