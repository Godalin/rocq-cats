From Cats Require Import Cat.Core.

(** * Equalizers *)

(** * 等化子 *)

(** A commuting arrow universal among arrows equalizing the given pair. *)

(** 等化给定平行箭头对并对所有此类箭头具有泛性质的候选箭头。 *)

Definition is_equalizer {C : Cat} {X Y : @Ob C} (f g : Hom X Y)
    (E : @Ob C) (e : Hom E X)
  := f ∘ e ≈ g ∘ e ∧
    ∀ Q (q : Hom Q X), f ∘ q ≈ g ∘ q
      → ∃ h : Hom Q E, is_unique (λ h, e ∘ h ≈ q) h.

Notation "e '⦂' 'Eq(' f ',' g ')'" := (is_equalizer f g _ e)
  (at level 50, no associativity) : cat_scope.

(** Selected equalizers with their inclusions and universal properties. *)

(** 选定等化子、包含箭头及其泛性质。 *)

Class HasEqualizer (C : Cat)
  :=
  { EqObj {X Y} : Hom X Y → Hom X Y → Ob
  ; eqι {X Y} (f g : Hom X Y) : Hom (EqObj f g) X
  ; equalizer_universal {X Y} {f g : Hom X Y}
    : is_equalizer f g (EqObj f g) (eqι f g)
  }.

Notation "'Eq[' f ',' g ']'" := (EqObj f g) : ob_scope.
Notation "'ιeq[' f ',' g ']'" := (eqι f g) : hom_scope.

Section Equalizer.
Context {C : Cat} `{HE : !HasEqualizer C}.

(** The universal factor through the selected equalizer. *)

(** 经过选定等化子的泛分解。 *)

Definition equalize {X Y Q} {f g : Hom X Y} (q : Hom Q X)
    (H : f ∘ q ≈ g ∘ q)
  : Hom Q Eq[f, g]
  := (snd (equalizer_universal (f := f) (g := g)) Q q H).1.

(** The equalizer inclusion equalizes the given parallel arrows. *)

(** 等化子包含箭头等化给定平行箭头。 *)

Theorem equalizer_comm {X Y} {f g : Hom X Y}
  : f ∘ ιeq[f, g] ≈ g ∘ ιeq[f, g].
Proof. exact (fst (equalizer_universal (f := f) (g := g))). Qed.

(** The equalizer factor is uniquely determined by its inclusion composite. *)

(** 等化子分解由其与包含箭头的复合唯一确定。 *)

Theorem equalizer_mediator_unique {X Y Q} {f g : Hom X Y}
    (q : Hom Q X) (H : f ∘ q ≈ g ∘ q)
  : is_unique (λ h, ιeq[f, g] ∘ h ≈ q) (equalize q H).
Proof. exact (snd (equalizer_universal (f := f) (g := g)) Q q H).2. Qed.

(** Composing the factor with the inclusion recovers the given arrow. *)

(** 分解与包含箭头复合后恢复给定箭头。 *)

Theorem equalizer_β {X Y Q} {f g : Hom X Y}
    (q : Hom Q X) (H : f ∘ q ≈ g ∘ q)
  : ιeq[f, g] ∘ equalize q H ≈ q.
Proof. exact (@this _ _ _ _ _ (equalizer_mediator_unique q H)). Qed.

(** Equal mediating data need no equality between their commutativity
    witnesses. *)

(** 相等的中介数据不要求其交换性见证相等。 *)

Theorem equalizer_proper {X Y Q} {f g : Hom X Y} {q q' : Hom Q X}
    (H : f ∘ q ≈ g ∘ q) (H' : f ∘ q' ≈ g ∘ q') (Hq : q ≈ q')
  : equalize q H ≈ equalize q' H'.
Proof. apply equalizer_mediator_unique. rewrite equalizer_β. exact Hq. Qed.

(** The universal equalizer factor commutes with precomposition. *)

(** 等化子的泛分解与预合成交换。 *)

Lemma equalizer_comp {X Y Q R} {f g : Hom X Y} (q : Hom Q X)
    (H : f ∘ q ≈ g ∘ q) (k : Hom R Q)
    (Hk : f ∘ (q ∘ k) ≈ g ∘ (q ∘ k))
  : equalize (q ∘ k) Hk ≈ equalize q H ∘ k.
Proof.
  symmetry. apply equalizer_mediator_unique.
  rewrite <- comp_assoc, equalizer_β. reflexivity.
Qed.

End Equalizer.

Notation "'eq⟨' q ',' H '⟩'" := (equalize q H) : hom_scope.

(** Cancellation is a consequence of the candidate universal property. *)

(** 消去性质由候选泛性质导出。 *)

Theorem equalizer_hom_ext {C : Cat} {X Y E Q : @Ob C} {f g : Hom X Y}
    {e : Hom E X} (HE : is_equalizer f g E e) (u v : Hom Q E)
    (H : e ∘ u ≈ e ∘ v)
  : u ≈ v.
Proof.
  assert (Hv : f ∘ (e ∘ v) ≈ g ∘ (e ∘ v)).
  { rewrite <- !comp_assoc, (fst HE). reflexivity. }
  destruct (snd HE Q (e ∘ v) Hv) as [w [_ Hw]].
  transitivity w; [apply Hw; exact H | symmetry; apply Hw; reflexivity].
Qed.

(** Factoring an inclusion composite recovers its original factor. *)

(** 分解一个包含箭头的复合后恢复原分解。 *)

Theorem equalizer_η {C : Cat} `{HE : !HasEqualizer C}
    {X Y Q} {f g : Hom X Y} (h : Hom Q Eq[f, g])
    (H : f ∘ (ιeq[f, g] ∘ h) ≈ g ∘ (ιeq[f, g] ∘ h))
  : eq⟨ιeq[f, g] ∘ h, H⟩ ≈ h.
Proof. apply (equalizer_hom_ext equalizer_universal). apply equalizer_β. Qed.
