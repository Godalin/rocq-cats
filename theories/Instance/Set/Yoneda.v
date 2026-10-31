From Cats Require Import Cat.Core Cat.Functor Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Hom.

(** * Representable Set-Valued Functors and the Yoneda Lemma *)

(** ** Representable Functor *)

Section Representable.
Context {C : Cat}.

Definition represents (F : Functor C SetCat) (X : @Ob C)
  := Hom( X ,-) ≅N F.

Notation "X '⦂' 'represents' F" := (represents F X)
  (at level 50).

Definition is_representable (F : Functor C SetCat)
  := ∃ X, X ⦂ represents F.

Context {F : Functor C SetCat} {G : Functor (C^op) SetCat}.
Context {X : @Ob C}.

Proposition represents_self : X ⦂ represents Hom(X,-).
Proof. exists idN. intros Y. exists id. cato. Qed.

End Representable.

Notation "X '⦂' 'represents' F" := (represents F X)
  (at level 50).



(** ** Yoneda Lemma *)

Program Canonical Nat_SetS {C D : Cat}
  (F G : Functor C D) :=
  {|carrier := F => G
  ; carrier_equiv := NatEq
  |} .

Section Yoneda.
Context `{C : Cat}.
Context {F : Functor C SetCat}.

Program Canonical yoneda_func {X}
    : Nat Hom(X,-) F →r F X
  := {| func α := α X id |}.
Next Obligation. intros a a' Ha.
  pose (HaX := Ha X id). cato.
Qed.

Program Canonical yoneda_func_inv {X}
    : F X →r Nat Hom(X,-) F
  := {| func (x : F X) := {| nt Y := {| func f :=
        (fmap F f) x |} |} |}.
Next Obligation.
  intros f f' Hf.
  assert (H : fmap F f ≈ fmap F f').
  { rewrite Hf. cato. }
  specialize (H x). cato.
Qed.
Next Obligation. intros g.
  assert (H : fmap F (f ∘ g) ≈ fmap F f ∘ fmap F g).
  { rewrite functor_comp. cato. }
  specialize (H x). cato.
Qed.
Next Obligation.
  intros a a' Ha Y. simpl.
  intros f. simpl in f.
  rewrite Ha. cato.
Qed.

Theorem yoneda_lemma_iso {X : @Ob C}
  : Nat Hom(X,-) F ≅[SetCat] F X.
Proof. exists yoneda_func, yoneda_func_inv.
  split; simpl.
  - intros a Y. simpl. intros f.
    assert (fmap F f ∘ a X ≈ a Y ∘ fmap Hom(X,-) f).
    { symmetry. apply nt_naturality. }
    specialize (X0 id). rewrite X0.
    simpl. rewrite comp_id_r. cato.
  - intros x.
    assert (fmap F (@id X) ≈ id_resp).
    { rewrite functor_id. cato. }
    specialize (X0 x). cato.
Qed.

End Yoneda.

Theorem yoneda_func_natural_functor {C : Cat} {F G : Functor C SetCat}
    {X : @Ob C}
    (β : F => G) (α : Hom(X,-) => F)
  : yoneda_func (β ∘Nv α) ≈S β X (yoneda_func α).
Proof. reflexivity. Qed.

Theorem yoneda_func_natural_object {C : Cat} {F : Functor C SetCat}
    {X Y : @Ob C} (f : Hom X Y)
    (α : Hom(X,-) => F)
  : yoneda_func (α ∘Nv f ^*N) ≈S fmap F f (yoneda_func α).
Proof.
  pose proof (nt_naturality α f) as Hα.
  specialize (Hα id). simpl in Hα. rewrite comp_id_r in Hα.
  simpl. rewrite comp_id_l. exact Hα.
Qed.
