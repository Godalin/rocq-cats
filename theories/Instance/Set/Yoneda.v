From Cats Require Import Cat.Core Cat.Functor Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Hom.

(** * Representable Set-Valued Functors and the Yoneda Lemma *)

(** ** Representable Functor *)

Definition represents {C : Cat} (F : Functor C SetCat) (X : @Ob C)
  := Hom( X ,-) ≅N F.

Notation "X '⦂' 'Rep' F" := (represents F X)
  (at level 50, no associativity, format "X  ⦂  Rep  F") : cat_scope.

Definition is_representable {C : Cat} (F : Functor C SetCat)
  := ∃ X, X ⦂ Rep F.

Proposition represents_self {C : Cat} {X : @Ob C} : X ⦂ Rep Hom(X,-).
Proof. exists idN. intros Y. exists id. cato. Defined.



(** ** Yoneda Lemma *)

Program Canonical Nat_SetS {C D : Cat}
  (F G : Functor C D) :=
  {|carrier := F => G
  ; carrier_equiv := NatEq
  |} .

Section Yoneda.
Context {C : Cat}.
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
  exact (@func_proper _ _ (fmap F f) a a' Ha).
Qed.

Theorem yoneda_func_inv_func {X : @Ob C} (α : Hom(X,-) => F)
  : yoneda_func_inv (yoneda_func α) ≈N α.
Proof.
  intros Y f.
  exact (transitivity (symmetry (nt_naturality α f id))
    (@func_proper _ _ (α Y) (f ∘ id) f (comp_id_r f))).
Defined.

Theorem yoneda_func_func_inv {X : @Ob C} (x : F X)
  : yoneda_func (yoneda_func_inv x) ≈S x.
Proof. exact (functor_id C SetCat F x). Defined.

(** Natural transformations can be larger than values of F. Lift both sets
    into a common ambient category without identifying their native sizes. *)
Definition yoneda_lemma_iso@{n e +} {X : @Ob C}
  : LiftS@{_ _ n e} (Nat_SetS Hom(X,-) F) ≅[SetCat] LiftS@{_ _ n e} (F X).
Proof.
  exists (yoneda_func^↑S), (yoneda_func_inv^↑S). split.
  - intros [α]. refine {| lower := _ |}. apply yoneda_func_inv_func.
  - intros [x]. refine {| lower := _ |}. apply yoneda_func_func_inv.
Defined.

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
