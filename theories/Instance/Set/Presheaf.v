From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Hom.



(** * The Category of Presheaves *)

Definition Psh C := Fct (op C) SetCat.

Section Psh.
Context `{C : Cat}.

Program Canonical Embedding : Functor C (Psh C) :=
  {|F0 := ℎ2F
  ; F1 X Y f := f _*N
  |}.
Next Obligation. apply nt_comp_post_id. Qed.
Next Obligation. apply nt_comp_post_comp. Qed.

(** A natural transformation between representables is determined by its
    value on the identity. Keep the inverse transparent. *)
Theorem embedding_hom_iso {X Y : @Ob C}
  : @is_iso SetCat _ _ (fmap_resp Embedding (X := X) (Y := Y)).
Proof.
  unshelve eexists (@Build_FunS_resp
    (Hom_SetC (C := Psh C) (X := Embedding X) (Y := Embedding Y))
    (Hom_SetC (C := C) (X := X) (Y := Y))
    (λ α, α X id) _).
  - intros α β Hαβ. exact (Hαβ X id).
  - split.
    + intros f. change (f ∘ id ≈ f). apply comp_id_r.
    + intros α Z h. change (α X id ∘ h ≈ α Z h).
      pose proof (nt_naturality α (X := X) (Y := Z) h) as Hα.
      specialize (Hα id). simpl in Hα. rewrite comp_id_l in Hα.
      symmetry. exact Hα.
Defined.

Theorem embedding_fully_faithful : is_fully_faithful Embedding.
Proof.
  apply (snd (functor_fully_faithful_iff_hom_iso Embedding)).
  intros X Y. apply embedding_hom_iso.
Defined.

End Psh.
