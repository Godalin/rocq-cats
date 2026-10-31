From Cats Require Import Cat.Core Cat.Functor Cat.Natural Instance.Set.Core.

(** * Hom-Functors *)

Definition ℎ1 {C : Cat} (X : Ob) := λ Y, Hom X Y.
Definition ℎ2 {C : Cat} (X : Ob) := λ Y, Hom Y X.

Program Definition ℎ1F {C : Cat} (X : Ob) : Functor C SetCat :=
  {|F0 := ℎ1 X
  ; F1 Y Y' (f : Hom Y Y') := f _*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. simpl. cato. Qed.
Next Obligation. intros x. simpl. apply comp_assoc. Qed.

Notation "'Hom(' X  ',-)'" := (ℎ1F X).

Program Definition ℎ2F {C : Cat} (X : Ob)
  : Functor (op C) SetCat :=
  {|F0 := ℎ2 X
  ; F1 Y Y' (f : (@Hom C) Y' Y) := f ^*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. simpl. cato. Qed.
Next Obligation. intros x. simpl. cacl. Qed.

Notation "'Hom(-,'  X ')'" := (ℎ2F X).

(** Precomposition varies the source of the covariant Hom-functor
    contravariantly. Its components compare maps pointwise. *)
Program Definition nt_comp_pre {C : Cat} {X Y : @Ob C} (f : Hom X Y)
  : Hom(Y,-) => Hom(X,-) :=
  {| nt Z := comp_r_resp (f := f) (Z := Z) |}.
Next Obligation. intros h. simpl. apply comp_assoc. Qed.

Notation "f ^*N" := (nt_comp_pre f) (at level 35) : cat_scope.

Global Instance nt_comp_pre_proper {C : Cat} {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> NatEq) (@nt_comp_pre C X Y).
Proof. intros f g Hfg Z h. simpl. rewrite Hfg. reflexivity. Qed.

Theorem nt_comp_pre_id {C : Cat} {X : @Ob C}
  : (@id X) ^*N ≈N idN.
Proof. intros Z h. simpl. apply comp_id_r. Qed.

Theorem nt_comp_pre_comp {C : Cat} {X Y Z : @Ob C}
    (g : Hom Y Z) (f : Hom X Y)
  : (g ∘ f) ^*N ≈N (f ^*N ∘Nv g ^*N).
Proof. intros W h. simpl. symmetry. apply comp_assoc. Qed.

(** Postcomposition varies the target of the contravariant Hom-functor
    covariantly. *)
Program Definition nt_comp_post {C : Cat} {X Y : @Ob C} (f : Hom X Y)
  : Hom(-,X) => Hom(-,Y) :=
  {| nt Z := comp_l_resp (C := C) (f := f) (X := Z) |}.
Next Obligation. intros h. simpl. symmetry. apply comp_assoc. Qed.

Notation "f _*N" := (nt_comp_post f) (at level 35) : cat_scope.

Global Instance nt_comp_post_proper {C : Cat} {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> NatEq) (@nt_comp_post C X Y).
Proof. intros f g Hfg Z h. simpl. rewrite Hfg. reflexivity. Qed.

Theorem nt_comp_post_id {C : Cat} {X : @Ob C}
  : (@id X) _*N ≈N idN.
Proof. intros Z h. simpl. apply comp_id_l. Qed.

Theorem nt_comp_post_comp {C : Cat} {X Y Z : @Ob C}
    (g : Hom Y Z) (f : Hom X Y)
  : (g ∘ f) _*N ≈N (g _*N ∘Nv f _*N).
Proof. intros W h. simpl. apply comp_assoc. Qed.

Program Canonical bi_comp {C : Cat} {X' X Y Y' : @Ob C}
    (f : (@Hom op C) X X') (g : Hom Y Y')
  : (Hom X Y) →r (Hom X' Y')
  := {|func := λ h, g ∘ h ∘ f |}.
Next Obligation. intros h h' Hh. rewrite Hh. cato. Qed.

Program Definition HomF {C : Cat}
  : Functor (op C ×C C) SetCat :=
  {|F0 X := (@Hom C) (fst X) (snd X)
  ; F1 _ _ f := bi_comp (fst f) (snd f)
  |}.
Next Obligation. simpl. intros [f g] [f' g'] [Hf Hg].
  simpl. intros h. simpl.
  rewrite Hf, Hg. reflexivity.
Qed.
Next Obligation. simpl. intros h. simpl; carw. Qed.
Next Obligation. simpl. intros g. simpl. repeat cacr. Qed.

(** * Morphism Maps of Functors

    Full faithfulness makes this specific map an isomorphism of setoids. *)

Program Canonical fmap_resp {C D : Cat} (F : Functor C D) {X Y : @Ob C}
  : Hom X Y →r Hom (F X) (F Y) :=
  {| func := fmap F (X := X) (Y := Y) |}.

Theorem functor_fully_faithful_iff_hom_iso {C D : Cat} (F : Functor C D)
  : is_fully_faithful F ↔
      ∀ X Y, @is_iso SetCat _ _ (fmap_resp F (X := X) (Y := Y)).
Proof. split.
  - intros HF X Y.
    pose (Hfull := fst HF). pose (Hfaith := snd HF).
    unshelve eexists (@Build_FunS_resp _ _ (λ g, (Hfull X Y g).1) _).
    + intros g h Hgh. apply (Hfaith X Y).
      transitivity g. exact (Hfull X Y g).2.
      transitivity h. exact Hgh. symmetry. exact (Hfull X Y h).2.
    + split.
      * intros f. apply (Hfaith X Y). exact (Hfull X Y (fmap F f)).2.
      * intros g. exact (Hfull X Y g).2.
  - intros Hiso. split.
    + intros X Y g. exists ((Hiso X Y).1 g).
      exact (snd ((Hiso X Y).2) g).
    + intros X Y f g Hfg. destruct (Hiso X Y) as [i [Hl Hr]].
      transitivity (i (fmap F f)). symmetry. exact (Hl f).
      transitivity (i (fmap F g)). apply func_proper. exact Hfg.
      exact (Hl g).
Defined.
