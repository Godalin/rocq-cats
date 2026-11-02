From Cats Require Import Cat.Core Cat.Functor Cat.Adjunction Cat.Product.

(** * Exponential Objects *)

Definition is_exponential {C : Cat} `{HP : !HasProduct C}
    (X Y E : Ob) (ev : Hom (E × X) Y) :=
  ∀ Z (f : Hom (Z × X) Y),
    ∃ h : Hom Z E, is_unique (λ h, ev ∘ (h × id) ≈ f) h.

Class HasExponential {C : Cat} (HP : HasProduct C) :=
  { exp : Ob → Ob → Ob
  ; eval {X Y} : Hom (exp Y X × X) Y

  ; exponential_universal {X Y} : is_exponential X Y (exp Y X) eval
  }.

Arguments exponential_universal {_ _ _ _ _} _ _.

Definition curry {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}
    {X Y Z} (f : Hom (Z × X) Y) : Hom Z (exp Y X) :=
  (exponential_universal Z f).1.

Theorem exponential_curry_unique {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
    (f : Hom (Z × X) Y)
  : is_unique (λ h, eval ∘ (h × id) ≈ f) (curry f).
Proof. exact (exponential_universal Z f).2. Qed.

Global Instance exponential_curry_proper {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
  : Proper (@HomEq[Z × X, Y] ==> @HomEq[Z, exp Y X]) curry.
Proof.
  intros f g Hfg.
  destruct (exponential_curry_unique f) as [Hf _].
  apply (exponential_curry_unique g). transitivity f; assumption.
Qed.

Notation "X '^' Y" := (exp X Y)
  (at level 30, right associativity): ob_scope.

Notation "'ƛ' f" := (curry f)
  (at level 35) : hom_scope.

Notation "'@eval' X Y" := (@eval _ _ _ _ X Y)
  (at level 35) : hom_scope.

(** ** Transposition and Substitution

    Only products and exponentials are needed. No terminal object, equality
    of functions, or equality of chosen universal-property witnesses is used. *)

Section Exponential.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

Definition uncurry {X Y Z} (g : Hom Z (Y ^ X)) : Hom (Z × X) Y :=
  eval ∘ (g × id).

Global Instance exponential_uncurry_proper {X Y Z}
  : Proper (@HomEq[Z, Y ^ X] ==> @HomEq[Z × X, Y]) uncurry.
Proof. intros f g Hfg. unfold uncurry. rewrite Hfg. reflexivity. Qed.

Theorem exponential_β {X Y Z} (f : Hom (Z × X) Y)
  : uncurry (curry f) ≈ f.
Proof. exact (@this _ _ _ _ _ (exponential_curry_unique f)). Qed.

Theorem exponential_η {X Y Z} (g : Hom Z (Y ^ X))
  : curry (uncurry g) ≈ g.
Proof. symmetry. apply (exponential_curry_unique (uncurry g)). reflexivity. Qed.

(** The two respectful maps and the inverse laws give the hom-setoid
    correspondence. They retain their computational witness functions. *)
Program Definition exponential_curry_resp {X Y Z}
  : HomSet (Z × X) Y →r HomSet Z (Y ^ X) := {| func := curry |}.

Program Definition exponential_uncurry_resp {X Y Z}
  : HomSet Z (Y ^ X) →r HomSet (Z × X) Y := {| func := uncurry |}.

Lemma exponential_uncurry_comp_r {X Y Z W}
    (g : Hom Z (Y ^ X)) (σ : Hom W Z)
  : uncurry (g ∘ σ) ≈ uncurry g ∘ (σ × id).
Proof.
  unfold uncurry. rewrite comp_assoc, <- cross_comp, comp_id_l. reflexivity.
Qed.

Lemma exponential_curry_comp_r {X Y Z W}
    (f : Hom (Z × X) Y) (σ : Hom W Z)
  : curry (f ∘ (σ × id)) ≈ curry f ∘ σ.
Proof.
  symmetry. apply exponential_curry_unique.
  change (uncurry (curry f ∘ σ) ≈ f ∘ (σ × id)).
  rewrite exponential_uncurry_comp_r, exponential_β. reflexivity.
Qed.

(** Covariant action on the result type, with the argument object fixed. *)
Definition exponential_map {X Y Y'} (f : Hom Y Y') : Hom (Y ^ X) (Y' ^ X) :=
  curry (f ∘ eval).

Global Instance exponential_map_proper {X Y Y'}
  : Proper (@HomEq[Y, Y'] ==> @HomEq[Y ^ X, Y' ^ X]) exponential_map.
Proof. intros f g Hfg. unfold exponential_map. rewrite Hfg. reflexivity. Qed.

Lemma exponential_uncurry_comp_l {X Y Y' Z}
    (f : Hom Y Y') (g : Hom Z (Y ^ X))
  : uncurry (exponential_map f ∘ g) ≈ f ∘ uncurry g.
Proof.
  rewrite exponential_uncurry_comp_r.
  unfold exponential_map. rewrite exponential_β. apply comp_assoc.
Qed.

Lemma exponential_curry_comp_l {X Y Y' Z}
    (f : Hom Y Y') (g : Hom (Z × X) Y)
  : curry (f ∘ g) ≈ exponential_map f ∘ curry g.
Proof.
  symmetry. apply exponential_curry_unique.
  change (uncurry (exponential_map f ∘ curry g) ≈ f ∘ g).
  rewrite exponential_uncurry_comp_l, exponential_β. reflexivity.
Qed.

Lemma exponential_map_id {X Y} : exponential_map (@id Y) ≈ @id (Y ^ X).
Proof.
  unfold exponential_map. rewrite comp_id_l.
  transitivity (curry (uncurry (@id (Y ^ X)))).
  - apply exponential_curry_proper. unfold uncurry.
    rewrite cross_id, comp_id_r. reflexivity.
  - apply exponential_η.
Qed.

Lemma exponential_map_comp {X Y Y' Y''} (g : Hom Y' Y'') (f : Hom Y Y')
  : exponential_map (X := X) (g ∘ f) ≈ exponential_map g ∘ exponential_map f.
Proof.
  unfold exponential_map at 1 3. rewrite comp_assoc.
  apply exponential_curry_comp_l.
Qed.

(** Application is evaluation in a shared context. These are the equations
    needed for function beta/eta and semantic simultaneous substitution. *)
Definition app {X Y Z} (f : Hom Z (Y ^ X)) (a : Hom Z X) : Hom Z Y :=
  eval ∘ ⟨f, a⟩.

Global Instance exponential_app_proper {X Y Z}
  : Proper (@HomEq[Z, Y ^ X] ==> @HomEq[Z, X] ==> @HomEq[Z, Y]) app.
Proof. intros f f' Hf a a' Ha. unfold app. rewrite Hf, Ha. reflexivity. Qed.

Lemma exponential_app_comp {X Y Z W}
    (f : Hom Z (Y ^ X)) (a : Hom Z X) (σ : Hom W Z)
  : app f a ∘ σ ≈ app (f ∘ σ) (a ∘ σ).
Proof. unfold app. rewrite comp_assoc, product_comp_r. reflexivity. Qed.

Lemma exponential_app_β {X Y Z} (f : Hom (Z × X) Y) (a : Hom Z X)
  : app (curry f) a ≈ f ∘ ⟨id, a⟩.
Proof.
  rewrite <- (exponential_β f) at 2. unfold app, uncurry.
  rewrite comp_assoc, product_comp_l, comp_id_r, comp_id_l. reflexivity.
Qed.

Lemma exponential_app_η {X Y Z} (f : Hom Z (Y ^ X))
  : curry (app (f ∘ π1) π2) ≈ f.
Proof.
  transitivity (curry (uncurry f)).
  - apply exponential_curry_proper. unfold app, uncurry.
    rewrite cross_η, comp_id_l. reflexivity.
  - apply exponential_η.
Qed.

End Exponential.

(** ** The Product–Exponential Adjunction *)

Program Definition ExponentialF {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} (X : @Ob C)
  : Functor C C :=
  {| F0 Y := Y ^ X
   ; F1 Y Y' f := exponential_map f |}.
Next Obligation. apply exponential_map_id. Qed.
Next Obligation. apply exponential_map_comp. Qed.

Notation "'(-^' X ')'" := (ExponentialF X) : cat_scope.

Definition ProductExponentialAdjunction {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} (X : @Ob C)
  : (-× X) ⊣ (-^ X).
Proof.
  refine (AdjunctionFromHom (-× X) (-^ X)
    (λ Z Y, exponential_curry_resp) (λ Z Y, exponential_uncurry_resp)
    _ _ _ _).
  - intros Z Y f. apply exponential_β.
  - intros Z Y g. apply exponential_η.
  - intros Z Z' Y f h. apply exponential_curry_comp_r.
  - intros Z Y Y' k f. apply exponential_curry_comp_l.
Defined.

Theorem exponential_adjunct {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
    (f : Hom (Z × X) Y)
  : f^♯[ProductExponentialAdjunction X] ≈ ƛ f.
Proof. apply adjunct_from_hom. Qed.

Theorem exponential_unadjunct {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
    (g : Hom Z (Y ^ X))
  : g^♭[ProductExponentialAdjunction X] ≈ uncurry g.
Proof. apply unadjunct_from_hom. Qed.
