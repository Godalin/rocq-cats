From Cats Require Export Cat.Exponential.Core.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Exponential.Functor.

(** * Transport of Exponential Objects

    Changing the argument and result by isomorphisms preserves the full
    exponential property, with the same representing object. *)

(** * 指数对象的同构运输

    沿参数与结果的同构变换保持完整指数泛性质，表示对象保持相同。 *)

Section ExponentialTransport.
Context {C : Cat} `{HP : !HasProduct C}.

(** Equivalent evaluation arrows have the same universal property, retaining
    the original mediator function. *)

(** 相等的求值箭头具有相同泛性质，并保留原中介函数。 *)

Definition exponential_eval_equiv {X Y E : @Ob C}
    {ev ev' : Hom (E × X) Y} (H : ev ≈ ev')
    (HE : is_exponential X Y E ev)
  : is_exponential X Y E ev'.
Proof.
  intros Z f. destruct (HE Z f) as [h [Hh Hunique]].
  exists h.
  refine {|this := _
         ; that := _
         |}.
  - rewrite <- H. exact Hh.
  - intros k Hk. apply Hunique. rewrite H. exact Hk.
Defined.

(** Transport evaluation contravariantly in its argument and covariantly in
    its result. The original universal property supplies the mediator; its
    input change uses explicit pairing to retain computation. All inverse and
    uniqueness laws use only hom equality. *)

(** 求值对参数反变、对结果协变地运输。原泛性质给出中介，其输入变换使用显式
    配对以保持计算；所有互逆律及唯一性仅使用 Hom 指定的相等。 *)

Definition exponential_transport {X Y E X' Y' : @Ob C}
    (i : X' ≅ X) (j : Y ≅ Y') (ev : Hom (E × X) Y)
    (H : is_exponential X Y E ev)
  : is_exponential X' Y' E (j.1 ∘ ev ∘ (id × i.1)).
Proof.
  destruct i as [u [ui [Hu Huu]]], j as [v [vi [Hv Hvv]]]; cbn.
  intros Z f.
  destruct (H Z (vi ∘ f ∘ ⟨π1, ui ∘ π2⟩)) as [h [Hh Hunique]].
  assert (Harg : ⟨(π1 : Hom (Z × X) Z), ui ∘ π2⟩ ≈ id × ui).
  { rewrite cross_η, comp_id_l. reflexivity. }
  exists h.
  refine {|this := _
         ; that := _
         |}.
  - rewrite (comp_assoc (v ∘ ev) (id × u) (h × id)).
    rewrite (cross_exchange h u).
    rewrite <- (comp_assoc (v ∘ ev) (h × id) (id × u)).
    rewrite (comp_assoc v ev (h × id)), Hh, Harg.
    rewrite <- !comp_assoc, Hvv, comp_id_l.
    rewrite comp_assoc, <- cross_comp, Hu, comp_id_l, cross_id, comp_id_r.
    reflexivity.
  - intros k Hk. apply Hunique. rewrite Harg.
    rewrite <- Hk.
    rewrite <- !comp_assoc, Hv, comp_id_l.
    rewrite (comp_assoc ev (id × u) (k × id)), (cross_exchange k u).
    rewrite <- (comp_assoc ev (k × id) (id × u)).
    rewrite comp_assoc, <- cross_comp, Huu, comp_id_l, cross_id, comp_id_r.
    reflexivity.
Defined.

End ExponentialTransport.

(** Isomorphisms of arguments and results induce an exponential isomorphism. *)

(** 参数与结果的同构诱导指数同构。 *)

Definition exponential_iso {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y X' Y' : @Ob C}
    (i : X ≅ X') (j : Y ≅ Y')
  : (Y ^ X) ≅ (Y' ^ X').
Proof.
  exists (j.1 ^ i.2.1)%hom, (j.2.1 ^ i.1)%hom. split;
    unfold is_linv_of, is_rinv_of;
    rewrite <- exponential_dimap_comp;
    [rewrite (fst i.2.2), (fst j.2.2) |
     rewrite (snd i.2.2), (snd j.2.2)]; apply exponential_dimap_id.
Defined.

(** The induced exponential isomorphism intertwines the two evaluations. *)

(** 诱导的指数同构使两侧求值相容。 *)

Lemma exponential_iso_eval {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y X' Y' : @Ob C}
    (i : X ≅ X') (j : Y ≅ Y')
  : eval ∘ ((exponential_iso i j).1 × i.1) ≈ j.1 ∘ eval.
Proof.
  change (eval ∘ ((j.1 ^ i.2.1) × i.1)%hom ≈ j.1 ∘ eval).
  transitivity ((eval ∘ ((j.1 ^ i.2.1) × id)%hom) ∘ (id × i.1)%hom).
  - rewrite comp_assoc, <- cross_comp, comp_id_l, comp_id_r. reflexivity.
  - rewrite exponential_dimap_eval, comp_assoc,
      <- cross_comp, (fst i.2.2), comp_id_l, cross_id, comp_id_r.
    reflexivity.
Qed.

(** Evaluation after an invertible change of input still determines a map
    into an exponential. *)

(** 输入作可逆变换之后，求值仍能确定指向指数的箭头。 *)

Lemma exponential_ext_iso {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X X' Y Z : @Ob C} (i : X' ≅ X)
    {f g : Hom Z (Y ^ X)}
    (H : eval ∘ (f × i.1) ≈ eval ∘ (g × i.1))
  : f ≈ g.
Proof.
  apply exponential_ext.
  assert (K : (eval ∘ (f × i.1)) ∘ (id × i.2.1) ≈
    (eval ∘ (g × i.1)) ∘ (id × i.2.1)).
  { apply comp_proper; [exact H | reflexivity]. }
  rewrite !comp_assoc, <- !cross_comp, !comp_id_r, (snd i.2.2) in K.
  exact K.
Qed.
