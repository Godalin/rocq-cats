From Cats Require Export
  Cat.Groupoid.Core.
From Cats Require Import
  Cat.CatCat
  Cat.Diagram.Initial
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal.

(** * Functors and Groupoids *)

(** * 函子与群胚 *)

(** Every functor from a groupoid sends arrows to isomorphisms, even when
    its target is not a groupoid. *)

(** 任意源于群胚的函子均将箭头送到同构，即使目标范畴不是群胚。 *)

Definition groupoid_fmap_iso {C D : Cat} `{HC : !IsGroupoid C}
    (F : Fct C D) {X Y : @Ob C} (f : Hom X Y)
  : is_iso (fmap F f)
  := functor_is_iso F f (groupoid_iso f).

(** Functors between groupoids preserve the selected inverses up to hom
    equality; no compatibility of the inverse choices is assumed. *)

(** 群胚间函子在 Hom 相等下保持选定逆，不额外假设两侧选逆相容。 *)

Lemma groupoid_fmap_inv {C D : Cat}
    `{HC : !IsGroupoid C} `{HD : !IsGroupoid D}
    (F : Fct C D) {X Y : @Ob C} (f : Hom X Y)
  : fmap F f⁻¹ ≈ (fmap F f)⁻¹.
Proof.
  apply groupoid_inv_unique.
  rewrite <- functor_comp, groupoid_inv_l. apply functor_id.
Qed.

(** Inversion is a contravariant functor, not an endofunctor with the same
    variance. It keeps objects and reverses arrows. *)

(** 取逆给出反变函子，保留对象并反转箭头，而非同方差的自函子。 *)

Program Definition InvF (C : Cat) `{HC : !IsGroupoid C}
  : Fct (C^op) C
  :=
  {|F0 X := X
  ; F1 X Y f := @groupoid_inv C HC Y X f
  |}.
Next Obligation.
  intros f g H. exact (@groupoid_inv_proper C HC Y X f g H).
Qed.
Next Obligation. exact (@groupoid_inv_id C HC X). Qed.
Next Obligation. exact (@groupoid_inv_comp C HC Z Y X g f). Qed.

(** A fully faithful functor into a groupoid makes its source a groupoid. *)

(** 到群胚的全忠实函子使其源范畴成为群胚。 *)

Program Definition fully_faithful_IsGroupoid {C D : Cat}
    (F : Fct C D) (HF : is_fully_faithful F)
    `{HD : !IsGroupoid D}
  : C ⦂ Gpd
  :=
  {|groupoid_iso X Y f := functor_reflects_iso F HF f (groupoid_iso _)
  |}.

(** A functor category with groupoid target is a groupoid. Inverses are the
    existing componentwise inverse natural transformations. *)

(** 目标为群胚的函子范畴也是群胚，逆直接复用已有的逐分量逆自然变换。 *)

Program Definition FctCat_IsGroupoid (C D : Cat) `{HD : !IsGroupoid D}
  : FctCat C D ⦂ Gpd
  :=
  {|groupoid_iso F G α := NatIso_is_iso α (λ X, groupoid_iso (α X))
  |}.

(** A category which is a retract of a groupoid up to natural isomorphism
    is a groupoid. Only the source-side retraction is needed. *)

(** 在自然同构下为群胚之收缩的范畴仍是群胚，只需源侧的收缩同构。 *)

Program Definition retract_IsGroupoid {C D : Cat}
    (F : Fct C D) (G : Fct D C)
    (α : (G ∘F F) ≅N (@IdF C)) `{HD : !IsGroupoid D}
  : C ⦂ Gpd
  :=
  {|groupoid_iso X Y f := _
  |}.
Next Obligation.
  pose (H := functor_is_iso G (fmap F f) (groupoid_iso (fmap F f))).
  pose (K := is_iso_comp H (α.2 Y)).
  pose (L := is_iso_comp (iso_symm (α.1 X; α.2 X)).2 K).
  refine (is_iso_equiv _ L).
  change ((α.1 Y ∘ fmap G (fmap F f)) ∘ (α.2 X).1 ≈ f).
  rewrite (nt_naturality α.1 f).
  cbn. rewrite comp_assoc, (snd (α.2 X).2), comp_id_r. reflexivity.
Defined.

(** Groupoid structure transports across an equivalence of categories.
    The equivalence uses natural isomorphisms, not equality of functors. *)

(** 群胚结构沿范畴等价传递；此等价使用自然同构，而非函子的原生相等。 *)

Definition equivalence_IsGroupoid {C D : Cat} (e : C ≃C D)
    `{HC : !IsGroupoid C}
  : D ⦂ Gpd
  := retract_IsGroupoid e.2.1 e.1 (snd e.2.2).

(** A diagram in a groupoid with an initial source position is naturally
    isomorphic to the constant diagram at that position. Its components
    are images of the universal arrows, so their inverses are constructive. *)

(** 定义域有始位置的群胚值图式自然同构于该位置处的常图式。比较分量是泛箭头
    的像，因而其逆可构造。 *)

Definition groupoid_initial_diagram_iso {J C : Cat}
    `{HC : !IsGroupoid C} {j : @Ob J}
    (Hj : is_initial j) (F : Fct J C)
  : ConstF J (F j) ≅N F.
Proof.
  exists (InitialCone Hj F). intros k. apply groupoid_iso.
Defined.
