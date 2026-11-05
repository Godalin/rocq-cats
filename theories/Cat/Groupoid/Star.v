From Cats Require Export
  Cat.Groupoid.Core.
From Cats Require Import
  Cat.Functor.Core
  Cat.Natural
  Cat.Shape.Ordinal.

(** * Diagrams Determined by a Common Source

    In a groupoid, arrows from one centre determine all transitions.
    Ordinal diagrams admit such a description from their initial vertex. *)

(** * 由共同源确定的图式

    群胚中，从一个中心出发的箭头确定全部过渡；序数图式的首顶点提供这种描述。 *)

Section Stars.
Context {C : Cat} `{HC : !IsGroupoid C}.

(** A star gives a diagram on any indexing category. Each transition
    follows the inverse incoming leg and then the outgoing leg. *)

(** 星形数据给出任意索引范畴上的图式；每个过渡先沿入腿的逆，再沿出腿。 *)

Program Definition StarF (J : Cat) (A : @Ob C)
    (v : @Ob J → @Ob C) (s : ∀ j, Hom A (v j))
  : Functor J C
  :=
  {|F0 := v
  ; F1 i j f := s j ∘ (s i)⁻¹
  |}.
Next Obligation. intros f g H. reflexivity. Defined.
Next Obligation. apply groupoid_inv_r. Defined.
Next Obligation.
  rewrite comp_assoc, <- (comp_assoc (s Y)⁻¹), groupoid_inv_l,
    comp_id_l. reflexivity.
Defined.

(** Two stars commute on every transition if their legs commute with one
    common centre map. No equality of centre or leg data is required. *)

(** 两个星形的腿若与同一个中心映射交换，则全部过渡交换；不比较中心或腿的原生相等。 *)

Lemma star_transition_square {A B V W V' W' : @Ob C}
    (s : Hom A V) (t : Hom A W) (s' : Hom B V') (t' : Hom B W')
    (a : Hom V V') (b : Hom W W') (c : Hom A B)
    (Hs : a ∘ s ≈ s' ∘ c) (Ht : b ∘ t ≈ t' ∘ c)
  : b ∘ (t ∘ s⁻¹) ≈ (t' ∘ (s')⁻¹) ∘ a.
Proof.
  apply (iso_cancel_r (groupoid_arrow_iso s)).
  rewrite !comp_assoc, groupoid_inv_l, comp_id_r, Hs,
    <- (comp_assoc (s')⁻¹), groupoid_inv_l, comp_id_l. exact Ht.
Defined.

(** A commuting square of invertible arrows also commutes backwards. *)

(** 可逆箭头的交换方块在反向也交换。 *)

Lemma groupoid_inverse_square {A B A' B' : @Ob C}
    (f : Hom A B) (g : Hom A' B') (a : Hom A A') (b : Hom B B')
    (H : b ∘ f ≈ g ∘ a)
  : a ∘ f⁻¹ ≈ g⁻¹ ∘ b.
Proof.
  apply (iso_cancel_r (groupoid_arrow_iso f)).
  rewrite !comp_assoc, groupoid_inv_l, comp_id_r, H,
    <- comp_assoc, groupoid_inv_l, comp_id_l. reflexivity.
Defined.

(** Extend an ordinal diagram to transitions between arbitrary positions,
    including the backward ones. All inverse choices come from C. *)

(** 将序数图式延拓到任意位置间的过渡，包括逆向过渡；全部逆选择来自 C。 *)

Definition ordinal_radial {n : nat} (F : Functor [Ord n] C)
    (i j : Ordinal n)
  : Hom (F i) (F j)
  := fmap F (ordinal_from_first j) ∘ (fmap F (ordinal_from_first i))⁻¹.

(** Existing directed arrows are exactly these transitions. *)

(** 原有有向箭头恰等于这些过渡。 *)

Lemma ordinal_radial_arrow {n : nat} (F : Functor [Ord n] C)
    {i j : Ordinal n} (f : (@Hom [Ord n]) i j)
  : fmap F f ≈ ordinal_radial F i j.
Proof.
  unfold ordinal_radial.
  apply (iso_cancel_r (groupoid_arrow_iso (fmap F (ordinal_from_first i)))).
  rewrite comp_assoc, groupoid_inv_l, comp_id_r.
  transitivity (fmap F (f ∘ ordinal_from_first i)).
  - symmetry. exact (@functor_comp [Ord n] C F fin_first i j
      f (ordinal_from_first i)).
  - exact (@functor_fmap_proper [Ord n] C F fin_first j _ _ tt).
Defined.

(** Radial transitions compose without any ordering hypothesis. *)

(** 径向过渡的复合不要求位置间有顺序关系。 *)

Lemma ordinal_radial_comp {n : nat} (F : Functor [Ord n] C)
    (i j k : Ordinal n)
  : ordinal_radial F j k ∘ ordinal_radial F i j ≈ ordinal_radial F i k.
Proof.
  unfold ordinal_radial.
  rewrite comp_assoc, <- (comp_assoc (fmap F (ordinal_from_first j))⁻¹),
    groupoid_inv_l, comp_id_l. reflexivity.
Defined.

(** Reversing a radial transition gives its selected inverse. *)

(** 反转径向过渡得到其选定逆。 *)

Lemma ordinal_radial_inv {n : nat} (F : Functor [Ord n] C)
    (i j : Ordinal n)
  : (ordinal_radial F i j)⁻¹ ≈ ordinal_radial F j i.
Proof.
  unfold ordinal_radial. rewrite groupoid_inv_comp, groupoid_inv_inv.
  reflexivity.
Defined.

(** Natural transformations commute with arbitrary radial transitions. *)

(** 自然变换与任意径向过渡交换。 *)

Lemma ordinal_radial_natural {n : nat} {F G : Functor [Ord n] C}
    (α : F ⇒ G) (i j : Ordinal n)
  : α j ∘ ordinal_radial F i j ≈ ordinal_radial G i j ∘ α i.
Proof.
  apply (star_transition_square _ _ _ _ _ _ (α fin_first));
    apply nt_naturality.
Defined.

(** Radial transitions commute with ordinal substitution, even when the
    substituted diagram starts at a different vertex. *)

(** 径向过渡与序数替换交换，即使替换后的图式从另一个顶点开始。 *)

Lemma ordinal_radial_precomp {m n : nat} (F : Functor [Ord n] C)
    (Q : Functor [Ord m] [Ord n]) (i j : Ordinal m)
  : ordinal_radial (F ∘F Q) i j ≈ ordinal_radial F (Q i) (Q j).
Proof.
  pose (c := fmap F (ordinal_from_first (Q fin_first))).
  assert (H : ∀ k, id ∘ fmap (F ∘F Q) (ordinal_from_first k) ≈
      fmap F (ordinal_from_first (Q k)) ∘ c⁻¹).
  { intros k. rewrite comp_id_l.
    apply (iso_cancel_r (groupoid_arrow_iso c)).
    rewrite comp_assoc, groupoid_inv_l, comp_id_r.
    change (fmap F (fmap Q (ordinal_from_first k)) ∘
      fmap F (ordinal_from_first (Q fin_first)) ≈
      fmap F (ordinal_from_first (Q k))).
    transitivity (fmap F (fmap Q (ordinal_from_first k) ∘
      ordinal_from_first (Q fin_first))).
    - symmetry. exact (@functor_comp [Ord n] C F _ _ _ _ _).
    - exact (@functor_fmap_proper [Ord n] C F _ _ _ _ tt). }
  pose proof (star_transition_square _ _ _ _ id id c⁻¹ (H i) (H j)) as K.
  rewrite comp_id_l, comp_id_r in K. exact K.
Defined.

End Stars.

Notation "'ρ[' F ';' i ';' j ']'" := (ordinal_radial F i j) : hom_scope.
