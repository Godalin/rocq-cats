From Cats Require Import
  Cat.Core
  Cat.Morphism
  Cat.Equalizer
  Cat.EqualizerMorphism.

(** * Images and Epimorphic Factors

    An image is a least monomorphism through which a supplied arrow
    factors. Keep the Type-valued factor witnesses. Equalizers alone
    suffice to prove the factor into any image epimorphic. *)

(** * 像与满分解箭头

    像是给定箭头所经的最小单态射，保留 Type 值分解见证。
    仅用等化子即可证明进入任意像的分解箭头为满态射。 *)

(** The candidate image property supplies a factor and a factor into
    every other containing subobject, without choosing a new object. *)

(** 候选像性质提供分解因子及进入任意其他包含子对象的因子，不另选对象。 *)

Definition is_image {C : Cat} {X Y I : C} (f : Hom X Y) (m : I ↣ Y)
  : Type
  := is_factored_through m f ∧
      ∀ s : Sub Y, is_factored_through s f → is_factored_through s m.

(** For any given factorization through a candidate image, equalize two
    outputs agreeing after the factor. Image minimality splits that
    equalizer inclusion, proving cancellation in specified hom equality. *)

(** 对经候选像的任意给定分解，等化在因子后相等的两个后继箭头。像最小性
    分裂此等化子包含，从而在指定 Hom 相等下证明消去。 *)

Theorem image_factor_epi {C : Cat} `{EQ : !HasEqualizer C}
    {X Y I : C} {f : Hom X Y} {m : I ↣ Y} (HI : is_image f m)
    (e : Hom X I) (H : m ∘ e ≈ f)
  : is_epi e.
Proof.
  intros Z u v Huv.
  pose (j := @eqι C EQ I Z u v).
  pose (E := @equalizer_universal C EQ I Z u v).
  pose (s := {|sub := @EqObj C EQ I Z u v
             ; sub_mono := Mono_comp m (EqualizerMono E)
             |}).
  assert (Hf : is_factored_through s f).
  { pose (q := @equalize C EQ I Z X u v e Huv).
    exists q. change (f ≈ (m ∘ j) ∘ q).
    rewrite comp_assoc. transitivity (m ∘ e).
    - symmetry. exact H.
    - apply comp_proper; [reflexivity | symmetry].
      exact (@equalizer_β C EQ I Z X u v e Huv). }
  destruct (snd HI s Hf) as [r Hr].
  assert (Hs : j ∘ r ≈ (@Cats.Cat.Core.id C I)).
  { apply (@mor_mono C I Y m I (j ∘ r) (@Cats.Cat.Core.id C I)).
    rewrite <- comp_assoc. transitivity (m : Hom I Y).
    - symmetry. exact Hr.
    - symmetry. apply comp_id_r. }
  assert (Hcomm : u ∘ j ≈ v ∘ j) by exact (fst E).
  transitivity (u ∘ (j ∘ r)).
  - rewrite Hs, comp_id_r. reflexivity.
  - rewrite <- comp_assoc, Hcomm, comp_assoc, Hs, comp_id_r.
    reflexivity.
Qed.
