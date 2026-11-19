From Cats Require Import
  Cat.Core
  Cat.Equalizer
  Cat.Morphism.

(** * Equalizer Inclusions and Factors

    A candidate equalizer is already monic. Package that same inclusion
    and retain the universal factor, without selecting any new limits. *)

(** * 等化子包含与分解

    候选等化子已是单态射。打包同一包含箭头并保留泛分解，不另选任何极限。 *)

(** Package a candidate equalizer inclusion using its cancellation law. *)

(** 由候选等化子的消去律打包其包含箭头。 *)

Program Definition EqualizerMono {C : Cat} {X Y E : C}
    {f g : Hom X Y} {e : Hom E X} (HE : is_equalizer f g E e)
  : E ↣ X
  :=
  {|mor := e
  |}.
Next Obligation.
  intros Q u v H. exact (equalizer_hom_ext HE u v H).
Defined.

(** Factoring through this inclusion is equivalent to equalizing the
    parallel pair. The reverse map keeps the supplied universal mediator. *)

(** 经过此包含箭头分解等价于等化平行箭头对；反向保留给定的泛中介。 *)

Definition equalizer_factor {C : Cat} {X Y E Q : C}
    {f g : Hom X Y} {e : Hom E X} (HE : is_equalizer f g E e)
    (q : Hom Q X)
  : is_factored_through (EqualizerMono HE) q ↔ f ∘ q ≈ g ∘ q.
Proof.
  split.
  - intros [h Hh]. change (q ≈ e ∘ h) in Hh.
    rewrite Hh, <- !comp_assoc, (fst HE). reflexivity.
  - intros Hq. pose (u := snd HE Q q Hq).
    exists u.1. symmetry. exact (this u.2).
Defined.
