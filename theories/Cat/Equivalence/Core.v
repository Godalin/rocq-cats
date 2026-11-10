From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Isomorphism
  Cat.CatCat.

(** * Computational Consequences of Specified Equivalences

    The general statements accept quasi-inverse functors and their two
    natural isomorphisms separately. Their native hom and equality universes
    remain independent; no triangle identities are assumed. *)

(** * 指定等价的计算性推论

    一般陈述分别接受拟逆函子及两个自然同构，保持两侧原生 Hom 与相等宇宙
    独立，不假设三角恒等式。 *)

Local Open Scope cat_scope.
Local Open Scope hom_scope.

(** Faithfulness transfers across a specified natural isomorphism. *)

(** 忠实性沿指定自然同构运输。 *)

Definition nat_iso_faithful {C D : Cat} {F G : Functor C D}
    (i : F ≅N G) (HG : is_faithful G)
  : is_faithful F.
Proof.
  intros X Y f g H. apply HG.
  apply (iso_cancel_r (i.1 X; i.2 X)).
  rewrite <- (nt_naturality i.1 f), <- (nt_naturality i.1 g), H.
  reflexivity.
Defined.

(** Fullness transports actual preimages by conjugating with the supplied
    components; only specified hom equality is used. *)

(** 满性通过与给定分量共轭运输实际原像，仅使用指定 Hom 相等。 *)

Definition nat_iso_full {C D : Cat} {F G : Functor C D}
    (i : F ≅N G) (HG : is_full G)
  : is_full F.
Proof.
  intros X Y h.
  destruct (HG X Y (i.1 Y ∘ h ∘ (i.2 X).1)) as [f Hf].
  exists f. apply (iso_cancel_l (i.1 Y; i.2 Y)).
  rewrite (nt_naturality i.1 f), Hf, !comp_assoc,
    (fst (i.2 X).2), comp_id_r.
  reflexivity.
Defined.

(** A functor with a left quasi-inverse reflects hom equality. One natural
    isomorphism suffices. *)

(** 具有左拟逆的函子反映 Hom 相等，只需一个自然同构。 *)

Definition quasi_inverse_faithful {C D : Cat}
    (F : Functor C D) (G : Functor D C) (u : (G ∘F F) ≅N IdF)
  : is_faithful F.
Proof.
  intros X Y f g H.
  apply (nat_iso_faithful u (λ X Y f g H, H) X Y f g).
  exact (@functor_fmap_proper D C G _ _ _ _ H).
Defined.

(** Two quasi-inverse isomorphisms give full preimages without coherence
    assumptions: fullness of [G ∘F F] is reflected by faithfulness of [G]. *)

(** 两个拟逆同构无需相干假设即可给出满性的原像：由 [G] 的忠实性反映
    [G ∘F F] 的满性。 *)

Definition quasi_inverse_full {C D : Cat}
    (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF)
  : is_full F.
Proof.
  intros X Y h.
  assert (Hid : is_full (@IdF C)).
  { intros A B f. exists f. reflexivity. }
  destruct (nat_iso_full u Hid X Y (fmap G h)) as [f Hf].
  exists f. exact (quasi_inverse_faithful G F v _ _ _ _ Hf).
Defined.

(** Fullness and faithfulness retain the same explicit preimage operation. *)

(** 满性与忠实性的组合保留同一个显式原像运算。 *)

Definition quasi_inverse_fully_faithful {C D : Cat}
    (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF)
  : is_fully_faithful F
  := (quasi_inverse_full F G u v, quasi_inverse_faithful F G u).

(** The right quasi-inverse provides an object representative and its
    isomorphism, with no truncated choice. *)

(** 右拟逆给出对象代表及其同构，不使用截断选择。 *)

Definition quasi_inverse_essentially_surjective {C D : Cat}
    (F : Functor C D) (G : Functor D C) (v : (F ∘F G) ≅N IdF)
  : is_essentially_surjective F
  := λ Y, (G Y; (v.1 Y; v.2 Y)).

(** The ordinary category-equivalence notation supplies these hypotheses. *)

(** 通常的范畴等价记号提供上述假设。 *)

Definition equivalence_fully_faithful {C D : Cat} (e : C ≃C D)
  : is_fully_faithful e.1
  := quasi_inverse_fully_faithful e.1 e.2.1
      (fst e.2.2) (snd e.2.2).

(** The inverse functor is fully faithful by the same construction. *)

(** 逆函子的全忠实性由同一构造给出。 *)

Definition equivalence_inverse_fully_faithful {C D : Cat} (e : C ≃C D)
  : is_fully_faithful e.2.1
  := quasi_inverse_fully_faithful e.2.1 e.1
      (snd e.2.2) (fst e.2.2).

(** Essential surjectivity keeps the chosen inverse object and component. *)

(** 本质满性保留选定的逆像对象及分量。 *)

Definition equivalence_essentially_surjective {C D : Cat} (e : C ≃C D)
  : is_essentially_surjective e.1
  := quasi_inverse_essentially_surjective e.1 e.2.1 (snd e.2.2).
