From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.Core.
From Cats Require Import Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom.



(** * The Category of Presheaves *)

(** * 预层范畴 *)

(** Presheaves are contravariant setoid-valued functors with natural
    transformations. *)

(** 预层是反变广集值函子，其态射为自然变换。 *)

Definition Psh C
  := Fct (op C) SetCat.

Section Psh.
Context {C : Cat}.

(** The Yoneda embedding sends an object to its contravariant representable. *)

(** Yoneda 嵌入将对象送到其反变可表函子。 *)

Program Canonical Embedding
  : Functor C (Psh C)
  :=
  {|F0 := ℎ2F
  ; F1 X Y f := f _*N
  |}.
Next Obligation. apply nt_comp_post_id. Qed.
Next Obligation. apply nt_comp_post_comp. Qed.

(** A natural transformation between representables is determined by its value
    on the identity. Keep the inverse transparent. *)

(** 可表函子之间的自然变换由其在恒等态射处的值决定；逆映射保持透明。 *)

Theorem embedding_hom_iso {X Y : @Ob C}
  : @is_iso SetCat _ _ (fmap_resp Embedding (X := X) (Y := Y)).
Proof.
  unshelve notypeclasses refine (({|func := _
                                  |}); _).
  - exact (λ α, α X id).
  - intros α β Hαβ. exact (Hαβ X id).
  - split.
    + intros f. change (f ∘ id ≈ f). apply comp_id_r.
    + intros α Z h. change (α X id ∘ h ≈ α Z h).
      pose proof (nt_naturality α (X := X) (Y := Z) h) as Hα.
      specialize (Hα id). simpl in Hα. rewrite comp_id_l in Hα.
      symmetry. exact Hα.
Defined.

(** The Yoneda embedding is fully faithful by the representable hom
    correspondence. *)

(** 由可表函子的 Hom 对应，Yoneda 嵌入全忠实。 *)

Theorem embedding_fully_faithful
  : is_fully_faithful Embedding.
Proof.
  apply (snd (functor_fully_faithful_iff_hom_iso Embedding)).
  intros X Y. apply embedding_hom_iso.
Defined.

End Psh.
