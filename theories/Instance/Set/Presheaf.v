From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.Core.
From Cats Require Import Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Yoneda.



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

(** * Yoneda Embedding into Larger Value Universes *)

(** * 进入更大值宇宙的 Yoneda 嵌入 *)

(** Lift representables into an independently chosen pair of value universes.
    This also applies when the category is small and its presheaves are large. *)

(** 将可表函子提升到独立选择的一对值宇宙；适用于小范畴上的较大预层。 *)

Program Definition RaisedEmbedding@{u p +} {C : Cat}
  : Functor C (Fct (C^op) SetCat@{u p _ _ _ _ _})
  :=
  {|F0 X := LiftF ∘F Hom(-,X)
  ; F1 X Y f := LiftF ∘Nl f _*N
  |}.
Next Obligation.
  intros f g H Z [h].
  exact {|lower := @comp_proper C _ _ _ f g H h h (reflexivity h)
         |}.
Defined.
Next Obligation.
  intros Z [h]. exact {|lower := comp_id_l h
                      |}.
Defined.
Next Obligation.
  intros W [h]. exact {|lower := comp_assoc f g h
                      |}.
Defined.

(** Raising values preserves full faithfulness. Yoneda reconstruction gives
    fullness; identity evaluation recovers the original arrow for faithfulness. *)

(** 提升值保持全忠实性；Yoneda 重构给出满性，恒等处求值恢复原箭头而给出忠实性。 *)

Theorem raised_embedding_fully_faithful@{u p +} {C : Cat}
  : is_fully_faithful
      (RaisedEmbedding : Functor C (Fct (C^op) SetCat@{u p _ _ _ _ _})).
Proof.
  split.
  - intros X Y α. exists (lower (presheaf_yoneda_resp
      (C := C) (P := RaisedEmbedding Y) (X := X) α)).
    exact (presheaf_yoneda_η α).
  - intros X Y f g H.
    transitivity (f ∘ id). symmetry. apply comp_id_r.
    transitivity (g ∘ id).
    + exact (lower (H X {|lower := id
                        |})).
    + apply comp_id_r.
Defined.
