From Cats Require Export
  Cat.Monoidal.Semigroupal
  Cat.Monoidal.Premonoidal.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Monoidal Categories

    A monoidal category extends a semigroupal category by unitors
    compatible with its associator. *)

(** * 幺半范畴

    幺半范畴在半群张量范畴上增加与结合子相容的单位子。 *)

(** Combine the two branches on their shared binoidal tensor and associator. *)

(** 在共享的双侧张量和结合子上组合两条分支。 *)

Minks.Struct MonoidalCat
  extends SemigroupalCat, PremonoidalCat
  exports HasMonoidal [carrier].

(** Fix the tensor interchange and the unitors. Their joint bifunctor
    views retain the same component maps and inverses. *)

(** 固定张量的交换律及单位子。其联合双函子视图沿用同一组分量映射与逆。 *)

Section Coherence.
Context {C : Cat}
  `{BC : !HasBinoidal C} `{IM : !@IsMagmoidal C BC}.

(** The joint unitors use only the chosen unitor package. *)

(** 联合单位子仅使用已选定的单位子结构。 *)

Section Unit.
Context `{UC : !@HasTensorUnitors C BC}.

(** The joint left unitor retains its selected component inverses. *)

(** 联合左单位子沿用选定的分量逆。 *)

Program Definition TensorUnitorLIsoN
  : AtLF tensorF 𝐈 ≅N IdF
  := ({|nt X := λ[X]|}; λ X, (tensor_unitor_l X).2).
Next Obligation.
  change (λ[Y] ∘ (id[𝐈] ⊗ f) ≈ f ∘ λ[X]).
  unfold tensor_map. rewrite tensor_sequence_left.
  apply tensor_unitor_l_natural.
Qed.

(** The joint right unitor retains its selected component inverses. *)

(** 联合右单位子沿用选定的分量逆。 *)

Program Definition TensorUnitorRIsoN
  : AtRF tensorF 𝐈 ≅N IdF
  := ({|nt X := ρ[X]|}; λ X, (tensor_unitor_r X).2).
Next Obligation.
  change (ρ[Y] ∘ (f ⊗ id[𝐈]) ≈ f ∘ ρ[X]).
  unfold tensor_map. rewrite tensor_sequence_right.
  apply tensor_unitor_r_natural.
Qed.

End Unit.

(** Fix a premonoidal structure together with interchange. The triangle
    then has a joint-tensor formulation. *)

(** 固定预幺半结构和交换律，以联合张量表述三角形。 *)

Context `{AC : !@HasTensorAssoc C BC}
  `{UC : !@HasTensorUnitors C BC}
  `{IP : !@IsPremonoidal C BC AC UC}.

(** The inherited triangle expressed with the derived bimap. *)

(** 用导出的二元映射表述继承的三角形。 *)

Lemma tensor_map_triangle (X Y : C)
  : (id ⊗ λ[Y]) ∘ α[X; 𝐈; Y] ≈ ρ[X] ⊗ id.
Proof.
  unfold tensor_map.
  rewrite tensor_sequence_left, tensor_sequence_right.
  apply tensor_triangle.
Qed.

End Coherence.
