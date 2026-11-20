From Cats Require Export
  Cat.Monoidal.Semigroupal.
From Cats Require Import
  Cat.Monoidal.PremonoidalLaws.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Coherence of the Tensor Bifunctor

    This module derives the joint unitors and triangle for the
    assembled tensor bifunctor. *)

(** * 张量双函子的相干性

    本模块给出组装后张量双函子的联合单位子及三角形。 *)

(** Fix the tensor interchange and the unitors. Their joint bifunctor
    views retain the same component maps and inverses. *)

(** 固定张量的交换律及单位子。其联合双函子视图沿用同一组分量映射与逆。 *)

Section Unit.
Context {C : Cat}
  `{BC : !HasBinoidal C} `{IM : !IsMagmoidal BC}
  `{UC : !HasUnitors C BC}.

(** Package the inherited left unitor as a natural transformation. *)

(** 将继承左单位子打包为自然变换。 *)

Local Program Definition TensorLeftUnitorN
  : AtLF (tensorF IM) (𝐈[UC]) ⇒ IdF
  :=
  {|nt X := λ[X]
  |}.
Next Obligation.
  change (λ[Y] ∘ (id[𝐈[UC]] ⊗ f) ≈ f ∘ λ[X]).
  unfold tensor_map. rewrite tensor_sequence_left.
  apply tensor_unitor_l_natural.
Qed.

(** Package the inherited right unitor as a natural transformation. *)

(** 将继承右单位子打包为自然变换。 *)

Local Program Definition TensorRightUnitorN
  : AtRF (tensorF IM) (𝐈[UC]) ⇒ IdF
  :=
  {|nt X := ρ[X]
  |}.
Next Obligation.
  change (ρ[Y] ∘ (f ⊗ id[𝐈[UC]]) ≈ f ∘ ρ[X]).
  unfold tensor_map. rewrite tensor_sequence_right.
  apply tensor_unitor_r_natural.
Qed.

(** The natural left-unitor isomorphism keeps its selected inverse. *)

(** 左单位自然同构保留其选定逆。 *)

Definition TensorUnitorLIsoN
  : AtLF (tensorF IM) (𝐈[UC]) ≅N IdF
  := (TensorLeftUnitorN; λ X, (tensor_unitor_l X).2).

(** The natural right-unitor isomorphism keeps its selected inverse. *)

(** 右单位自然同构保留其选定逆。 *)

Definition TensorUnitorRIsoN
  : AtRF (tensorF IM) (𝐈[UC]) ≅N IdF
  := (TensorRightUnitorN; λ X, (tensor_unitor_r X).2).

End Unit.

(** Fix a premonoidal structure together with interchange. The triangle
    then has a joint-tensor formulation. *)

(** 固定预幺半结构和交换律，以联合张量表述三角形。 *)

Section Triangle.
Context {C : Cat} `{BC : !HasBinoidal C} `{IM : !IsMagmoidal BC}
  `{PC : !HasPremonoidal C BC}.

(** The inherited triangle expressed with the derived bimap. *)

(** 用导出的二元映射表述继承的三角形。 *)

Lemma tensor_map_triangle (X Y : @Ob C)
  : (id ⊗ λ[Y]) ∘ α[X; 𝐈[PC]; Y] ≈ ρ[X] ⊗ id.
Proof.
  unfold tensor_map. rewrite tensor_sequence_left, tensor_sequence_right.
  apply tensor_triangle.
Qed.

End Triangle.
