From Cats.Set Require Import
  Subset.
From Cats Require Import
  Cat.Isomorphism.
From Cats Require Export
  Cat.Monoidal.Functor.

Local Open Scope monoidal_scope.

(** * Monoidal Natural Transformations between Lax Functors *)

(** * Lax 函子之间的幺半自然变换 *)

(** ** Preservation on a Supplied Transformation

    Fix monoidal structures on named source and target categories. A monoidal
    natural transformation preserves the unit comparison and tensorator.
    Neither the lax comparisons nor the transformation need be invertible;
    no strength, symmetry, cartesian structure or coends are required. *)

(** ** 给定变换上的保持性

    固定具名来源及目标范畴上的幺半结构。幺半自然变换保持单位比较及张量子。
    不要求 lax 比较或变换可逆，也不需要强度、对称、笛卡尔结构或 coend。 *)

Section Preservation.
Context {C D : Cat} {MC : MonoidalCat C} {MD : MonoidalCat D}.
Local Existing Instance MD.

(** Type-valued diagrams on existing data, without equality of law records. *)

(** 已有数据上的 Type 值交换图，不要求定律记录相等。 *)

Definition is_lax_monoidal_hom (L K : LaxMonoidalFct MC MD) (α : L ⇒ K)
  : Type
  := (α (TensorUnit MC) ∘ φ₀[L] ≈ φ₀[K]) ∧
      (∀ X Y, α (@tensor C MC X Y) ∘ φ₂[L; X; Y] ≈
        φ₂[K; X; Y] ∘ @tensor_map D MD _ _ _ _ (α X) (α Y)).

(** Naturally equal transformations have the same preservation property. *)

(** 自然相等的变换具有相同保持性。 *)

Lemma lax_monoidal_hom_equiv (L K : LaxMonoidalFct MC MD) (α β : L ⇒ K)
    (E : α ≈N β)
  : is_lax_monoidal_hom L K α ↔ is_lax_monoidal_hom L K β.
Proof.
  split; intros [Hu Ht]; split.
  - rewrite <- (E (TensorUnit MC)). exact Hu.
  - intros X Y. rewrite <- (E (@tensor C MC X Y)), <- (E X), <- (E Y).
    exact (Ht X Y).
  - rewrite (E (TensorUnit MC)). exact Hu.
  - intros X Y. rewrite (E (@tensor C MC X Y)), (E X), (E Y).
    exact (Ht X Y).
Defined.

(** Identity preserves the selected comparisons. *)

(** 恒等变换保持选定比较。 *)

Lemma lax_monoidal_hom_id (L : LaxMonoidalFct MC MD)
  : is_lax_monoidal_hom L L idN.
Proof.
  split; cbn; intros; rewrite ?tensor_map_id, ?comp_id_l, ?comp_id_r;
    reflexivity.
Defined.

(** Vertical composition preserves both comparisons by tensoriality. *)

(** 由张量函子性，竖直复合保持两项比较。 *)

Lemma lax_monoidal_hom_comp (L K J : LaxMonoidalFct MC MD)
    (β : K ⇒ J) (α : L ⇒ K)
    (Hβ : is_lax_monoidal_hom K J β) (Hα : is_lax_monoidal_hom L K α)
  : is_lax_monoidal_hom L J (β ∘Nv α).
Proof.
  destruct Hα as [Hαu Hαt], Hβ as [Hβu Hβt]. split.
  - change ((β (TensorUnit MC) ∘ α (TensorUnit MC)) ∘ φ₀[L] ≈ φ₀[J]).
    rewrite comp_assoc, Hαu. exact Hβu.
  - intros X Y.
    change ((β (@tensor C MC X Y) ∘ α (@tensor C MC X Y)) ∘
      φ₂[L; X; Y] ≈ φ₂[J; X; Y] ∘
        @tensor_map D MD _ _ _ _ (β X ∘ α X) (β Y ∘ α Y)).
    rewrite comp_assoc, Hαt, <- comp_assoc, Hβt, comp_assoc.
    apply comp_proper; [reflexivity |]. symmetry.
    exact (@tensor_map_comp D MD _ _ _ _ _ _ (β X) (α X) (β Y) (α Y)).
Defined.

(** A chosen natural inverse preserves comparisons by cancellation.
    Invertibility is used only here, not in the morphism definition. *)

(** 指定自然逆通过消去保持比较；可逆性只用于本引理，不用于态射定义。 *)

Lemma lax_monoidal_hom_inverse (L K : LaxMonoidalFct MC MD) (α : L ⇒ K)
    (Hα : is_lax_monoidal_hom L K α) (I : α ⦂ L ≅N K)
  : is_lax_monoidal_hom K L (α ^-1N I).
Proof.
  destruct Hα as [Hu Ht]. split.
  - apply (iso_cancel_l (α (TensorUnit MC); I (TensorUnit MC))).
    change (α (TensorUnit MC) ∘ ((I (TensorUnit MC)).1 ∘ φ₀[K]) ≈
      α (TensorUnit MC) ∘ φ₀[L]).
    rewrite <- comp_assoc, (snd (I (TensorUnit MC)).2), comp_id_l, Hu.
    reflexivity.
  - intros X Y.
    apply (iso_cancel_l (α (@tensor C MC X Y); I (@tensor C MC X Y))).
    change (α (@tensor C MC X Y) ∘
      ((I (@tensor C MC X Y)).1 ∘ φ₂[K; X; Y]) ≈
      α (@tensor C MC X Y) ∘ (φ₂[L; X; Y] ∘
        @tensor_map D MD _ _ _ _ (I X).1 (I Y).1)).
    rewrite <- !comp_assoc, (snd (I (@tensor C MC X Y)).2), comp_id_l,
      Ht, comp_assoc.
    rewrite <- (@tensor_map_comp D MD _ _ _ _ _ _
      (α X) (I X).1 (α Y) (I Y).1).
    rewrite (snd (I X).2), (snd (I Y).2),
      (@tensor_map_id D MD (K X) (K Y)), comp_id_r.
    reflexivity.
Defined.

End Preservation.

(** ** The Category at Fixed Source and Target

    Retain the same monoidal structures. Morphisms store a natural
    transformation and its preservation witnesses; equality compares only
    the transformation. The forgetful functor keeps that exact data. *)

(** ** 固定来源及目标的范畴

    保持相同幺半结构。态射保存自然变换及保持性见证，相等只比较自然变换。
    忘却函子保留该项原数据。 *)

Section Categories.
Context {C D : Cat} (MC : MonoidalCat C) (MD : MonoidalCat D).

(** The subset hom-set retains Type-valued law witnesses. *)

(** 子集 Hom 广集保留 Type 值定律见证。 *)

Definition LaxMonoidalHomS (L K : LaxMonoidalFct MC MD)
  : SetC
  := SubsetS (@HomSet (FctCat C D) L K) (is_lax_monoidal_hom L K).

(** Lift identity without changing its underlying transformation. *)

(** 提升恒等，不改变其底层变换。 *)

Definition lax_monoidal_id (L : LaxMonoidalFct MC MD)
  : LaxMonoidalHomS L L
  := (idN; lax_monoidal_hom_id L).

(** Lift vertical composition, keeping both original witnesses. *)

(** 提升竖直复合，保留两个原始见证。 *)

Definition lax_monoidal_comp {L K J : LaxMonoidalFct MC MD}
    (β : LaxMonoidalHomS K J) (α : LaxMonoidalHomS L K)
  : LaxMonoidalHomS L J
  := (β.1 ∘Nv α.1; lax_monoidal_hom_comp L K J β.1 α.1 β.2 α.2).

(** Lax monoidal functors and monoidal natural transformations form a
    category, without equality of structures or preservation proofs. *)

(** Lax 幺半函子与幺半自然变换组成范畴，无需结构或保持性证明相等。 *)

Program Definition LaxMonoidalFctCat
  : Cat
  :=
  {|Ob := LaxMonoidalFct MC MD
  ; HomSet := LaxMonoidalHomS
  ; id := lax_monoidal_id
  ; comp _ _ _ := lax_monoidal_comp
  |}.
Next Obligation.
  intros [β Hβ] [β' Hβ'] Eβ [α Hα] [α' Hα'] Eα O.
  exact (comp_proper (β O) (β' O) (Eβ O) (α O) (α' O) (Eα O)).
Defined.
Next Obligation. intros O. exact (comp_id_r (f.1 O)). Defined.
Next Obligation. intros O. exact (comp_id_l (f.1 O)). Defined.
Next Obligation.
  intros O. exact (comp_assoc (f.1 O) (g.1 O) (h.1 O)).
Defined.

(** Forget comparisons and their preservation proofs, retaining the
    supplied underlying functors and natural transformations. *)

(** 忘却比较及其保持性证明，保留所给底层函子和自然变换。 *)

Program Definition LaxMonoidalForgetF
  : Fct LaxMonoidalFctCat (FctCat C D)
  :=
  {|F0 := LaxMonoidalF
  ; F1 L K α := α.1
  |}.
Next Obligation. intros α β E. exact E. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Faithfulness uses the inherited equality, never proof irrelevance. *)

(** 忠实性使用继承的相等，不使用证明无关性。 *)

Lemma lax_monoidal_forget_faithful
  : is_faithful LaxMonoidalForgetF.
Proof. intros L K α β E. exact E. Defined.

End Categories.
