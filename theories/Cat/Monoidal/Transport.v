From Cats Require Import
  Cat.Monoidal.Natural.
From Cats Require Export
  Cat.Monoidal.Functor
  Cat.Monoidal.Monoid.

Local Open Scope monoidal_scope.

(** * Lax Monoidal Transport of Monoids

    A lax monoidal functor preserves monoid objects. This uses naturality
    and the three lax coherence diagrams only: no strength, symmetry,
    closedness, cartesian products or coends are needed. Homomorphisms
    map by the same underlying functor, with equality inherited from the
    target category rather than equality of preservation witnesses.
    The carrier coercion supports [L A] and [Hom A B]. Tensorator pairs
    retain explicit carrier projections for endpoint inference. *)

(** * 幺半群的 Lax Monoidal 传输

    Lax monoidal 函子保持幺半群对象，只使用自然性及三条 lax 相干律，不需要
    强度、对称性、闭性、笛卡尔积或余端。同态由同一个底层函子映射，相等继承
    自目标范畴，而不比较保持性见证。载体强制转换支持 [L A] 和 [Hom A B]；
    tensorator 的成对输入保留显式载体投影，以便推断端点。 *)

Section LaxMonoidTransport.
Context {C D : Cat}
    {MC : MonoidalCat C} {MD : MonoidalCat D}
    (L : LaxMonoidalFct MC MD).
Local Existing Instance MD.

(** The transported unit first inserts the lax unit comparison. *)

(** 传输后的单位先插入 lax 单位比较。 *)

Definition lax_monoid_unit (A : MonoidObj MC)
  : Hom (I⊗[MD]) (L A)
  := fmap L e[A] ∘ φ₀[L].

(** The transported multiplication combines images before mapping the
    original multiplication. *)

(** 传输后的乘法先组合像，再映射原乘法。 *)

Definition lax_monoid_mul (A : MonoidObj MC)
  : Hom (L A ⊗ L A) (L A)
  := fmap L m[A] ∘ φ₂[L; MonoidCarrier A; MonoidCarrier A].

(** Lax coherence and the source monoid laws give a target monoid. The
    carrier and both operations remain transparent computational data. *)

(** Lax 相干性及来源幺半群定律给出目标幺半群；载体和两个运算均保留透明的
    计算数据。 *)

Program Definition LaxMonoidObj (A : MonoidObj MC)
  : MonoidObj MD
  :=
  {|MonoidCarrier := L A
  ; monoid_object_unit := lax_monoid_unit A
  ; monoid_object_mul := lax_monoid_mul A
  |}.
Next Obligation.
  unfold lax_monoid_mul, lax_monoid_unit.
  transitivity (fmap L m[A] ∘ φ₂[L; MonoidCarrier A; MonoidCarrier A] ∘
    ((fmap L e[A] ⊗m fmap L id) ∘ (φ₀[L] ⊗m id))).
  - rewrite <- tensor_map_comp, functor_id, comp_id_l. reflexivity.
  - rewrite comp_assoc,
      <- (comp_assoc φ₂[L; MonoidCarrier A; MonoidCarrier A]),
      (lax_tensor_natural L e[A] id), <- !comp_assoc, <- functor_comp.
    rewrite (monoid_object_unit_l A). apply lax_unit_l.
Defined.
Next Obligation.
  unfold lax_monoid_mul, lax_monoid_unit.
  transitivity (fmap L m[A] ∘ φ₂[L; MonoidCarrier A; MonoidCarrier A] ∘
    ((fmap L id ⊗m fmap L e[A]) ∘ (id ⊗m φ₀[L]))).
  - rewrite <- tensor_map_comp, functor_id, comp_id_l. reflexivity.
  - rewrite comp_assoc,
      <- (comp_assoc φ₂[L; MonoidCarrier A; MonoidCarrier A]),
      (lax_tensor_natural L id e[A]), <- !comp_assoc, <- functor_comp.
    rewrite (monoid_object_unit_r A). apply lax_unit_r.
Defined.
Next Obligation.
  unfold lax_monoid_mul.
  transitivity (fmap L m[A] ∘ φ₂[L; MonoidCarrier A; MonoidCarrier A] ∘
    ((fmap L m[A] ⊗m fmap L id) ∘
      (φ₂[L; MonoidCarrier A; MonoidCarrier A] ⊗m id))).
  - rewrite <- tensor_map_comp, functor_id, comp_id_l. reflexivity.
  - rewrite comp_assoc,
      <- (comp_assoc φ₂[L; MonoidCarrier A; MonoidCarrier A]),
      (lax_tensor_natural L m[A] id), <- !comp_assoc, <- functor_comp.
    rewrite (monoid_object_assoc A), !(@functor_comp _ _ L), !comp_assoc.
    rewrite <- (comp_assoc (fmap L (@tensor_assoc C MC A A A))).
    rewrite (lax_assoc L A A A).
    rewrite !comp_assoc.
    rewrite <- (comp_assoc
      (fmap L (@tensor_map C MC _ _ _ _ id m[A]))).
    rewrite <- (lax_tensor_natural L id m[A]).
    rewrite !comp_assoc.
    rewrite <- (comp_assoc
      (@tensor_map D MD _ _ _ _
        (fmap L (@id A)) (fmap L m[A]))).
    rewrite <- tensor_map_comp, functor_id, comp_id_l.
    reflexivity.
Defined.

(** Mapping an operation-preserving arrow preserves both transported
    operations. The proof is reusable independently of the bundled functor. *)

(** 保持运算的箭头在映射后保持两个传输后的运算；证明可独立于打包函子复用。 *)

Lemma lax_monoid_hom {A B : MonoidObj MC}
    (f : Hom A B)
    (Hf : is_monoid_hom A B f)
  : is_monoid_hom (LaxMonoidObj A) (LaxMonoidObj B) (fmap L f).
Proof.
  destruct Hf as [He Hm]. split; cbn.
  - unfold lax_monoid_unit. rewrite <- comp_assoc, <- functor_comp, He.
    reflexivity.
  - unfold lax_monoid_mul.
    rewrite <- comp_assoc, <- functor_comp, Hm, functor_comp, comp_assoc.
    rewrite <- (lax_tensor_natural L f f), <- comp_assoc. reflexivity.
Qed.

(** The induced functor on monoid objects maps homomorphisms by [fmap L].
    Its respectfulness and category laws are inherited from [L]. *)

(** 幺半群对象上的诱导函子用 [fmap L] 映射同态；其保相等性及范畴律继承自 [L]。 *)

Program Definition LaxMonoidF
  : Fct (MonoidCat MC) (MonoidCat MD)
  :=
  {|F0 := LaxMonoidObj
  ; F1 A B f := (fmap L f.1; lax_monoid_hom f.1 f.2)
  |}.
Next Obligation.
  intros [f Hf] [g Hg] E.
  exact (@functor_fmap_proper C D L _ _ f g E).
Defined.
Next Obligation. apply functor_id. Defined.
Next Obligation. apply functor_comp. Defined.

End LaxMonoidTransport.

(** ** Naturality with Respect to Monoidal Transformations

    Fix source and target monoidal structures. A monoidal transformation
    between lax functors gives a homomorphism between every pair of
    transported monoids. Reuse their existing functors and subset hom-sets;
    preservation witnesses remain distinct from the underlying arrows. *)

(** ** 关于幺半变换的自然性

    固定来源和目标幺半结构。Lax 函子之间的幺半变换在每个传输后的幺半群对
    之间给出同态。复用其已有函子及子集 Hom 广集，将保持性见证与底层箭头
    区分开来。 *)

Section LaxMonoidTransformations.
Context {C D : Cat} {MC : MonoidalCat C} {MD : MonoidalCat D}.

(** Monoidal preservation and naturality give both monoid homomorphism
    diagrams, without unfolding or reproving transported monoid laws. *)

(** 幺半保持性与自然性给出两个幺半群同态图，无需展开或重证传输后的定律。 *)

Lemma lax_monoidal_monoid_hom (L K : LaxMonoidalFct MC MD) (α : L ⇒ K)
    (Hα : is_lax_monoidal_hom L K α) (A : MonoidObj MC)
  : is_monoid_hom (LaxMonoidObj L A) (LaxMonoidObj K A) (α A).
Proof.
  destruct Hα as [Hu Ht]. split; cbn.
  - unfold lax_monoid_unit.
    rewrite <- comp_assoc, (nt_naturality α e[A]), comp_assoc, Hu.
    reflexivity.
  - unfold lax_monoid_mul.
    rewrite <- comp_assoc, (nt_naturality α m[A]), comp_assoc,
      (Ht (MonoidCarrier A) (MonoidCarrier A)).
    rewrite <- comp_assoc. reflexivity.
Defined.

(** The same components are natural in monoid homomorphisms. *)

(** 相同分量关于幺半群同态自然。 *)

Program Definition LaxMonoidN (L K : LaxMonoidalFct MC MD) (α : L ⇒ K)
    (Hα : is_lax_monoidal_hom L K α)
  : LaxMonoidF L ⇒ LaxMonoidF K
  :=
  {|nt A := (α A; lax_monoidal_monoid_hom L K α Hα A)
  |}.
Next Obligation. exact (nt_naturality α f.1). Defined.

(** Equality compares the same components regardless of preservation
    witnesses. This is natural equality in the target monoid category. *)

(** 无论保持性见证如何，相等比较相同分量，即目标幺半群范畴中的自然相等。 *)

Lemma lax_monoid_nt_proper (L K : LaxMonoidalFct MC MD) (α β : L ⇒ K)
    (Hα : is_lax_monoidal_hom L K α) (Hβ : is_lax_monoidal_hom L K β)
    (E : α ≈N β)
  : LaxMonoidN L K α Hα ≈N LaxMonoidN L K β Hβ.
Proof. intros A. exact (E A). Defined.

(** Transport respects the identity monoidal transformation. *)

(** 传输保持恒等幺半变换。 *)

Lemma lax_monoid_nt_id (L : LaxMonoidalFct MC MD)
  : LaxMonoidN L L idN (lax_monoidal_hom_id L) ≈N idN.
Proof.
  intros A. change (@Cat.Core.id D (L A) ≈ @Cat.Core.id D (L A)). reflexivity.
Defined.

(** Transport respects vertical composition in designated equality. *)

(** 传输按指定相等保持竖直复合。 *)

Lemma lax_monoid_nt_comp (L K J : LaxMonoidalFct MC MD)
    (β : K ⇒ J) (α : L ⇒ K)
    (Hβ : is_lax_monoidal_hom K J β) (Hα : is_lax_monoidal_hom L K α)
  : LaxMonoidN L J (β ∘Nv α) (lax_monoidal_hom_comp L K J β α Hβ Hα) ≈N
      (LaxMonoidN K J β Hβ ∘Nv LaxMonoidN L K α Hα).
Proof.
  intros A. change (β A ∘ α A ≈ β A ∘ α A). reflexivity.
Defined.

(** The existing lax monoid functors now vary functorially with the lax
    functor, providing a general client of monoidal natural transformations. *)

(** 已有 lax 幺半群函子现在关于 lax 函子也具有函子性，成为幺半自然变换的
    一般客户端。 *)

Program Definition LaxMonoidTransportF
  : Fct (LaxMonoidalFctCat MC MD) (FctCat (MonoidCat MC) (MonoidCat MD))
  :=
  {|F0 := LaxMonoidF
  ; F1 L K α := LaxMonoidN L K α.1 α.2
  |}.
Next Obligation.
  intros [α Hα] [β Hβ] E. exact (lax_monoid_nt_proper X Y α β Hα Hβ E).
Defined.
Next Obligation. exact (lax_monoid_nt_id X). Defined.
Next Obligation.
  symmetry. exact (lax_monoid_nt_comp X Y Z f.1 g.1 f.2 g.2).
Defined.

End LaxMonoidTransformations.
