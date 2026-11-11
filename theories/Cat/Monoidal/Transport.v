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
    (L : LaxMonoidalFunctor MC MD).
Local Existing Instance MD.

(** The transported unit first inserts the lax unit comparison. *)

(** 传输后的单位先插入 lax 单位比较。 *)

Definition lax_monoid_unit (A : MonoidObject MC)
  : Hom (I⊗[MD]) (L A)
  := fmap L e[A] ∘ φ₀[L].

(** The transported multiplication combines images before mapping the
    original multiplication. *)

(** 传输后的乘法先组合像，再映射原乘法。 *)

Definition lax_monoid_mul (A : MonoidObject MC)
  : Hom (L A ⊗ L A) (L A)
  := fmap L m[A] ∘ φ₂[L; MonoidCarrier A; MonoidCarrier A].

(** Lax coherence and the source monoid laws give a target monoid. The
    carrier and both operations remain transparent computational data. *)

(** Lax 相干性及来源幺半群定律给出目标幺半群；载体和两个运算均保留透明的
    计算数据。 *)

Program Definition LaxMonoidObject (A : MonoidObject MC)
  : MonoidObject MD
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

Lemma lax_monoid_hom {A B : MonoidObject MC}
    (f : Hom A B)
    (Hf : is_monoid_hom A B f)
  : is_monoid_hom (LaxMonoidObject A) (LaxMonoidObject B) (fmap L f).
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
  : Functor (MonoidCat MC) (MonoidCat MD)
  :=
  {|F0 := LaxMonoidObject
  ; F1 A B f := (fmap L f.1; lax_monoid_hom f.1 f.2)
  |}.
Next Obligation.
  intros [f Hf] [g Hg] E.
  exact (@functor_fmap_proper C D L _ _ f g E).
Defined.
Next Obligation. apply functor_id. Defined.
Next Obligation. apply functor_comp. Defined.

End LaxMonoidTransport.
