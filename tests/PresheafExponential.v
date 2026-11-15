From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.FiniteProducts
  Cat.Natural
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC
  Cat.Induced
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Kripke
  Instance.Set.PresheafExponential.
From CatsTests Require Import
  Gluing.

(** * Presheaf Exponential Sizes and Original Function Values

    Check both strict world Hom/equality orders and both orders between
    the world-law and common semantic bounds. Concrete probes use all
    respectful endomorphisms as world arrows, with observable equality data. *)

(** * 预层指数的大小与原函数值

    检查世界 Hom/相等的两种严格次序，以及世界定律界与共同语义界的两种次序。
    具体探针以所有保相等自同态作为世界箭头，并保留可观察的相等数据。 *)

(** ** Large World Laws

    Keep [e < h < o < u < l]; stored world laws need not fit the value bound. *)

(** ** 较大的世界定律

    保持 [e < h < o < u < l]；所存世界定律不需要容纳于值界。 *)

Section LargeLaws.
Universes o h e l u.
Constraint e < h.
Constraint h < o.
Constraint o < u.
Constraint u < l.
Context (C : Cat@{o h e l l}).

(** Explicitly chosen exponentials keep these native world levels. *)

(** 显式选定的指数保持这些原生世界层级。 *)

Definition presheaf_large_law_exponentials
  : @HasExponential (FctCat (C^op) SetCat@{u u _ _ _ _ _})
      (@FctCat_HasProduct _ _ SetCat_HasProduct)
  := Psh_HasExponential C.

(** The complete CCC has the same independent world and value bounds. *)

(** 完整 CCC 保持同样独立的世界与值界限。 *)

Definition presheaf_large_law_ccc
  : CCC (FctCat (C^op) SetCat@{u u _ _ _ _ _})
  := Psh_CCC C.

End LargeLaws.

(** ** Small World Laws

    Reverse the Hom/equality order with [h < e < o < l < u]. *)

(** ** 较小的世界定律

    用 [h < e < o < l < u] 反转 Hom/相等次序。 *)

Section SmallLaws.
Universes o h e l u.
Constraint h < e.
Constraint e < o.
Constraint o < l.
Constraint l < u.
Context (C : Cat@{o h e l l}).

(** The opposite strict orders also instantiate the chosen CCC. *)

(** 相反的严格次序也能实例化选定 CCC。 *)

Definition presheaf_small_law_ccc
  : CCC (FctCat (C^op) SetCat@{u u _ _ _ _ _})
  := Psh_CCC C.

End SmallLaws.

(** ** Future-World Computation

    Oppose an induced category with two labels and all respectful maps
    between the same tagged setoid. Its presheaf acts by the original maps,
    so a future arrow can change an ignored representation tag. *)

(** ** 未来世界的计算

    将具有两个标签、同一带标签广集间所有保相等映射的诱导范畴取反。其预层
    使用原映射作用，因此未来箭头可以改变被忽略的表示标签。 *)

Section TaggedWorlds.

(** Use the existing induced category and opposite construction. *)

(** 使用已有诱导范畴和反范畴构造。 *)

Definition TaggedWorlds
  : Cat
  := (InducedCat bool (λ _, TaggedGluingS))^op.

(** The original inclusion diagram is read on the double opposite. *)

(** 在双重反范畴上读原包含图式。 *)

Definition TaggedPsh
  : Fct (TaggedWorlds^op) SetCat
  := @CompF (TaggedWorlds^op) (InducedCat bool (λ _, TaggedGluingS))
      SetCat (InducedInclusionF bool (λ _, TaggedGluingS))
      (@FromDoubleOpF (InducedCat bool (λ _, TaggedGluingS))).

(** A future arrow changes the observable natural-number coordinate. *)

(** 一个未来箭头改变可观察的自然数坐标。 *)

Program Definition tagged_advance_resp
  : TaggedGluingS →r TaggedGluingS
  :=
  {|func x := (S (fst x), snd x)
  |}.
Next Obligation.
  intros [n b] [m c] [Hnm token]. exact (f_equal S Hnm, token).
Defined.

Local Instance tagged_pointwise_products
  : HasProduct (FctCat (TaggedWorlds^op) SetCat)
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Local Instance tagged_presheaf_exponentials
  : HasExponential tagged_pointwise_products
  := Psh_HasExponential TaggedWorlds.

(** The selected exponential keeps the existing coherent function presheaf. *)

(** 选定指数保持已有相容函数预层。 *)

Definition TaggedExpPsh
  : Fct (TaggedWorlds^op) SetCat
  := @exp (FctCat (TaggedWorlds^op) SetCat) tagged_pointwise_products
      tagged_presheaf_exponentials TaggedPsh TaggedPsh.

(** Transpose the context projection using the new selected structure. *)

(** 使用新选定结构转置上下文投影。 *)

Definition TaggedCurryN
  : TaggedPsh ⇒ TaggedExpPsh
  := @Cats.Cat.Exponential.Core.curry
      (FctCat (TaggedWorlds^op) SetCat) tagged_pointwise_products
      tagged_presheaf_exponentials _ _ _
      (PointwiseFstN _ _ TaggedPsh TaggedPsh).

(** A future world arrow actually transports the stored context value. *)

(** 未来世界箭头实际运输已保存的上下文值。 *)

Example presheaf_curry_future_computes
  : TaggedCurryN false (3%nat, false) true tagged_advance_resp (7%nat, true)
      = (4%nat, false).
Proof. reflexivity. Qed.

(** Current-world evaluation keeps the untransported representation. *)

(** 当前世界的求值保持未运输的表示。 *)

Example presheaf_curry_current_computes
  : TaggedCurryN false (3%nat, false) false id (7%nat, true)
      = (3%nat, false).
Proof. reflexivity. Qed.

(** Restriction followed by current-world evaluation computes as well. *)

(** 限制后再在当前世界求值也能计算。 *)

Example presheaf_restricted_eval_computes
  : kripke_eval TaggedPsh TaggedPsh
      (fmap TaggedExpPsh (X := false) (Y := true)
        tagged_advance_resp (TaggedCurryN false (4%nat, false))) (8%nat, true)
      = (5%nat, false).
Proof. reflexivity. Qed.

(** The selected evaluation arrow computes on a natural pair. *)

(** 选定求值箭头在自然配对上计算。 *)

Example presheaf_selected_eval_computes
  : (@Cats.Cat.Exponential.Core.eval
      (FctCat (TaggedWorlds^op) SetCat) tagged_pointwise_products
      tagged_presheaf_exponentials TaggedPsh TaggedPsh)
        false (TaggedCurryN false (5%nat, true), (9%nat, false))
      = (5%nat, true).
Proof. reflexivity. Qed.

(** The native transpose accepts context equality with different tags. *)

(** 原生转置接受标签不同的上下文相等。 *)

Example presheaf_curry_context_equal
  : TaggedCurryN false (3%nat, false) ≈S
      TaggedCurryN false (3%nat, true).
Proof.
  exact (@func_proper _ _ (TaggedCurryN false)
    (3%nat, false) (3%nat, true) (eq_refl, true)).
Defined.

(** Its pointwise equality still carries Boolean evidence. *)

(** 其逐点相等仍携带布尔证据。 *)

Definition presheaf_curry_equality_token
  : bool
  := snd (presheaf_curry_context_equal true gluing_toggle (7%nat, false)).

(** Reuse the old native function values: only the model packaging is new. *)

(** 复用旧原生函数值；新增的只是模型打包。 *)

Example presheaf_curry_original_application
    (X Y : bool) (z a : TaggedGluingS)
    (f : (@Hom TaggedWorlds) Y X)
  : TaggedCurryN X z Y f a ≈S
      kripke_curry_at TaggedPsh TaggedPsh TaggedPsh
        (PointwiseFstN _ _ TaggedPsh TaggedPsh) X z Y f a.
Proof. reflexivity. Qed.

End TaggedWorlds.
