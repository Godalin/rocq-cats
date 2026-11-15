From Cats Require Import
  Cat.Gluing.Cartesian
  Cat.Diagram.Core
  Cat.Functor.Cartesian
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product.
From Stdlib Require Import Bool.Bool.

(** * Gluing Interfaces and Computational Mediators

    Check opposite strict orders for native hom and equality levels.
    Concrete setoid tests retain nontrivial equivalence witnesses and
    compute the two component mediators without inspecting square proofs. *)

(** * 粘合接口与可计算中介

    检查原有 Hom 与相等层级的相反严格次序。具体广集测试保留非平凡等价
    见证，并在不检查方形证明的前提下计算两端中介。 *)

(** ** Equality above the Glued Hom Carrier

    Fix [ed < hd < hc < ec < o < l]. The result keeps hom bound [hc]
    and equality bound [ec]; no native endpoint bound is identified. *)

(** ** 相等界高于粘合 Hom 载体

    固定 [ed < hd < hc < ec < o < l]。结果保持 Hom 界 [hc] 与相等界
    [ec]，不合并两端原有的界。 *)

Section LargeEquality.
Universes ed hd hc ec o l.
Constraint ed < hd, hd < hc, hc < ec, ec < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).

(** The comma wrapper preserves the strict output separation. *)

(** 逗号包装保持输出界的严格分离。 *)

Definition gluing_large_equality
  : Cat@{o hc ec l l}
  := Gluing F.

(** The weak terminal theorem needs no chosen target terminal. *)

(** 弱终对象定理不需要选定目标终对象。 *)

Definition gluing_large_equality_terminal (T : @Ob C) (HT : is_terminal T)
  : @is_terminal (Gluing F) (GluingTerminal F T)
  := gluing_terminal F T HT.

(** Product witnesses also retain the larger equality bound. *)

(** 积见证也保持较大的相等界。 *)

Definition gluing_large_equality_products
    `{PC : !HasProduct C} `{PD : !HasProduct D}
    (preserves : ∀ X Y : @Ob C,
      is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2))
  : HasProduct (Gluing F)
  := Gluing_HasProduct F preserves.

End LargeEquality.

(** ** Equality below the Glued Hom Carrier

    Reverse the native orders: [ec < hd < ed < hc < o < l]. The square
    witness fits [hc], while the resulting equality can stay at [ed]. *)

(** ** 相等界低于粘合 Hom 载体

    反转原有次序：[ec < hd < ed < hc < o < l]。方形见证位于 [hc]，而
    所得相等可以保持在 [ed]。 *)

Section SmallEquality.
Universes ec hd ed hc o l.
Constraint ec < hd, hd < ed, ed < hc, hc < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).

(** The same construction accepts the reverse strict separation. *)

(** 同一构造接受反向的严格分离。 *)

Definition gluing_small_equality
  : Cat@{o hc ed l l}
  := Gluing F.

(** The product construction does not equate these native levels. *)

(** 积构造不合并这些原有层级。 *)

Definition gluing_small_equality_products
    `{PC : !HasProduct C} `{PD : !HasProduct D}
    (preserves : ∀ X Y : @Ob C,
      is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2))
  : HasProduct (Gluing F)
  := Gluing_HasProduct F preserves.

End SmallEquality.

(** ** A Setoid with Observable Equality Witnesses

    Only the natural-number component is compared. A Boolean token is
    retained in each equality witness, and the carrier's Boolean tag is
    ignored. Thus neither equality nor witness data is native identity. *)

(** ** 具有可观测相等见证的广集

    只比较自然数分量。每个相等见证保留一个布尔标记，载体中的布尔标签则被
    忽略。因此相等及见证数据均不能被当作原生恒等。 *)

Program Definition TaggedGluingS
  : SetC
  :=
  {|carrier := (nat * bool)%type
  ; carrier_equiv x y := ((fst x = fst y) * bool)%type
  |}.
Next Obligation.
  split.
  - intros x. exact (eq_refl, false).
  - intros x y [h token]. exact (eq_sym h, token).
  - intros x y z [h token] [k other]. exact (eq_trans h k, token).
Defined.

(** A respectful map changes the ignored tag. *)

(** 保相等映射改变被忽略的标签。 *)

Program Definition gluing_toggle
  : TaggedGluingS →r TaggedGluingS
  :=
  {|func x := (fst x, negb (snd x))
  |}.
Next Obligation. intros x y [h token]. exact (h, token). Defined.

(** ** Explicit Chosen Structures in the Concrete Model

    Enable terminal and product choices only in this test section. The
    glued product reuses the identity functor's preserved product cones. *)

(** ** 具体模型中显式选定的结构

    只在此测试节启用终对象与积选择。粘合积复用恒等函子保持的积锥。 *)

Section SetoidGluing.
Local Instance set_terminal
  : HasTerminal SetCat
  := SetCat_HasTerminal.
Local Instance set_product
  : HasProduct SetCat
  := SetCat_HasProduct.

(** Select the constructed gluing products locally. *)

(** 局部选择已构造的粘合积。 *)

Local Instance identity_gluing_products
  : HasProduct (Gluing (@IdF SetCat))
  := Gluing_HasProduct IdF (λ X Y, product_universal).

(** A glued object with the identity structure arrow. *)

(** 结构箭头为恒等的粘合对象。 *)

Program Definition TaggedGluingObj
  : @Ob (Gluing (@IdF SetCat))
  :=
  {|comma_left_ob := TaggedGluingS
  ; comma_right_ob := TaggedGluingS
  ; comma_arrow := id
  |}.

(** Both components change the ignored tag; the square commutes by
    designated equality, with an observable token in its witness. *)

(** 两端都改变被忽略的标签；方形按指定相等交换，见证中有可观测标记。 *)

Program Definition tagged_gluing_toggle
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedGluingObj
  :=
  {|comma_left := gluing_toggle
  ; comma_right := gluing_toggle
  |}.
Next Obligation. intros [n b]. exact (eq_refl, true). Defined.

(** Native differences in tags do not change the glued arrow's equality. *)

(** 标签的原生差异不改变粘合箭头的指定相等。 *)

Definition tagged_gluing_toggle_equal
  : tagged_gluing_toggle ≈ id.
Proof. split; intros [n b]; exact (eq_refl, true). Defined.

(** The universal mediator computes both diagonal functions. *)

(** 泛中介计算两个对角函数。 *)

Definition tagged_gluing_diagonal
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj
      ((TaggedGluingObj × TaggedGluingObj)%ob)
  := ⟨id, id⟩.

(** Computing the left component does not evaluate the square witness. *)

(** 计算左分量不对方形见证求值。 *)

Example tagged_gluing_left_computes
  : comma_left tagged_gluing_diagonal (3, false) =
      ((3, false), (3, false)).
Proof. reflexivity. Defined.

(** The right component is the same transparent base mediator. *)

(** 右分量是同样透明的基中介。 *)

Example tagged_gluing_right_computes
  : comma_right tagged_gluing_diagonal (4, true) =
      ((4, true), (4, true)).
Proof. reflexivity. Defined.

(** Pairing respects nontrivial equality on both component maps. *)

(** 配对保持两个分量映射上的非平凡相等。 *)

Example tagged_gluing_pair_respects
  : ⟨tagged_gluing_toggle, tagged_gluing_toggle⟩ ≈ tagged_gluing_diagonal.
Proof.
  apply product_pair_proper; exact tagged_gluing_toggle_equal.
Defined.

(** The right projection's finite-product preservation is explicitly enabled. *)

(** 显式启用右投影的有限积保持性。 *)

Definition identity_gluing_right_cartesian
  : IsCartF (GluingRightF (@IdF SetCat)) (Gluing_HasTerminal IdF)
      identity_gluing_products
  := GluingRight_IsCartF IdF (λ X Y, product_universal).

(** ** Terminality without Preservation by the Gluing Functor

    A constant functor at the tagged setoid does not preserve terminality.
    Its gluing still has the constructed terminal. This concrete boundary
    prevents accidentally strengthening the terminal interface later. *)

(** ** 粘合函子不保持终性时的终对象

    取值于带标签广集的常值函子不保持终性，但其粘合仍有已构造的终对象。
    此具体边界防止以后无意加强终对象接口的假设。 *)

(** Constant points witness that the tagged setoid is not terminal. *)

(** 常值点见证带标签广集不是终对象。 *)

Program Definition tagged_gluing_point (n : nat)
  : UnitS →r TaggedGluingS
  :=
  {|func _ := (n, false)
  |}.
Next Obligation. intros x y h. exact (eq_refl, true). Defined.

(** Its points zero and one are inequivalent in the specified equality. *)

(** 按指定相等，零点与一点不等价。 *)

Definition tagged_gluing_not_terminal (H : is_terminal TaggedGluingS)
  : Empty_set.
Proof.
  destruct (H UnitS) as [h unique].
  assert (same : tagged_gluing_point 0 ≈ tagged_gluing_point 1).
  { transitivity h; [apply unique; exact I |
      symmetry; apply unique; exact I]. }
  destruct (same tt) as [impossible token]. discriminate impossible.
Defined.

(** The gluing terminal requires no image-terminal hypothesis. *)

(** 粘合终对象不要求终对象的像为终这一假设。 *)

Definition constant_gluing_terminal
  : @is_terminal (Gluing (ConstF SetCat TaggedGluingS))
      (GluingTerminal (ConstF SetCat TaggedGluingS) UnitS)
  := gluing_terminal _ _ terminal_universal.

(** Its left projection is demonstrably not terminal. *)

(** 其左投影可证不是终对象。 *)

Definition constant_gluing_left_not_terminal
  : is_terminal (GluingLeftF (ConstF SetCat TaggedGluingS)
      (GluingTerminal (ConstF SetCat TaggedGluingS) UnitS)) → Empty_set
  := tagged_gluing_not_terminal.

(** The left terminal mediator still computes to the unchanged value. *)

(** 左侧终中介仍计算为不变的值。 *)

Example constant_gluing_terminal_computes
  : comma_left (@term (Gluing (ConstF SetCat TaggedGluingS))
      (Gluing_HasTerminal
      (ConstF SetCat TaggedGluingS))
      (GluingTerminal (ConstF SetCat TaggedGluingS) UnitS)) (9, true) =
      (9, true).
Proof. reflexivity. Defined.

End SetoidGluing.
