From Cats Require Import
  Cat.Gluing.ChangeTerminal
  Cat.Functor.Cartesian
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Initial
  Instance.Set.Product.
From CatsTests Require Import
  Gluing
  GluingChangeProduct
  ProductPreservation.

(** * Local Terminal Boundaries and Finite Products

    Strict profiles check local terminal preservation separately from
    chosen finite products. Tagged boundaries retain transparent inverses.
    Concrete empty models separate gluing preservation from preservation
    by the target change, and binary products from terminal objects. *)

(** * 局部终边界及有限积

    严格配置将局部终对象保持与选定有限积分开检查。标签边界保留透明逆；
    具体空模型区分粘合保持与目标变化的保持，以及二元积与终对象。 *)

(** ** Independent Native Bounds

    Fix four independent category boundaries and only one invertible
    boundary component. The weak terminal result requires no choices. *)

(** ** 独立原生边界

    固定四个独立范畴边界，只给出一个可逆边界分量。弱终对象结果不要求选择。 *)

Section IndependentTerminalChange.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2 o3 h3 e3 l3.
Constraint h0 < e0, e0 < o0, o0 < l0.
Constraint e1 < h1, h1 < o1, o1 < l1.
Constraint h2 < e2, e2 < o2, o2 < l2.
Constraint e3 < h3, h3 < o3, o3 < l3.
Constraint l0 < o1, l1 < o2, l2 < o3.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)) (T : C).
Context (HT : is_terminal (H T)) (Hα : is_iso (α T)).

(** The image terminal is witnessed using only these local hypotheses. *)

(** 只用这些局部假设给出像终对象见证。 *)

Definition independent_changed_terminal
  : @is_terminal (Gluing F')
      (GluingChangeF H K α (GluingTerminal F T))
  := gluing_change_terminal H K α T HT Hα.

Context {TC : HasTerminal C} {PC : HasProduct C} {PD : HasProduct D}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ A B : D,
    is_product (K A) (K B) (K ((A × B)%ob)) (fmap K π1) (fmap K π2)).
Context (image : ∀ A B : C,
    is_product (F' (H A)) (F' (H B)) (F' (H ((A × B)%ob)))
      (fmap F' (fmap H π1)) (fmap F' (fmap H π2))).
Context (HT1 : is_terminal (H (@Term C TC)))
    (Hα1 : is_iso (α (@Term C TC))).

(** Explicit preservation retains the named source gluing choices. *)

(** 显式保持性保留具名的来源粘合选择。 *)

Definition independent_changed_cartesian
  : IsCartF (GluingChangeF H K α) (@Gluing_HasTerminal C D F TC)
      (Gluing_HasProduct F source)
  := GluingChange_IsCartF H K α source base target image HT1 Hα1.

End IndependentTerminalChange.

(** ** Reversed Native Bounds

    Fix four independent category boundaries and only one invertible
    boundary component. The weak terminal result requires no choices. *)

(** ** 反向原生边界

    固定四个独立范畴边界，只给出一个可逆边界分量。弱终对象结果不要求选择。 *)

Section ReversedTerminalChange.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2 o3 h3 e3 l3.
Constraint e0 < h0, h0 < o0, o0 < l0.
Constraint h1 < e1, e1 < o1, o1 < l1.
Constraint e2 < h2, h2 < o2, o2 < l2.
Constraint h3 < e3, e3 < o3, o3 < l3.
Constraint l3 < o2, l2 < o1, l1 < o0.
Context {C : Cat@{o0 h0 e0 l0 l0}}.
Context {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}}.
Context {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)) (T : C).
Context (HT : is_terminal (H T)) (Hα : is_iso (α T)).

(** The image terminal is witnessed using only these local hypotheses. *)

(** 只用这些局部假设给出像终对象见证。 *)

Definition reversed_changed_terminal
  : @is_terminal (Gluing F')
      (GluingChangeF H K α (GluingTerminal F T))
  := gluing_change_terminal H K α T HT Hα.

Context {TC : HasTerminal C} {PC : HasProduct C} {PD : HasProduct D}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ A B : D,
    is_product (K A) (K B) (K ((A × B)%ob)) (fmap K π1) (fmap K π2)).
Context (image : ∀ A B : C,
    is_product (F' (H A)) (F' (H B)) (F' (H ((A × B)%ob)))
      (fmap F' (fmap H π1)) (fmap F' (fmap H π2))).
Context (HT1 : is_terminal (H (@Term C TC)))
    (Hα1 : is_iso (α (@Term C TC))).

(** Explicit preservation retains the named source gluing choices. *)

(** 显式保持性保留具名的来源粘合选择。 *)

Definition reversed_changed_cartesian
  : IsCartF (GluingChangeF H K α) (@Gluing_HasTerminal C D F TC)
      (Gluing_HasProduct F source)
  := GluingChange_IsCartF H K α source base target image HT1 Hα1.

End ReversedTerminalChange.

(** Importing the result does not automatically select terminal objects. *)

(** 导入结果不会自动选择终对象。 *)

Fail Definition automatic_changed_terminal
  : HasTerminal (Gluing (ConstF SetCat TaggedGluingS))
  := ltac:(typeclasses eauto).

(** ** A Tagged Local Inverse without Product Assumptions

    Both interpretations are constant at the tagged setoid. No products
    or terminal preservation by these interpretations are assumed. The
    boundary toggles the ignored tag and supplies its inverse locally. *)

(** ** 不带积假设的标签局部逆

    两个解释均常值取标签广集。不假设积或这些解释的终对象保持性；边界翻转
    被忽略的标签，并局部给出其逆。 *)

Section TaggedTerminal.

(** Constant interpretations make the tag-changing family natural. *)

(** 常值解释使改变标签的族成为自然变换。 *)

Program Definition TaggedTerminalBoundaryN
  : (@CompF SetCat SetCat SetCat (@IdF SetCat)
        (ConstF SetCat TaggedGluingS)) ⇒
      (@CompF SetCat SetCat SetCat (ConstF SetCat TaggedGluingS)
        (@IdF SetCat))
  :=
  {|nt X := gluing_toggle
  ; nt_naturality X Y f x := (eq_refl, true)
  |}.

(** Only the component at the supplied unit object is given an inverse. *)

(** 只为给定单位对象处的分量提供逆。 *)

Definition tagged_terminal_boundary_iso
  : is_iso (TaggedTerminalBoundaryN UnitS).
Proof.
  exists gluing_toggle. split; intros [n b]; exact (eq_refl, false).
Defined.

(** A probe with identity structural arrow lies in the target gluing. *)

(** 结构箭头为恒等的探测对象位于目标粘合中。 *)

Definition TaggedTerminalProbe
  : Gluing (ConstF SetCat TaggedGluingS)
  := GluingTerminal (ConstF SetCat TaggedGluingS) UnitS.

(** Transported terminality keeps the original universal arrow as data. *)

(** 运输后的终性将原泛箭头保留为数据。 *)

Definition tagged_changed_terminal
  : @is_terminal (Gluing (ConstF SetCat TaggedGluingS))
      (GluingChangeF IdF IdF TaggedTerminalBoundaryN TaggedTerminalProbe)
  := gluing_change_terminal IdF IdF TaggedTerminalBoundaryN UnitS
      (@terminal_universal SetCat SetCat_HasTerminal)
      tagged_terminal_boundary_iso.

(** The comparison and inverse are retained as a single isomorphism. *)

(** 比较及逆保留在同一个同构中。 *)

Definition TaggedTerminalComparison
  : GluingChangeF IdF IdF TaggedTerminalBoundaryN TaggedTerminalProbe ≅
      TaggedTerminalProbe
  := gluing_change_terminal_iso IdF IdF TaggedTerminalBoundaryN UnitS
      tagged_terminal_boundary_iso.

(** The stored image structure keeps its changed tag. *)

(** 所存像结构保留改变后的标签。 *)

Example tagged_terminal_structure_computes
  : comma_arrow (GluingChangeF IdF IdF TaggedTerminalBoundaryN
      TaggedTerminalProbe) (3, false) = (3, true).
Proof. reflexivity. Defined.

(** The forward comparison keeps exactly the boundary's map. *)

(** 正向比较恰保留边界映射。 *)

Example tagged_terminal_comparison_computes
  : comma_left TaggedTerminalComparison.1 (3, false) = (3, true).
Proof. reflexivity. Defined.

(** The saved inverse computes using the supplied inverse map. *)

(** 保存的逆使用给定逆映射计算。 *)

Example tagged_terminal_inverse_computes
  : comma_left TaggedTerminalComparison.2.1 (3, true) = (3, false).
Proof. reflexivity. Defined.

(** The base comparison remains an identity on the supplied base object. *)

(** 基比较仍为给定基对象上的恒等。 *)

Example tagged_terminal_base_computes
  : comma_right TaggedTerminalComparison.2.1 tt = tt.
Proof. reflexivity. Defined.

(** The transported terminal mediator uses the inverse comparison. *)

(** 运输后的终中介使用逆比较。 *)

Example tagged_terminal_mediator_computes
  : comma_left (tagged_changed_terminal TaggedTerminalProbe).1
      (4, false) = (4, true).
Proof. reflexivity. Defined.

(** Its independent base mediator still computes. *)

(** 其独立基中介仍可计算。 *)

Example tagged_terminal_mediator_base_computes
  : comma_right (tagged_changed_terminal TaggedTerminalProbe).1 tt = tt.
Proof. reflexivity. Defined.

(** The inverse's respectful action keeps the input Type-valued token. *)

(** 逆的保相等作用保留输入的 Type 值标记。 *)

Example tagged_terminal_inverse_token_computes
  : snd (@func_proper _ _ (comma_left TaggedTerminalComparison.2.1)
      (3, false) (3, true) (eq_refl, true)) = true.
Proof. reflexivity. Defined.

(** An alternative map keeps its tag; its square uses specified equality. *)

(** 另一条映射保留标签，其方形使用指定相等。 *)

Program Definition tagged_terminal_alternative
  : Hom TaggedTerminalProbe
      (GluingChangeF IdF IdF TaggedTerminalBoundaryN TaggedTerminalProbe)
  :=
  {|comma_left := id
  ; comma_right := id
  ; comma_comm x := (eq_refl, true)
  |}.

(** Terminal uniqueness compares these different native maps. *)

(** 终对象唯一性比较这些原生不同的映射。 *)

Example tagged_terminal_uniqueness
  : tagged_terminal_alternative ≈
      (tagged_changed_terminal TaggedTerminalProbe).1.
Proof. apply (tagged_changed_terminal TaggedTerminalProbe).2. exact I. Defined.

(** Equality does not erase the distinct computational tags of the maps. *)

(** 相等不会擦除两条映射各自不同的计算标签。 *)

Example tagged_terminal_distinct_maps_compute
  : (comma_left tagged_terminal_alternative (4, false),
      comma_left (tagged_changed_terminal TaggedTerminalProbe).1
        (4, false)) = ((4, false), (4, true)).
Proof. reflexivity. Defined.

End TaggedTerminal.

(** ** Finite Products without Target Terminal Preservation

    Set [F = F' = K = const Empty] and [H = Id]. Reuse the earlier
    concrete binary-preservation witnesses. [K] fails to preserve the
    setoid terminal, but the Gluing change preserves all finite products. *)

(** ** 目标不保持终对象时的有限积

    取 [F = F' = K = const Empty]、[H = Id]，复用已有具体二元积保持见证。
    [K] 不保持广集终对象，但Gluing变化保持全部有限积。 *)

Section EmptyFiniteProducts.
Local Instance terminal_set_terminal
  : HasTerminal SetCat
  := SetCat_HasTerminal.
Local Instance terminal_set_products
  : HasProduct SetCat
  := SetCat_HasProduct.

(** Identity empty maps supply the compatible local boundary. *)

(** 空广集上的恒等映射提供相容局部边界。 *)

Program Definition EmptyStableBoundaryN
  : (@CompF SetCat SetCat SetCat (ConstF SetCat EmptyS)
        (ConstF SetCat EmptyS)) ⇒
      (@CompF SetCat SetCat SetCat (ConstF SetCat EmptyS) (@IdF SetCat))
  :=
  {|nt X := id
  ; nt_naturality X Y f x := tt
  |}.

(** The local inverse is the original identity isomorphism. *)

(** 局部逆为原有恒等同构。 *)

Definition empty_stable_boundary_iso
  : is_iso (EmptyStableBoundaryN UnitS)
  := (@iso_refl SetCat EmptyS).2.

(** The source choices match the original selected gluing structures. *)

(** 来源选择与原选定粘合结构一致。 *)

Definition empty_stable_cartesian
  : @IsCartF (Gluing (ConstF SetCat EmptyS))
      (Gluing (ConstF SetCat EmptyS))
      (GluingChangeF IdF (ConstF SetCat EmptyS) EmptyStableBoundaryN)
      (Gluing_HasTerminal (ConstF SetCat EmptyS))
      (Gluing_HasProduct (ConstF SetCat EmptyS)
        empty_constant_preserves_products)
  := GluingChange_IsCartF IdF (ConstF SetCat EmptyS) EmptyStableBoundaryN
      empty_constant_preserves_products (λ A B, product_universal)
      empty_constant_preserves_products empty_constant_preserves_products
      terminal_universal empty_stable_boundary_iso.

(** Yet the actual image of the target terminal under [K] is not terminal. *)

(** 然而，目标终对象经 [K] 的实际像并不为终。 *)

Definition empty_stable_target_not_terminal
  : is_terminal ((ConstF SetCat EmptyS) UnitS) → Empty_set
  := empty_constant_not_terminal.

(** The stored finite-product preservation value retains its base mediator. *)

(** 保存的有限积保持值保留其基中介。 *)

Example empty_stable_terminal_base_computes
  : comma_right (@functor_terminal _ _ _ _ _ empty_stable_cartesian
      (GluingTerminal (ConstF SetCat EmptyS) UnitS)).1 tt = tt.
Proof. reflexivity. Defined.

End EmptyFiniteProducts.

(** ** Binary Products without Terminal Preservation

    Change the empty interpretation to constant unit with identity H/K.
    Both endpoint functors and both interpretations preserve binary
    products, but the boundary at unit has no inverse. The image of the
    source gluing terminal admits no map from the target unit gluing. *)

(** ** 保持二元积但不保持终对象

    用恒等H/K将空解释改为常单位解释。两端函子和两个解释都保持二元积，
    但单位处的边界没有逆；来源粘合终对象的像不接受来自目标单位粘合的映射。 *)

Section MissingTerminalBoundary.
Local Instance counter_terminal_products
  : HasProduct SetCat
  := SetCat_HasProduct.

(** Empty-to-unit components define an actual compatible natural boundary. *)

(** 空到单位分量定义实际相容自然边界。 *)

Program Definition EmptyUnitBoundaryN
  : (@CompF SetCat SetCat SetCat (@IdF SetCat) (ConstF SetCat EmptyS)) ⇒
      (@CompF SetCat SetCat SetCat (ConstF SetCat UnitS) (@IdF SetCat))
  :=
  {|nt X := @term SetCat SetCat_HasTerminal EmptyS
  ; nt_naturality X Y f x := tt
  |}.

(** Its inverse would give a point of the empty setoid. *)

(** 它的逆将给出空广集中的点。 *)

Definition empty_unit_boundary_not_iso
  : is_iso (EmptyUnitBoundaryN UnitS) → Empty_set.
Proof. intro H. exact (H.1 tt). Defined.

(** Binary products of the actual Gluing change still satisfy the theorem. *)

(** 实际Gluing变化的二元积仍满足保持定理。 *)

Definition empty_unit_binary_products (X Y : Gluing (ConstF SetCat EmptyS))
  : @is_product (Gluing (ConstF SetCat UnitS))
      (GluingChangeF IdF IdF EmptyUnitBoundaryN X)
      (GluingChangeF IdF IdF EmptyUnitBoundaryN Y)
      (GluingChangeF IdF IdF EmptyUnitBoundaryN
        (@Prod (Gluing (ConstF SetCat EmptyS))
          (Gluing_HasProduct (ConstF SetCat EmptyS)
          empty_constant_preserves_products) X Y))
      (fmap (GluingChangeF IdF IdF EmptyUnitBoundaryN)
        (@Cats.Cat.Product.Core.π1 (Gluing (ConstF SetCat EmptyS))
          (Gluing_HasProduct
          (ConstF SetCat EmptyS) empty_constant_preserves_products) X Y))
      (fmap (GluingChangeF IdF IdF EmptyUnitBoundaryN)
        (@Cats.Cat.Product.Core.π2 (Gluing (ConstF SetCat EmptyS))
          (Gluing_HasProduct
          (ConstF SetCat EmptyS) empty_constant_preserves_products) X Y))
  := gluing_change_product IdF IdF EmptyUnitBoundaryN
      empty_constant_preserves_products (λ A B, product_universal)
      (λ A B, product_universal) unit_model_product X Y.

(** Terminality of the image would supply an impossible left-side map. *)

(** 像的终性将提供不可能存在的左侧映射。 *)

Definition empty_unit_changed_not_terminal
    (HT : @is_terminal (Gluing (ConstF SetCat UnitS))
      (GluingChangeF IdF IdF EmptyUnitBoundaryN
        (GluingTerminal (ConstF SetCat EmptyS) UnitS)))
  : Empty_set
  := comma_left (HT (GluingTerminal (ConstF SetCat UnitS) UnitS)).1 tt.

End MissingTerminalBoundary.
