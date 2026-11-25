From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.Pullback
  Cat.Natural
  Cat.Diagram.Span
  Cat.Gluing.ChangeExponential
  Cat.Functor.ExponentialComparison
  Cat.Limit.Exponential
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Exponential
  Instance.Set.Pullback
  Instance.Set.Terminal
  Instance.Set.Initial
  Instance.Bool.Group.
From CatsTests.gluing Require Import
  Gluing.
From CatsTests.category Require Import
  ProductPreservation.

(** * Actual Gluing Exponential Cospan Transport

    Separate all four category boundaries in both strict orders. Then
    use a nonidentity Reader boundary, explicit comparison inverses and
    one particular setoid pullback to inspect the transported data. *)

(** * 实际粘合指数余跨度运输

    按两个严格次序分离全部四个范畴的边界；随后用非恒等 Reader 边界、
    显式比较逆和一个特定广集拉回检查运输后的数据。 *)

(** ** Increasing Category Bounds

    Supply independent object, hom, equality and auxiliary law levels.
    Inverse and image-pullback hypotheses are introduced only after
    constructing the maps and their naturality squares. *)

(** ** 递增的范畴界

    分别给出独立对象、Hom、相等及辅助律层级；在构造映射及其自然性方形
    之后才引入逆及像拉回假设。 *)

Section IndependentExpPullback.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2 o3 h3 e3 l3.
Constraint h0 < e0, e0 < o0, o0 < l0, l0 < e1.
Constraint e1 < h1, h1 < o1, o1 < l1, l1 < h2.
Constraint h2 < e2, e2 < o2, o2 < l2, l2 < e3.
Constraint e3 < h3, h3 < o3, o3 < l3.
Context {C : Cat@{o0 h0 e0 l0 l0}} {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}} {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context {PC : HasProduct C} {EC : HasExponential PC}
    {PD : HasProduct D} {ED : HasExponential PD}
    {PC' : HasProduct C'} {EC' : HasExponential PC'}
    {PD' : HasProduct D'} {ED' : HasExponential PD'}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (interpretation : ∀ A B : C',
    is_product (F' A) (F' B) (F' ((A × B)%ob)) (fmap F' π1) (fmap F' π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ U V : D,
    is_product (K U) (K V) (K ((U × V)%ob)) (fmap K π1) (fmap K π2)).
Context (X Y : Gluing F).

(** The three maps keep their different endpoints. *)

(** 三个映射保持各自不同的端点。 *)

Definition independent_exp_left
  : Hom (K ((comma_left_ob Y ^ comma_left_ob X)%ob))
      (K (comma_left_ob Y) ^ K (comma_left_ob X))
  := gluing_change_exp_left K target X Y.

(** The tip comparison changes the interpretation's result. *)

(** 共同目标比较改变解释的结果。 *)

Definition independent_exp_tip
  : Hom (K ((F (comma_right_ob Y) ^ comma_left_ob X)%ob))
      (F' (H (comma_right_ob Y)) ^ K (comma_left_ob X))
  := gluing_change_exp_tip H K α target X Y.

(** The right endpoint is the new base exponential's interpretation. *)

(** 右端点是新基指数的解释。 *)

Definition independent_exp_right
  : Hom (K (F ((comma_right_ob Y ^ comma_right_ob X)%ob)))
      (F' ((H (comma_right_ob Y) ^ H (comma_right_ob X))%ob))
  := gluing_change_exp_right H K α base X Y.

(** Both composite interpretations are compared at distinct native levels. *)

(** 在不同原生层级比较两个复合解释。 *)

Definition independent_exp_boundary (A B : C)
  : (α B ^ id[K (F A)]) ∘
      exp_cmp K target (F A) (F B) ∘
      fmap K (exp_cmp F source A B) ≈
      (id[F' (H B)] ^ α A) ∘
      exp_cmp F' interpretation (H A) (H B) ∘
      fmap F' (exp_cmp H base A B) ∘
      α ((B ^ A)%ob)
  := gluing_change_exp_boundary H K α source interpretation base target A B.

(** The actual result square needs no inverse. *)

(** 实际结果方形不需要逆。 *)

Definition independent_exp_result
  : gluing_change_exp_tip H K α target X Y ∘
      fmap K (gluing_exp_result F X Y) ≈
      gluing_exp_result F'
        (GluingChangeF H K α X) (GluingChangeF H K α Y) ∘
      gluing_change_exp_left K target X Y
  := gluing_change_exp_result H K α target X Y.

(** The base square also holds before invertibility hypotheses. *)

(** 基方形也在可逆假设之前成立。 *)

Definition independent_exp_base
  : gluing_change_exp_tip H K α target X Y ∘
      fmap K (gluing_exp_base F source X Y) ≈
      gluing_exp_base F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y) ∘
      gluing_change_exp_right H K α base X Y
  := gluing_change_exp_base H K α source interpretation base target X Y.

(** Naturality extends along the existing cospan paths. *)

(** 自然性沿既有余跨度路径延拓。 *)

Definition independent_exp_cospan
  : (K ∘F ⟨gluing_exp_result F X Y →←
        gluing_exp_base F source X Y⟩D) ⇒
      ⟨gluing_exp_result F'
          (GluingChangeF H K α X) (GluingChangeF H K α Y) →←
        gluing_exp_base F' interpretation
          (GluingChangeF H K α X) (GluingChangeF H K α Y)⟩D
  := GluingExpChangeN H K α source interpretation base target X Y.

Context (left : is_iso (gluing_change_exp_left K target X Y)).
Context (boundaryY : is_iso (α (comma_right_ob Y))).
Context (boundaryExp : is_iso
    (α ((comma_right_ob Y ^ comma_right_ob X)%ob))).
Context (baseExp : is_iso (exp_cmp H base
    (comma_right_ob X) (comma_right_ob Y))).
Context (targetExp : is_iso (exp_cmp K target
    (comma_left_ob X) (F (comma_right_ob Y)))).

(** The right inverse retains the mapped base inverse. *)

(** 右逆保留基逆的像。 *)

Definition independent_exp_right_iso
  : is_iso (gluing_change_exp_right H K α base X Y)
  := gluing_change_exp_right_iso H K α base X Y boundaryExp baseExp.

(** The tip inverse retains the result boundary's inverse. *)

(** 共同目标逆保留结果边界的逆。 *)

Definition independent_exp_tip_iso
  : is_iso (gluing_change_exp_tip H K α target X Y)
  := gluing_change_exp_tip_iso H K α target X Y boundaryY targetExp.

(** The three local witnesses assemble a diagram isomorphism. *)

(** 三个局部见证组成图式同构。 *)

Definition independent_exp_cospan_iso
  : independent_exp_cospan ⦂ _ ≅N _
  := gluing_change_exp_cospan_iso H K α source interpretation base target
      X Y left independent_exp_right_iso independent_exp_tip_iso.

Context (E : D)
    (p : Hom E (comma_left_ob Y ^ comma_left_ob X))
    (q : Hom E (F ((comma_right_ob Y ^ comma_right_ob X)%ob))).
Context (image : is_pullback
    (fmap K (gluing_exp_result F X Y))
    (fmap K (gluing_exp_base F source X Y))
    (K E) (fmap K p) (fmap K q)).

(** Only this image cone must be a pullback; no global selection occurs. *)

(** 只有此像锥须为拉回，不作全局选择。 *)

Definition independent_exp_pullback
  : is_pullback (gluing_exp_result F'
        (GluingChangeF H K α X) (GluingChangeF H K α Y))
      (gluing_exp_base F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y))
      (K E) (gluing_change_exp_left K target X Y ∘ fmap K p)
      (gluing_change_exp_right H K α base X Y ∘ fmap K q)
  := gluing_change_exp_pullback H K α source interpretation base target
      X Y E p q image left independent_exp_right_iso independent_exp_tip_iso.

(** The existing target theorem supplies evaluation and its universal
    property, without equating the two base exponential presentations. *)

(** 既有目标定理给出求值及泛性质，不识别两种基指数表示。 *)

Definition independent_exp_candidate
  : ∃ ev : (@Hom (Gluing F'))
      (@Prod (Gluing F') (Gluing_HasProduct F' interpretation)
        (GluingExp F' (GluingChangeF H K α X) (GluingChangeF H K α Y)
          (K E) (gluing_change_exp_right H K α base X Y ∘ fmap K q))
        (GluingChangeF H K α X)) (GluingChangeF H K α Y),
      @is_exp (Gluing F') (Gluing_HasProduct F' interpretation)
        (GluingChangeF H K α X) (GluingChangeF H K α Y)
        (GluingExp F' (GluingChangeF H K α X) (GluingChangeF H K α Y)
          (K E) (gluing_change_exp_right H K α base X Y ∘ fmap K q)) ev
  := (_; gluing_change_exp_universal H K α
      source interpretation base target X Y E p q image
      left independent_exp_right_iso independent_exp_tip_iso).

End IndependentExpPullback.

(** ** Reversed Category Bounds

    Supply independent object, hom, equality and auxiliary law levels.
    Inverse and image-pullback hypotheses are introduced only after
    constructing the maps and their naturality squares. *)

(** ** 反向的范畴界

    分别给出独立对象、Hom、相等及辅助律层级；在构造映射及其自然性方形
    之后才引入逆及像拉回假设。 *)

Section ReversedExpPullback.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2 o3 h3 e3 l3.
Constraint h3 < e3, e3 < o3, o3 < l3, l3 < e2.
Constraint e2 < h2, h2 < o2, o2 < l2, l2 < h1.
Constraint h1 < e1, e1 < o1, o1 < l1, l1 < e0.
Constraint e0 < h0, h0 < o0, o0 < l0.
Context {C : Cat@{o0 h0 e0 l0 l0}} {D : Cat@{o1 h1 e1 l1 l1}}.
Context {C' : Cat@{o2 h2 e2 l2 l2}} {D' : Cat@{o3 h3 e3 l3 l3}}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context {PC : HasProduct C} {EC : HasExponential PC}
    {PD : HasProduct D} {ED : HasExponential PD}
    {PC' : HasProduct C'} {EC' : HasExponential PC'}
    {PD' : HasProduct D'} {ED' : HasExponential PD'}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (interpretation : ∀ A B : C',
    is_product (F' A) (F' B) (F' ((A × B)%ob)) (fmap F' π1) (fmap F' π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ U V : D,
    is_product (K U) (K V) (K ((U × V)%ob)) (fmap K π1) (fmap K π2)).
Context (X Y : Gluing F).

(** The three maps keep their different endpoints. *)

(** 三个映射保持各自不同的端点。 *)

Definition reversed_exp_left
  : Hom (K ((comma_left_ob Y ^ comma_left_ob X)%ob))
      (K (comma_left_ob Y) ^ K (comma_left_ob X))
  := gluing_change_exp_left K target X Y.

(** The tip comparison changes the interpretation's result. *)

(** 共同目标比较改变解释的结果。 *)

Definition reversed_exp_tip
  : Hom (K ((F (comma_right_ob Y) ^ comma_left_ob X)%ob))
      (F' (H (comma_right_ob Y)) ^ K (comma_left_ob X))
  := gluing_change_exp_tip H K α target X Y.

(** The right endpoint is the new base exponential's interpretation. *)

(** 右端点是新基指数的解释。 *)

Definition reversed_exp_right
  : Hom (K (F ((comma_right_ob Y ^ comma_right_ob X)%ob)))
      (F' ((H (comma_right_ob Y) ^ H (comma_right_ob X))%ob))
  := gluing_change_exp_right H K α base X Y.

(** Both composite interpretations are compared at distinct native levels. *)

(** 在不同原生层级比较两个复合解释。 *)

Definition reversed_exp_boundary (A B : C)
  : (α B ^ id[K (F A)]) ∘
      exp_cmp K target (F A) (F B) ∘
      fmap K (exp_cmp F source A B) ≈
      (id[F' (H B)] ^ α A) ∘
      exp_cmp F' interpretation (H A) (H B) ∘
      fmap F' (exp_cmp H base A B) ∘
      α ((B ^ A)%ob)
  := gluing_change_exp_boundary H K α source interpretation base target A B.

(** The actual result square needs no inverse. *)

(** 实际结果方形不需要逆。 *)

Definition reversed_exp_result
  : gluing_change_exp_tip H K α target X Y ∘
      fmap K (gluing_exp_result F X Y) ≈
      gluing_exp_result F'
        (GluingChangeF H K α X) (GluingChangeF H K α Y) ∘
      gluing_change_exp_left K target X Y
  := gluing_change_exp_result H K α target X Y.

(** The base square also holds before invertibility hypotheses. *)

(** 基方形也在可逆假设之前成立。 *)

Definition reversed_exp_base
  : gluing_change_exp_tip H K α target X Y ∘
      fmap K (gluing_exp_base F source X Y) ≈
      gluing_exp_base F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y) ∘
      gluing_change_exp_right H K α base X Y
  := gluing_change_exp_base H K α source interpretation base target X Y.

(** Naturality extends along the existing cospan paths. *)

(** 自然性沿既有余跨度路径延拓。 *)

Definition reversed_exp_cospan
  : (K ∘F ⟨gluing_exp_result F X Y →←
        gluing_exp_base F source X Y⟩D) ⇒
      ⟨gluing_exp_result F'
          (GluingChangeF H K α X) (GluingChangeF H K α Y) →←
        gluing_exp_base F' interpretation
          (GluingChangeF H K α X) (GluingChangeF H K α Y)⟩D
  := GluingExpChangeN H K α source interpretation base target X Y.

Context (left : is_iso (gluing_change_exp_left K target X Y)).
Context (boundaryY : is_iso (α (comma_right_ob Y))).
Context (boundaryExp : is_iso
    (α ((comma_right_ob Y ^ comma_right_ob X)%ob))).
Context (baseExp : is_iso (exp_cmp H base
    (comma_right_ob X) (comma_right_ob Y))).
Context (targetExp : is_iso (exp_cmp K target
    (comma_left_ob X) (F (comma_right_ob Y)))).

(** The right inverse retains the mapped base inverse. *)

(** 右逆保留基逆的像。 *)

Definition reversed_exp_right_iso
  : is_iso (gluing_change_exp_right H K α base X Y)
  := gluing_change_exp_right_iso H K α base X Y boundaryExp baseExp.

(** The tip inverse retains the result boundary's inverse. *)

(** 共同目标逆保留结果边界的逆。 *)

Definition reversed_exp_tip_iso
  : is_iso (gluing_change_exp_tip H K α target X Y)
  := gluing_change_exp_tip_iso H K α target X Y boundaryY targetExp.

(** The three local witnesses assemble a diagram isomorphism. *)

(** 三个局部见证组成图式同构。 *)

Definition reversed_exp_cospan_iso
  : reversed_exp_cospan ⦂ _ ≅N _
  := gluing_change_exp_cospan_iso H K α source interpretation base target
      X Y left reversed_exp_right_iso reversed_exp_tip_iso.

Context (E : D)
    (p : Hom E (comma_left_ob Y ^ comma_left_ob X))
    (q : Hom E (F ((comma_right_ob Y ^ comma_right_ob X)%ob))).
Context (image : is_pullback
    (fmap K (gluing_exp_result F X Y))
    (fmap K (gluing_exp_base F source X Y))
    (K E) (fmap K p) (fmap K q)).

(** Only this image cone must be a pullback; no global selection occurs. *)

(** 只有此像锥须为拉回，不作全局选择。 *)

Definition reversed_exp_pullback
  : is_pullback (gluing_exp_result F'
        (GluingChangeF H K α X) (GluingChangeF H K α Y))
      (gluing_exp_base F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y))
      (K E) (gluing_change_exp_left K target X Y ∘ fmap K p)
      (gluing_change_exp_right H K α base X Y ∘ fmap K q)
  := gluing_change_exp_pullback H K α source interpretation base target
      X Y E p q image left reversed_exp_right_iso reversed_exp_tip_iso.

(** The existing target theorem supplies evaluation and its universal
    property, without equating the two base exponential presentations. *)

(** 既有目标定理给出求值及泛性质，不识别两种基指数表示。 *)

Definition reversed_exp_candidate
  : ∃ ev : (@Hom (Gluing F'))
      (@Prod (Gluing F') (Gluing_HasProduct F' interpretation)
        (GluingExp F' (GluingChangeF H K α X) (GluingChangeF H K α Y)
          (K E) (gluing_change_exp_right H K α base X Y ∘ fmap K q))
        (GluingChangeF H K α X)) (GluingChangeF H K α Y),
      @is_exp (Gluing F') (Gluing_HasProduct F' interpretation)
        (GluingChangeF H K α X) (GluingChangeF H K α Y)
        (GluingExp F' (GluingChangeF H K α X) (GluingChangeF H K α Y)
          (K E) (gluing_change_exp_right H K α base X Y ∘ fmap K q)) ev
  := (_; gluing_change_exp_universal H K α
      source interpretation base target X Y E p q image
      left reversed_exp_right_iso reversed_exp_tip_iso).

End ReversedExpPullback.

(** The theory does not enable a global pullback model. *)

(** 此理论不启用全局拉回模型。 *)

Fail Definition automatic_exp_change_pullbacks
  : HasPullback SetCat
  := ltac:(typeclasses eauto).

(** Nor does it enable the target Gluing product choice. *)

(** 也不启用目标粘合积选择。 *)

Fail Definition automatic_exp_change_products
  : HasProduct (Gluing (@IdF SetCat))
  := ltac:(typeclasses eauto).

(** ** A Nonidentity Reader Boundary

    Enable setoid structures locally. Both interpretations read a Boolean
    environment, while the boundary reverses that environment. The base
    and target changes are identity functors. All three comparison
    inverses and the one pullback remain explicit data. *)

(** ** 非恒等 Reader 边界

    局部启用广集结构。两侧解释都读取布尔环境，边界将环境反转；基与目标
    变化为恒等函子。三个比较逆及一个拉回始终作为显式数据给出。 *)

Section ReaderBoundary.
Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasExponential.
Local Existing Instance SetCat_HasPullback.

(** The interpretation is the existing exponential functor. *)

(** 解释为已有的取指数函子。 *)

Definition ExpChangeReaderF
  : Fct SetCat SetCat
  := (-^ BoolS).

(** Reuse right-adjoint product preservation rather than a new proof. *)

(** 复用右伴随保持积，不另作证明。 *)

Definition exp_change_reader_products (A B : SetC)
  : is_product (ExpChangeReaderF A) (ExpChangeReaderF B)
      (ExpChangeReaderF ((A × B)%ob))
      (fmap ExpChangeReaderF π1) (fmap ExpChangeReaderF π2)
  := exp_preserves_product BoolS product_universal.

(** Reverse the environment without changing the value setoid. Its
    respectful action retains the input Type-valued witness at that index. *)

(** 反转环境但不改变值广集；保相等作用保留该索引处的输入 Type 值见证。 *)

Program Definition ExpChangeSwapN
  : (@CompF SetCat SetCat SetCat IdF ExpChangeReaderF) ⇒
      (@CompF SetCat SetCat SetCat ExpChangeReaderF IdF)
  :=
  {|nt X :=
      {|func f :=
          {|func b := f (negb b)
          ; func_proper b c H :=
              @func_proper BoolS X f (negb b) (negb c) (f_equal negb H)
          |}
      ; func_proper f g H b := H (negb b)
      |}
  |}.
Next Obligation. intros g b. reflexivity. Defined.

(** The same reversal is an inverse at each object. *)

(** 相同反转给出每个对象处的逆。 *)

Definition exp_change_swap_iso (X : SetC)
  : is_iso (ExpChangeSwapN X).
Proof.
  exists (ExpChangeSwapN X). split; intros f b;
    change (f (negb (negb b)) ≈S f b); destruct b; reflexivity.
Defined.

(** Identity comparisons have transparent identity inverse maps for these
    concrete choices; no general model instance is registered. *)

(** 对这些具体选择，恒等比较具有透明的恒等逆映射；不注册一般模型实例。 *)

Definition exp_change_identity_comparison (A B : SetC)
  : is_iso (exp_cmp (@IdF SetCat)
      (λ A B, product_universal) A B).
Proof. exists id. split; intros f a; reflexivity. Defined.

(** The structure reads the environment into an observable ignored tag. *)

(** 结构将环境读入可观察的被忽略标签。 *)

Program Definition exp_change_reader_structure
  : TaggedGluingS →r ExpChangeReaderF TaggedGluingS
  :=
  {|func x :=
      {|func b := (fst x, xorb (snd x) b)
      ; func_proper b c H := (eq_refl, false)
      |}
  ; func_proper x y H b := H
  |}.

(** Keep the original tagged object and the actual structure map. *)

(** 保留原标签对象及实际结构映射。 *)

Program Definition ExpChangeProbe
  : Gluing ExpChangeReaderF
  :=
  {|comma_left_ob := TaggedGluingS
  ; comma_right_ob := TaggedGluingS
  ; comma_arrow := exp_change_reader_structure
  |}.

(** Select just the old cospan's pullback, not a Gluing exponential family. *)

(** 只选择旧余跨度的拉回，不选择粘合指数族。 *)

Definition ExpChangeSourcePb
  : SetC
  := Pb (gluing_exp_result ExpChangeReaderF ExpChangeProbe ExpChangeProbe)
      (gluing_exp_base ExpChangeReaderF exp_change_reader_products
        ExpChangeProbe ExpChangeProbe).

(** The first leg keeps the original function. *)

(** 第一锥腿保留原函数。 *)

Definition exp_change_source_p
  : ExpChangeSourcePb →r (TaggedGluingS →S TaggedGluingS)
  := pb1 _ _.

(** The second leg is the original reader of base functions. *)

(** 第二锥腿为原有读取基函数的 Reader。 *)

Definition exp_change_source_q
  : ExpChangeSourcePb →r ExpChangeReaderF (TaggedGluingS →S TaggedGluingS)
  := pb2 _ _.

(** For identity [K], its particular image pullback is the supplied one. *)

(** 对恒等 [K]，其特定像拉回就是给定拉回。 *)

Definition exp_change_image_pullback
  : is_pullback
      (fmap (@IdF SetCat)
        (gluing_exp_result ExpChangeReaderF
          ExpChangeProbe ExpChangeProbe))
      (fmap (@IdF SetCat)
        (gluing_exp_base ExpChangeReaderF exp_change_reader_products
          ExpChangeProbe ExpChangeProbe))
      ExpChangeSourcePb exp_change_source_p exp_change_source_q
  := pullback_universal.

(** The right comparison uses the saved boundary and base-comparison inverses. *)

(** 右比较使用保存的边界逆及基比较逆。 *)

Definition exp_change_right_inverse
  : is_iso (gluing_change_exp_right IdF IdF ExpChangeSwapN
      (λ A B, product_universal) ExpChangeProbe ExpChangeProbe)
  := gluing_change_exp_right_iso IdF IdF ExpChangeSwapN
      (λ A B, product_universal) ExpChangeProbe ExpChangeProbe
      (exp_change_swap_iso (TaggedGluingS →S TaggedGluingS))
      (exp_change_identity_comparison TaggedGluingS TaggedGluingS).

(** The common target comparison uses a different exponential endpoint. *)

(** 共同目标比较使用不同的指数端点。 *)

Definition exp_change_tip_inverse
  : is_iso (gluing_change_exp_tip IdF IdF ExpChangeSwapN
      (λ A B, product_universal) ExpChangeProbe ExpChangeProbe)
  := gluing_change_exp_tip_iso IdF IdF ExpChangeSwapN
      (λ A B, product_universal) ExpChangeProbe ExpChangeProbe
      (exp_change_swap_iso TaggedGluingS)
      (exp_change_identity_comparison TaggedGluingS
        (ExpChangeReaderF TaggedGluingS)).

(** Transport the particular pullback using the actual cospan transformation. *)

(** 用实际余跨度自然变换运输此特定拉回。 *)

Definition exp_change_transported_pullback
  : is_pullback
      (gluing_exp_result ExpChangeReaderF
        (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe)
        (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe))
      (gluing_exp_base ExpChangeReaderF exp_change_reader_products
        (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe)
        (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe))
      ExpChangeSourcePb
      (gluing_change_exp_left IdF (λ A B, product_universal)
        ExpChangeProbe ExpChangeProbe ∘ exp_change_source_p)
      (gluing_change_exp_right IdF IdF ExpChangeSwapN
        (λ A B, product_universal) ExpChangeProbe ExpChangeProbe ∘
        exp_change_source_q)
  := gluing_change_exp_pullback IdF IdF ExpChangeSwapN
      exp_change_reader_products exp_change_reader_products
      (λ A B, product_universal) (λ A B, product_universal)
      ExpChangeProbe ExpChangeProbe ExpChangeSourcePb
      exp_change_source_p exp_change_source_q exp_change_image_pullback
      (exp_change_identity_comparison TaggedGluingS TaggedGluingS)
      exp_change_right_inverse exp_change_tip_inverse.

(** An environment-dependent family exposes the right comparison's action. *)

(** 依赖环境的族显露右比较的作用。 *)

Program Definition exp_change_function_family
  : ExpChangeReaderF (TaggedGluingS →S TaggedGluingS)
  :=
  {|func b :=
      {|func x := (fst x, xorb (snd x) b)
      ; func_proper x y H := H
      |}
  ; func_proper b c H x := (eq_refl, false)
  |}.

(** Constant identity functions give a point of the old pullback. *)

(** 常恒等函数给出旧拉回的一个点。 *)

Program Definition exp_change_identity_family
  : ExpChangeReaderF (TaggedGluingS →S TaggedGluingS)
  :=
  {|func b := id_resp
  ; func_proper b c H x := (eq_refl, true)
  |}.

(** The point stores a genuine Type-valued commuting witness. *)

(** 此点保存真正的 Type 值交换见证。 *)

Definition ExpChangePoint
  : ExpChangeSourcePb
  := (id_resp; (exp_change_identity_family; λ x b, (eq_refl, false))).

(** A constant point supplies a small external test cone. *)

(** 常值点给出小型外部测试锥。 *)

Program Definition exp_change_point_map
  : UnitS →r ExpChangeSourcePb
  :=
  {|func _ := ExpChangePoint
  |}.
Next Obligation. intros x y H. split; reflexivity. Defined.

(** The transported cone's commutativity comes from its supplied pullback,
    without comparing commuting-square witnesses. *)

(** 运输后锥的交换性来自其给定拉回，不比较交换方形见证。 *)

Definition exp_change_test_cone_comm
  : gluing_exp_result ExpChangeReaderF
      (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe)
      (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe) ∘
      ((gluing_change_exp_left IdF (λ A B, product_universal)
        ExpChangeProbe ExpChangeProbe ∘ exp_change_source_p) ∘
        exp_change_point_map) ≈
    gluing_exp_base ExpChangeReaderF exp_change_reader_products
      (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe)
      (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe) ∘
      ((gluing_change_exp_right IdF IdF ExpChangeSwapN
        (λ A B, product_universal) ExpChangeProbe ExpChangeProbe ∘
        exp_change_source_q) ∘ exp_change_point_map).
Proof.
  rewrite <- (@comp_assoc SetCat _ _ _ _ _ _ exp_change_point_map).
  rewrite <- (@comp_assoc SetCat _ _ _ _ _ _ exp_change_point_map).
  apply comp_proper; [exact (fst exp_change_transported_pullback) | reflexivity].
Defined.

(** This is the transported universal mediator, not a hand-built point map. *)

(** 这是运输后的泛中介，而非手工构造的点映射。 *)

Definition exp_change_transported_mediator
  : UnitS →r ExpChangeSourcePb
  := (snd exp_change_transported_pullback UnitS
      ((gluing_change_exp_left IdF (λ A B, product_universal)
        ExpChangeProbe ExpChangeProbe ∘ exp_change_source_p) ∘
        exp_change_point_map)
      ((gluing_change_exp_right IdF IdF ExpChangeSwapN
        (λ A B, product_universal) ExpChangeProbe ExpChangeProbe ∘
        exp_change_source_q) ∘ exp_change_point_map)
      exp_change_test_cone_comm).1.

(** The left comparison retains the function data. *)

(** 左比较保留函数数据。 *)

Example exp_change_left_computes
  : gluing_change_exp_left IdF (λ A B, product_universal)
      ExpChangeProbe ExpChangeProbe id_resp (3%nat, false) = (3%nat, false).
Proof. reflexivity. Defined.

(** The right comparison reverses the represented family environment. *)

(** 右比较反转所表示函数族的环境。 *)

Example exp_change_right_computes
  : gluing_change_exp_right IdF IdF ExpChangeSwapN
      (λ A B, product_universal) ExpChangeProbe ExpChangeProbe
      exp_change_function_family true (3%nat, false) = (3%nat, false).
Proof. reflexivity. Defined.

(** Its supplied inverse keeps the same transparent reversal operation. *)

(** 所给的逆保留相同的透明反转操作。 *)

Example exp_change_right_inverse_computes
  : exp_change_right_inverse.1 exp_change_function_family
      false (3%nat, false) = (3%nat, true).
Proof. reflexivity. Defined.

(** The common-target comparison changes the result reader at each input. *)

(** 共同目标比较在每个输入处改变结果 Reader。 *)

Example exp_change_tip_computes
  : gluing_change_exp_tip IdF IdF ExpChangeSwapN
      (λ A B, product_universal) ExpChangeProbe ExpChangeProbe
      exp_change_reader_structure (3%nat, false) true = (3%nat, false).
Proof. reflexivity. Defined.

(** Its inverse also computes without evaluating inverse-law tokens. *)

(** 其逆同样无需对互逆律标记求值即可计算。 *)

Example exp_change_tip_inverse_computes
  : exp_change_tip_inverse.1 exp_change_reader_structure
      (3%nat, false) false = (3%nat, true).
Proof. reflexivity. Defined.

(** The actual changed structure includes the same observable reversal. *)

(** 实际变化后结构包含同样可观察的反转。 *)

Example exp_change_actual_structure_computes
  : comma_arrow (GluingChangeF IdF IdF ExpChangeSwapN ExpChangeProbe)
      (3%nat, false) true = (3%nat, false).
Proof. reflexivity. Defined.

(** Both coordinates of the transported universal mediator compute. *)

(** 运输后的泛中介的两个坐标均可计算。 *)

Example exp_change_mediator_left_computes
  : (exp_change_transported_mediator tt).1 (3%nat, false) = (3%nat, false).
Proof. reflexivity. Defined.

(** The second coordinate recovers the reader of base functions. *)

(** 第二坐标恢复读取基函数的 Reader。 *)

Example exp_change_mediator_right_computes
  : (exp_change_transported_mediator tt).2.1 true (3%nat, false) =
      (3%nat, false).
Proof. reflexivity. Defined.

(** The boundary's respectful map transports an actual Boolean witness. *)

(** 边界的保相等映射运输实际布尔见证。 *)

Example exp_change_boundary_token_computes
  : snd (@func_proper _ _ (ExpChangeSwapN TaggedGluingS)
      (exp_change_reader_structure (3%nat, false))
      (exp_change_reader_structure (3%nat, true))
      (λ b, (eq_refl, b)) true) = false.
Proof. reflexivity. Defined.

(** Right comparison respects distinct native family representatives. *)

(** 右比较保持不同原生函数族代表之间的相等。 *)

Example exp_change_comparison_proper
  : gluing_change_exp_right IdF IdF ExpChangeSwapN
      (λ A B, product_universal) ExpChangeProbe ExpChangeProbe
      exp_change_function_family ≈S
      gluing_change_exp_right IdF IdF ExpChangeSwapN
        (λ A B, product_universal) ExpChangeProbe ExpChangeProbe
        exp_change_identity_family.
Proof. apply func_proper. intros b [n t]. exact (eq_refl, true). Defined.

End ReaderBoundary.

(** ** Binary Products and an Invertible Boundary Are Not Enough

    The empty constant target functor preserves binary products. Its
    boundary to the empty interpretation is a natural isomorphism, and
    the actual cospan transformation exists. The left exponential
    comparison still cannot be inverted. This separates the inputs of
    the transport theorem; it does not assert failure of exponential
    preservation by the Gluing change itself. *)

(** ** 二元积及可逆边界仍不足够

    常空目标函子保持二元积，其到常空解释的边界为自然同构，实际余跨度
    自然变换也存在。但左指数比较仍不可逆。此例区分运输定理的各项输入，
    不声称粘合变化本身不能保持指数。 *)

Section EmptyCospanComparison.
Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasExponential.

(** A fixed identity gluing object keeps both exponential endpoints concrete. *)

(** 固定恒等粘合对象使两个指数端点保持具体。 *)

Program Definition ExpEmptyProbe
  : Gluing (@IdF SetCat)
  :=
  {|comma_left_ob := BoolS
  ; comma_right_ob := BoolS
  ; comma_arrow := id
  |}.

(** Both sides of the boundary are the empty constant functor. *)

(** 边界两侧都为常空函子。 *)

Program Definition ExpEmptyBoundaryN
  : (@CompF SetCat SetCat SetCat (ConstF SetCat EmptyS) IdF) ⇒
      (@CompF SetCat SetCat SetCat (ConstF SetCat EmptyS) IdF)
  :=
  {|nt X := id
  ; nat_naturality X Y f x := tt
  |}.

(** This boundary has explicit identity inverse components. *)

(** 此边界具有显式恒等逆分量。 *)

Definition exp_empty_boundary_iso
  : ExpEmptyBoundaryN ⦂ _ ≅N _
  := λ X, (@iso_refl SetCat EmptyS).2.

(** The cospan transformation needs no exponential inverses. *)

(** 余跨度自然变换不需要指数的逆。 *)

Definition ExpEmptyCospanN
  : @Nat CospanShape SetCat
      (@CompF CospanShape SetCat SetCat (ConstF SetCat EmptyS)
      ⟨gluing_exp_result IdF ExpEmptyProbe ExpEmptyProbe →←
        gluing_exp_base IdF (λ A B, product_universal)
          ExpEmptyProbe ExpEmptyProbe⟩D)
      ⟨gluing_exp_result (ConstF SetCat EmptyS)
          (GluingChangeF IdF (ConstF SetCat EmptyS)
            ExpEmptyBoundaryN ExpEmptyProbe)
          (GluingChangeF IdF (ConstF SetCat EmptyS)
            ExpEmptyBoundaryN ExpEmptyProbe) →←
        gluing_exp_base (ConstF SetCat EmptyS)
          empty_constant_preserves_products
          (GluingChangeF IdF (ConstF SetCat EmptyS)
            ExpEmptyBoundaryN ExpEmptyProbe)
          (GluingChangeF IdF (ConstF SetCat EmptyS)
            ExpEmptyBoundaryN ExpEmptyProbe)⟩D
  := GluingExpChangeN IdF (ConstF SetCat EmptyS) ExpEmptyBoundaryN
      (λ A B, product_universal) empty_constant_preserves_products
      (λ A B, product_universal) empty_constant_preserves_products
      ExpEmptyProbe ExpEmptyProbe.

(** The existing empty-comparison counterexample applies to the actual
    left component, despite all the binary-product hypotheses above. *)

(** 尽管上述二元积假设全部成立，既有常空比较反例仍适用于实际左分量。 *)

Definition exp_empty_left_not_iso
  : is_iso (gluing_change_exp_left (ConstF SetCat EmptyS)
      empty_constant_preserves_products ExpEmptyProbe ExpEmptyProbe) → Empty_set
  := empty_constant_comparison_not_iso.

(** Hence the induced cospan transformation is not a natural isomorphism. *)

(** 因而诱导的余跨度变换不是自然同构。 *)

Definition exp_empty_cospan_not_iso
    (H : ExpEmptyCospanN ⦂ _ ≅N _)
  : Empty_set
  := exp_empty_left_not_iso (H cospan_left).

End EmptyCospanComparison.
