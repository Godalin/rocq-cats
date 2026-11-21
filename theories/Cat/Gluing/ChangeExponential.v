From Cats Require Export
  Cat.Gluing.Exponential
  Cat.Gluing.Change.
From Cats Require Import
  Cat.Core
  Cat.Isomorphism
  Cat.Natural
  Cat.Product.Core
  Cat.Pullback
  Cat.Exponential.Functor
  Cat.Functor.ComparisonNaturality
  Cat.Limit.Pullback
  Cat.Limit.Transport.

(** * Transporting the Gluing Exponential Cospan

    Model change compares the old exponential cospan after [K] with the
    actual cospan of the changed glued objects. Weak comparison naturality
    and composition prove its two squares. Invertibility and preservation
    of the particular pullback are separate inputs; binary-product
    preservation alone implies neither. No terminal choices are needed. *)

(** * 运输粘合指数余跨度

    模型变化将旧指数余跨度的 [K] 像与变化后粘合对象的实际余跨度比较。
    弱比较自然性及复合律给出两个方形；可逆性和特定拉回的保持性是独立输入，
    二元积保持性本身不蕴含它们。不需要终对象选择。 *)

(** ** The Three Comparison Maps and Their Squares

    Fix products and exponentials in four categories, the interpretation
    functors [F], [F'], model changes [H], [K] and [α : K F ⇒ F' H].
    Supply binary-product preservation for all four functors. Construct
    the cospan comparison without assuming any component invertible. *)

(** ** 三个比较映射及其方形

    固定四个范畴中的积和指数、解释函子 [F]、[F']、模型变化 [H]、[K]
    及 [α : K F ⇒ F' H]，并给出四个函子的二元积保持性。构造余跨度比较
    时不假设任何分量可逆。 *)

Section ExponentialCospanChange.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}
    `{PC' : !HasProduct C'} `{EC' : !HasExponential PC'}
    `{PD' : !HasProduct D'} `{ED' : !HasExponential PD'}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (interpretation : ∀ A B : C',
    is_product (F' A) (F' B) (F' ((A × B)%ob)) (fmap F' π1) (fmap F' π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ U V : D,
    is_product (K U) (K V) (K ((U × V)%ob)) (fmap K π1) (fmap K π2)).

(** The left comparison transports functions between the left objects. *)

(** 左比较运输左对象之间的函数。 *)

Definition gluing_change_exp_left (X Y : Gluing F)
  : Hom (K ((comma_left_ob Y ^ comma_left_ob X)%ob))
      (K (comma_left_ob Y) ^ K (comma_left_ob X))
  := exp_cmp K target
      (comma_left_ob X) (comma_left_ob Y).

(** The common target also changes the result through the boundary. *)

(** 共同目标还通过边界改变结果。 *)

Definition gluing_change_exp_tip (X Y : Gluing F)
  : Hom (K ((F (comma_right_ob Y) ^ comma_left_ob X)%ob))
      (F' (H (comma_right_ob Y)) ^ K (comma_left_ob X))
  := exp_map (α (comma_right_ob Y)) ∘
      exp_cmp K target
        (comma_left_ob X) (F (comma_right_ob Y)).

(** The right comparison changes the represented base exponential.
    Its codomain is [F' (H B ^ H A)], not [F' (H (B ^ A))]. *)

(** 右比较改变所表示的基指数；其陪域为 [F' (H B ^ H A)]，而非
    [F' (H (B ^ A))]。 *)

Definition gluing_change_exp_right (X Y : Gluing F)
  : Hom (K (F ((comma_right_ob Y ^ comma_right_ob X)%ob)))
      (F' ((H (comma_right_ob Y) ^ H (comma_right_ob X))%ob))
  := fmap F' (exp_cmp H base
      (comma_right_ob X) (comma_right_ob Y)) ∘
      α ((comma_right_ob Y ^ comma_right_ob X)%ob).

(** The mixed boundary law for the composite interpretations factors
    through their original weak comparisons. No exponential preservation
    is required of [F] or [F']. *)

(** 复合解释的混合边界律经原有弱比较分解，不要求 [F] 或 [F'] 保持指数。 *)

Lemma gluing_change_exp_boundary (A B : C)
  : (α B ^ id[K (F A)]) ∘
      exp_cmp K target (F A) (F B) ∘
      fmap K (exp_cmp F source A B) ≈
      (id[F' (H B)] ^ α A) ∘
      exp_cmp F' interpretation (H A) (H B) ∘
      fmap F' (exp_cmp H base A B) ∘
      α ((B ^ A)%ob).
Proof.
  transitivity ((α B ^ id[K (F A)]) ∘
    exp_cmp (K ∘F F)
      (preserved_product_comp F K source target) A B).
  - rewrite comp_assoc. apply comp_l. symmetry.
    apply exp_cmp_comp.
  - transitivity ((id[F' (H B)] ^ α A) ∘
      exp_cmp (F' ∘F H)
        (preserved_product_comp H F' base interpretation) A B ∘
      α ((B ^ A)%ob)).
    + exact (exp_cmp_boundary (K ∘F F) (F' ∘F H)
        (preserved_product_comp F K source target)
        (preserved_product_comp H F' base interpretation) α A B).
    + rewrite (exp_cmp_comp H F'
        base interpretation
        (preserved_product_comp H F' base interpretation) A B).
      rewrite !comp_assoc. reflexivity.
Defined.

(** Naturality in the result intertwines the actual target structure
    arrow, including the retained identity in its comma presentation. *)

(** 结果自然性使实际目标结构箭头相容，包括逗号表示中保留的恒等。 *)

Lemma gluing_change_exp_result (X Y : Gluing F)
  : gluing_change_exp_tip X Y ∘
      fmap K (gluing_exp_result F X Y) ≈
      gluing_exp_result F'
        (GluingChangeF H K α X) (GluingChangeF H K α Y) ∘
      gluing_change_exp_left X Y.
Proof.
  pose proof (exp_cmp_natural K target
    id[comma_left_ob X] (comma_arrow Y)) as N.
  rewrite (fmap_id (IsFct := isFct K)), !exp_dimap_id_r in N.
  unfold gluing_change_exp_tip, gluing_change_exp_left,
    gluing_exp_result.
  rewrite comp_assoc, N, <- comp_assoc, <- exp_map_comp,
    (gluing_change_arrow H K α Y). reflexivity.
Defined.

(** Input restriction and the mixed boundary give the other square. *)

(** 输入限制与混合边界给出另一个方形。 *)

Lemma gluing_change_exp_base (X Y : Gluing F)
  : gluing_change_exp_tip X Y ∘
      fmap K (gluing_exp_base F source X Y) ≈
      gluing_exp_base F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y) ∘
      gluing_change_exp_right X Y.
Proof.
  pose proof (exp_cmp_natural K target
    (comma_arrow X) id[F (comma_right_ob Y)]) as N.
  rewrite (fmap_id (IsFct := isFct K)) in N.
  unfold gluing_change_exp_tip, gluing_change_exp_right,
    gluing_exp_base.
  rewrite (fmap_comp (IsFct := isFct K)).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc
    (exp_cmp K target
      (comma_left_ob X) (F (comma_right_ob Y)))).
  rewrite N.
  rewrite <- !comp_assoc.
  assert (E : exp_map (α (comma_right_ob Y)) ∘
      (id[K (F (comma_right_ob Y))] ^ fmap K (comma_arrow X)) ≈
      (id[F' (H (comma_right_ob Y))] ^ fmap K (comma_arrow X)) ∘
      (α (comma_right_ob Y) ^ id[K (F (comma_right_ob X))])).
  { rewrite <- exp_dimap_id_r, <- !exp_dimap_comp.
    rewrite !comp_id_l, !comp_id_r. reflexivity. }
  rewrite E.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (α (comma_right_ob Y) ^
    id[K (F (comma_right_ob X))])).
  rewrite gluing_change_exp_boundary.
  rewrite <- !comp_assoc, <- exp_dimap_comp,
    comp_id_l, (gluing_change_arrow H K α X).
  reflexivity.
Defined.

(** ** The Actual Cospan Transformation

    For fixed glued objects, extend the two commuting generating squares
    along the existing free cospan diagram. This retains the three maps
    above and uses the general naturality-on-paths construction. *)

(** ** 实际余跨度自然变换

    对固定粘合对象，沿既有自由余跨度图式延拓两个交换生成方形，保留上述
    三个映射，并复用一般的路径自然性构造。 *)

Definition GluingExpChangeN (X Y : Gluing F)
  : (K ∘F ⟨gluing_exp_result F X Y →←
        gluing_exp_base F source X Y⟩D) ⇒
      ⟨gluing_exp_result F'
          (GluingChangeF H K α X) (GluingChangeF H K α Y) →←
        gluing_exp_base F' interpretation
          (GluingChangeF H K α X) (GluingChangeF H K α Y)⟩D.
Proof.
  refine (@FreeN CospanGraph D'
    (K ∘F CospanDiagram (gluing_exp_result F X Y)
      (gluing_exp_base F source X Y))
    (CospanDiagram (gluing_exp_result F'
      (GluingChangeF H K α X) (GluingChangeF H K α Y))
      (gluing_exp_base F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y)))
    (λ v, match v as w return Hom
      (K (CospanDiagram (gluing_exp_result F X Y)
        (gluing_exp_base F source X Y) w))
      (CospanDiagram (gluing_exp_result F'
        (GluingChangeF H K α X) (GluingChangeF H K α Y))
        (gluing_exp_base F' interpretation
          (GluingChangeF H K α X) (GluingChangeF H K α Y)) w) with
    | cospan_left => gluing_change_exp_left X Y
    | cospan_right => gluing_change_exp_right X Y
    | cospan_tip => gluing_change_exp_tip X Y
    end) _).
  intros x y e. destruct x, y; destruct e.
  - exact (gluing_change_exp_result X Y).
  - exact (gluing_change_exp_base X Y).
Defined.

(** Only the three actual comparison maps must be invertible. No global
    exponential-preservation or natural-isomorphism class is selected. *)

(** 只要求三个实际比较映射可逆，不选择全局指数保持或自然同构类。 *)

Definition gluing_change_exp_cospan_iso (X Y : Gluing F)
    (left : is_iso (gluing_change_exp_left X Y))
    (right : is_iso (gluing_change_exp_right X Y))
    (tip : is_iso (gluing_change_exp_tip X Y))
  : GluingExpChangeN X Y ⦂ _ ≅N _.
Proof.
  intros v. destruct v; [exact left | exact right | exact tip].
Defined.

(** Local invertibility of the result boundary and the corresponding
    [K] comparison suffices for the common-target comparison. *)

(** 结果边界及对应 [K] 比较的局部可逆性足以使共同目标比较可逆。 *)

Definition gluing_change_exp_tip_iso (X Y : Gluing F)
    (boundary : is_iso (α (comma_right_ob Y)))
    (comparison : is_iso (exp_cmp K target
      (comma_left_ob X) (F (comma_right_ob Y))))
  : is_iso (gluing_change_exp_tip X Y)
  := is_iso_comp comparison (fct_is_iso (-^ K (comma_left_ob X))
      (α (comma_right_ob Y)) boundary).

(** On the right, use only the base comparison and the boundary at the
    original base exponential. Functors preserve their supplied inverses. *)

(** 右侧只使用基比较及原基指数处的边界；函子保持所给的逆。 *)

Definition gluing_change_exp_right_iso (X Y : Gluing F)
    (boundary : is_iso (α ((comma_right_ob Y ^ comma_right_ob X)%ob)))
    (comparison : is_iso (exp_cmp H base
      (comma_right_ob X) (comma_right_ob Y)))
  : is_iso (gluing_change_exp_right X Y)
  := is_iso_comp boundary (fct_is_iso F'
      (exp_cmp H base
        (comma_right_ob X) (comma_right_ob Y)) comparison).

(** ** Transport of a Supplied Image Pullback

    Fix a particular cone after [K]. Its image pullback property is an
    input, not inferred from product preservation. With the three local
    inverse witnesses, reuse pullbacks-as-limits and limit transport.
    No chosen family of pullbacks or new universal-property proof occurs. *)

(** ** 运输给定像拉回

    固定 [K] 之后的一个特定锥，其像拉回性质作为输入，不从积保持性推出。
    给出三个局部逆见证后，复用拉回作为极限及极限运输；不选择整族拉回，
    也不另证泛性质。 *)

Context (X Y : Gluing F) (E : D)
    (p : Hom E (comma_left_ob Y ^ comma_left_ob X))
    (q : Hom E (F ((comma_right_ob Y ^ comma_right_ob X)%ob))).

(** The transported vertex is [K E] and its legs use exactly the supplied
    comparison maps. The existence of the original pullback is not needed
    once this particular image cone is given as a pullback. *)

(** 运输后的顶点为 [K E]，锥腿恰使用所给比较映射；一旦指定这个像锥为
    拉回，就不再需要原拉回的存在性。 *)

Definition gluing_change_exp_pullback
    (image : is_pullback
      (fmap K (gluing_exp_result F X Y))
      (fmap K (gluing_exp_base F source X Y))
      (K E) (fmap K p) (fmap K q))
    (left : is_iso (gluing_change_exp_left X Y))
    (right : is_iso (gluing_change_exp_right X Y))
    (tip : is_iso (gluing_change_exp_tip X Y))
  : is_pullback (gluing_exp_result F'
        (GluingChangeF H K α X) (GluingChangeF H K α Y))
      (gluing_exp_base F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y))
      (K E) (gluing_change_exp_left X Y ∘ fmap K p)
      (gluing_change_exp_right X Y ∘ fmap K q).
Proof.
  pose (κ := @CospanConeOver D'
    (K ∘F CospanDiagram (gluing_exp_result F X Y)
      (gluing_exp_base F source X Y))
    (K E) (fmap K p) (fmap K q) (fst image)).
  exact (limit_pullback (GluingExpChangeN X Y ∘Nv κ)
    (limit_transport (GluingExpChangeN X Y)
      (gluing_change_exp_cospan_iso X Y left right tip)
      (pullback_limit κ image))).
Defined.

(** The transported pullback supplies an exponential of the actual changed
    objects via the existing Gluing theorem. Its base is [H B ^ H A].
    This candidate theorem does not yet identify the functor's image
    exponential, whose base is [H (B ^ A)], or its mapped evaluation. *)

(** 通过既有粘合定理，运输后的拉回给出实际变化后对象的指数，其基为
    [H B ^ H A]。此候选定理尚不识别函子的像指数（基为 [H (B ^ A)]）
    或其求值的像。 *)

Definition gluing_change_exp_universal
    (image : is_pullback
      (fmap K (gluing_exp_result F X Y))
      (fmap K (gluing_exp_base F source X Y))
      (K E) (fmap K p) (fmap K q))
    (left : is_iso (gluing_change_exp_left X Y))
    (right : is_iso (gluing_change_exp_right X Y))
    (tip : is_iso (gluing_change_exp_tip X Y))
  : @is_exp (Gluing F') (Gluing_HasProduct F' interpretation)
      (GluingChangeF H K α X) (GluingChangeF H K α Y)
      (GluingExp F' (GluingChangeF H K α X) (GluingChangeF H K α Y)
        (K E) (gluing_change_exp_right X Y ∘ fmap K q))
      (gluing_eval F' interpretation
        (GluingChangeF H K α X) (GluingChangeF H K α Y)
        (K E) (gluing_change_exp_left X Y ∘ fmap K p)
        (gluing_change_exp_right X Y ∘ fmap K q)
        (gluing_change_exp_pullback image left right tip))
  := gluing_exp_universal F' interpretation
      (GluingChangeF H K α X) (GluingChangeF H K α Y)
      (K E) (gluing_change_exp_left X Y ∘ fmap K p)
      (gluing_change_exp_right X Y ∘ fmap K q)
      (gluing_change_exp_pullback image left right tip).

End ExponentialCospanChange.
