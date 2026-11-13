From Cats Require Import
  Cat.Core
  Cat.Isomorphism
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Exponential.Functor
  Cat.Limit.Exponential.
From Cats Require Export
  Cat.Exponential.Core
  Cat.Exponential.Currying.

(** * Canonical Exponential Isomorphisms

    Fix selected binary products and exponentials. Construct canonical
    comparison isomorphisms and their evaluation diagrams; a selected
    terminal object is added only for the terminal and unit comparisons. *)

(** * 规范指数同构

    固定选定二元积与指数，构造规范比较同构及其求值图；仅在终对象及单位比较
    处增加选定终对象。 *)

Section ExponentialProducts.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Product preservation supplies this isomorphism and its inverse; the
    forward map pairs the exponentiated projections. *)

(** 积保持性给出此同构及其逆；正向映射配对取指数后的投影。 *)

Definition exponential_product_iso (A X Y : @Ob C)
  : ((X × Y) ^ A) ≅ ((X ^ A) × (Y ^ A))
  := product_unique (exponential_preserves_product A product_universal)
      product_universal.

(** The first projection of the comparison is the exponentiated projection. *)

(** 比较的第一投影为取指数后的投影。 *)

Lemma exponential_product_β1 (A X Y : @Ob C)
  : π1 ∘ (exponential_product_iso A X Y).1 ≈ fmap (-^ A) π1.
Proof. apply product_β1. Qed.

(** The second projection of the comparison is the exponentiated projection. *)

(** 比较的第二投影为取指数后的投影。 *)

Lemma exponential_product_β2 (A X Y : @Ob C)
  : π2 ∘ (exponential_product_iso A X Y).1 ≈ fmap (-^ A) π2.
Proof. apply product_β2. Qed.

(** Transposing a pair computes componentwise through the comparison. *)

(** 配对的转置通过比较逐分量计算。 *)

Lemma exponential_product_curry {A X Y Z : @Ob C}
    (f : Hom (Z × A) X) (g : Hom (Z × A) Y)
  : (exponential_product_iso A X Y).1 ∘ (ƛ ⟨f, g⟩) ≈ ⟨ƛ f, ƛ g⟩.
Proof.
  apply (product_cone_ext product_universal).
  - rewrite <- comp_assoc, exponential_product_β1.
    change (exponential_map π1 ∘ (ƛ ⟨f, g⟩) ≈ π1 ∘ ⟨ƛ f, ƛ g⟩).
    rewrite <- exponential_curry_comp_l, !product_β1. reflexivity.
  - rewrite <- comp_assoc, exponential_product_β2.
    change (exponential_map π2 ∘ (ƛ ⟨f, g⟩) ≈ π2 ∘ ⟨ƛ f, ƛ g⟩).
    rewrite <- exponential_curry_comp_l, !product_β2. reflexivity.
Qed.

(** Inverse comparison pairs functions by abstracting their evaluations. *)

(** 逆比较通过抽象两个函数的求值来配对函数。 *)

Lemma exponential_product_inv_curry {A X Y Z : @Ob C}
    (f : Hom Z (X ^ A)) (g : Hom Z (Y ^ A))
  : (exponential_product_iso A X Y).2.1 ∘ ⟨f, g⟩ ≈
      ƛ ⟨uncurry f, uncurry g⟩.
Proof.
  apply (iso_cancel_l (exponential_product_iso A X Y)).
  rewrite <- comp_assoc, (snd (exponential_product_iso A X Y).2.2),
    comp_id_l, exponential_product_curry, !exponential_η. reflexivity.
Qed.

(** The product-exponential inverse evaluates componentwise. *)

(** 积指数的逆映射逐分量求值。 *)

Lemma exponential_product_eval (A X Y : @Ob C)
  : uncurry (exponential_product_iso A X Y).2.1 ≈
      ⟨uncurry π1, uncurry π2⟩.
Proof.
  pose proof (exponential_product_inv_curry
    (π1 : Hom ((X ^ A) × (Y ^ A)) (X ^ A)) π2) as H.
  rewrite product_pair_η, comp_id_r in H.
  rewrite H, exponential_β. reflexivity.
Qed.

(** The inverse product-exponential comparison evaluates both internal
    functions at the same contextual argument, with the original chosen
    products and exponentials. *)

(** 积指数比较的逆在同一个上下文参数处求值两个内部函数，使用原有选定积与指数。 *)

Lemma exponential_product_app {W X Y Z : @Ob C}
    (u : Hom W ((Y ^ X) × (Z ^ X))) (a : Hom W X)
  : app ((exponential_product_iso X Y Z).2.1 ∘ u) a ≈
      ⟨app (π1 ∘ u) a, app (π2 ∘ u) a⟩.
Proof.
  pose proof (exponential_product_inv_curry (π1 ∘ u) (π2 ∘ u)) as H.
  rewrite <- product_comp_r, product_pair_η, comp_id_l in H.
  rewrite H, exponential_app_β. unfold uncurry, app.
  repeat first [rewrite comp_assoc | rewrite product_comp_r |
    rewrite product_comp_l | rewrite cross_η | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** The product comparison is natural in both result factors. *)

(** 积比较在两个结果因子上自然。 *)

Lemma exponential_product_natural (A : @Ob C) {X Y X' Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : (exponential_product_iso A X' Y').1 ∘ fmap (-^ A) (f × g) ≈
      (fmap (-^ A) f × fmap (-^ A) g) ∘
        (exponential_product_iso A X Y).1.
Proof.
  apply (product_cone_ext product_universal).
  - rewrite <- !comp_assoc, exponential_product_β1.
    rewrite (cross_η (fmap (-^ A) f) (fmap (-^ A) g)),
      product_β1, comp_assoc, (exponential_product_β1 A X Y).
    change (exponential_map (X := A) π1 ∘
      exponential_map (X := A) (f × g) ≈
      exponential_map (X := A) f ∘ exponential_map (X := A) π1).
    rewrite <- !exponential_map_comp, cross_η, product_β1. reflexivity.
  - rewrite <- !comp_assoc, exponential_product_β2.
    rewrite (cross_η (fmap (-^ A) f) (fmap (-^ A) g)),
      product_β2, comp_assoc, (exponential_product_β2 A X Y).
    change (exponential_map (X := A) π2 ∘
      exponential_map (X := A) (f × g) ≈
      exponential_map (X := A) g ∘ exponential_map (X := A) π2).
    rewrite <- !exponential_map_comp, cross_η, product_β2. reflexivity.
Qed.

(** The binary-product comparison as a natural transformation. *)

(** 将二元积比较组织为自然变换。 *)

Program Definition ExponentialProductN (A : @Ob C)
  : ((-^ A) ∘F ProductF) ⇒ (ProductF ∘F ((-^ A) ×F (-^ A)))
  :=
  {|nt XY := (exponential_product_iso A (fst XY) (snd XY)).1
  |}.
Next Obligation. destruct f as [f g]. apply exponential_product_natural. Qed.

(** Exponentiation distributes over products naturally in both factors. *)

(** 指数对积的分配在两个因子上自然。 *)

Definition exponential_product_nat_iso (A : @Ob C)
  : ((-^ A) ∘F ProductF) ≅N (ProductF ∘F ((-^ A) ×F (-^ A)))
  := (ExponentialProductN A;
      λ XY, (exponential_product_iso A (fst XY) (snd XY)).2).

Context `{HT : !HasTerminal C}.

(** Exponentiation into a terminal object is terminal, by limit preservation. *)

(** 指数进入终对象仍为终对象，来自极限保持性。 *)

Definition exponential_terminal_iso (A : @Ob C)
  : (1 ^ A) ≅ 1
  := terminal_unique (exponential_preserves_terminal A terminal_universal)
      terminal_universal.

(** Evaluate at the unique argument of the terminal object. *)

(** 在终对象的唯一参数处求值。 *)

Definition exponential_unit_eval (Y : @Ob C)
  : Hom (Y ^ 1) Y
  := app id !.

(** Evaluation at the terminal argument computes a transpose. *)

(** 在终参数处的求值计算转置。 *)

Lemma exponential_unit_eval_curry {Y Z : @Ob C} (f : Hom (Z × 1) Y)
  : exponential_unit_eval Y ∘ (ƛ f) ≈ f ∘ ⟨id, !⟩.
Proof.
  unfold exponential_unit_eval. rewrite exponential_app_comp, comp_id_l.
  rewrite (term_η (! ∘ (ƛ f))). apply exponential_app_β.
Qed.

(** Terminal-argument evaluation commutes with the selected internal pairing
    comparison. This is the product coherence needed to compare global values. *)

(** 终参数求值与选定内部配对比较交换，给出全局值比较所需的积相干。 *)

Lemma exponential_unit_product (Y Z : @Ob C)
  : exponential_unit_eval (Y × Z) ∘
      (exponential_product_iso 1 Y Z).2.1 ≈
      exponential_unit_eval Y × exponential_unit_eval Z.
Proof.
  unfold exponential_unit_eval.
  rewrite exponential_app_comp, comp_id_l, term_comp_l.
  rewrite <- (comp_id_r (exponential_product_iso 1 Y Z).2.1) at 1.
  rewrite exponential_product_app.
  repeat first [rewrite comp_assoc | rewrite exponential_app_comp |
    rewrite cross_η | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r | rewrite term_comp_l].
  reflexivity.
Qed.

(** Exponentiation by the terminal object is isomorphic to the result object.
    Both maps are explicit evaluation and abstraction. *)

(** 以终对象为指数同构于结果对象；两个映射为显式求值及抽象。 *)

Definition exponential_unit_iso (Y : @Ob C)
  : (Y ^ 1) ≅ Y.
Proof.
  exists (exponential_unit_eval Y), (ƛ π1).
  split; unfold is_linv_of, is_rinv_of.
  - apply exponential_ext.
    rewrite exponential_uncurry_comp_r, exponential_β.
    unfold uncurry, exponential_unit_eval, app.
    rewrite cross_η, comp_assoc, product_β1, product_comp_r, comp_id_l.
    assert (H : ! ∘ (π1 : Hom ((Y ^ 1) × 1) (Y ^ 1)) ≈ π2).
    { rewrite (term_η π2). apply term_comp_l. }
    rewrite H, product_pair_η, cross_id, !comp_id_r. reflexivity.
  - rewrite exponential_unit_eval_curry, product_β1. reflexivity.
Defined.

(** Evaluation at the terminal argument is natural in the result object. *)

(** 在终参数处的求值在结果对象上自然。 *)

Lemma exponential_unit_natural {X Y : @Ob C} (f : Hom X Y)
  : exponential_unit_eval Y ∘ fmap (-^ 1) f ≈ f ∘ exponential_unit_eval X.
Proof.
  unfold exponential_unit_eval, app.
  rewrite comp_assoc, product_comp_r, comp_id_l,
    (term_η (! ∘ fmap (-^ 1) f)).
  transitivity (uncurry (exponential_map (X := 1) f) ∘ ⟨id, !⟩).
  - unfold uncurry. rewrite comp_assoc, product_comp_l,
      comp_id_r, comp_id_l. reflexivity.
  - unfold exponential_map. rewrite exponential_β, comp_assoc. reflexivity.
Qed.

(** Evaluation at the terminal argument as a natural transformation. *)

(** 将终参数处的求值组织为自然变换。 *)

Program Definition ExponentialUnitN
  : (-^ 1) ⇒ (@IdF C)
  :=
  {|nt Y := exponential_unit_eval Y
  |}.
Next Obligation. apply exponential_unit_natural. Qed.

(** Exponentiation by the terminal object is naturally the identity. *)

(** 以终对象为指数自然同构于恒等函子。 *)

Definition exponential_unit_nat_iso
  : (-^ 1) ≅N (@IdF C)
  := (ExponentialUnitN; λ Y, (exponential_unit_iso Y).2).

End ExponentialProducts.
