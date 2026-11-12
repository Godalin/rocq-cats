From Cats Require Export
  Cat.Monoidal.Monoid.
From Cats Require Import
  Cat.Monoidal.Bifunctor
  Cat.Terminal
  Cat.Product.Transport.

Local Open Scope monoidal_scope.

(** * Cartesian Monoidal Structure

    Chosen binary products and a terminal object supply the tensor and
    unit. All comparisons are built from their universal properties;
    pentagon and triangle follow by comparing projections. *)

(** * 笛卡尔幺半结构

    选定二元积及终对象提供张量和单位。全部比较由其泛性质构造，五边形与三角形
    通过比较投影证明。 *)

Section Cartesian.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}.

(** Product reassociation is natural in the three factors. *)

(** 积的括号重排在三个因子上自然。 *)

Program Definition CartesianAssociatorN
  : TensorLeftF ProductF ⇒ TensorRightF ProductF
  :=
  {|nt '((X, Y), Z) := (@product_assoc C HP X Y Z).1
  |}.
Next Obligation.
  destruct X as [[A B] D], Y as [[A' B'] D'], f as [[a b] d]. cbn.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2].
  reflexivity.
Defined.

(** Projection from a product with the terminal object on the left. *)

(** 从左侧带终对象的积取投影。 *)

Program Definition CartesianLeftUnitorN
  : π2F ProductF 1 ⇒ IdF
  :=
  {|nt X := π2
  |}.
Next Obligation.
  rewrite cross_η, product_β2. reflexivity.
Defined.

(** Projection from a product with the terminal object on the right. *)

(** 从右侧带终对象的积取投影。 *)

Program Definition CartesianRightUnitorN
  : π1F ProductF 1 ⇒ IdF
  :=
  {|nt X := π1
  |}.
Next Obligation.
  rewrite cross_η, product_β1. reflexivity.
Defined.

(** The inverse left unitor pairs the terminal arrow and identity.
    This witness remains transparent, including in concrete models. *)

(** 左单位子的逆将终箭头与恒等配对；这个见证保持透明，也适用于具体模型计算。 *)

Definition CartesianLeftUnitorIso
  : π2F ProductF 1 ≅N IdF.
Proof.
  exists CartesianLeftUnitorN. intros X. exists ⟨!, id⟩. split.
  - change ((⟨!, id⟩ : Hom X (1 × X)) ∘ π2 ≈ id).
    rewrite product_comp_r, comp_id_l. symmetry.
    apply product_pair_unique. split.
    + transitivity (! : Hom (1 × X) 1);
        [apply term_η | symmetry; apply term_η].
    + apply comp_id_r.
  - apply product_β2.
Defined.

(** The inverse right unitor pairs identity and the terminal arrow. *)

(** 右单位子的逆将恒等与终箭头配对。 *)

Definition CartesianRightUnitorIso
  : π1F ProductF 1 ≅N IdF.
Proof.
  exists CartesianRightUnitorN. intros X. exists ⟨id, !⟩. split.
  - change ((⟨id, !⟩ : Hom X (X × 1)) ∘ π1 ≈ id).
    rewrite product_comp_r, comp_id_l. symmetry.
    apply product_pair_unique. split.
    + apply comp_id_r.
    + transitivity (! : Hom (X × 1) 1);
        [apply term_η | symmetry; apply term_η].
  - apply product_β1.
Defined.

(** Finite products define a chosen monoidal structure. Importing this
    module does not register a default monoidal structure on [C]. *)

(** 有限积给出选定幺半结构；导入本模块不会为 [C] 注册默认幺半结构。 *)

Program Definition CartesianMonoidal
  : MonoidalCat C
  := BifunctorMonoidal ProductF 1
    (CartesianAssociatorN;
      λ '((X, Y), Z), (@product_assoc C HP X Y Z).2)
    CartesianLeftUnitorIso CartesianRightUnitorIso _ _.
Next Obligation.
  cbn. repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r].
  reflexivity.
Defined.
Next Obligation.
  cbn. repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r].
  reflexivity.
Defined.

(** The derived tensor action agrees with the selected product bimap. *)

(** 导出的张量作用与选定积的二元映射相等。 *)

Lemma cartesian_tensor_map {X X' Y Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : @tensor_map C CartesianMonoidal X X' Y Y' f g ≈ f × g.
Proof. apply bifunctor_monoidal_map. Qed.

(** Internal monoids for finite products are a specialization of the same
    monoid-object definition. Their multiplication has type [M × M → M]
    and their unit has type [1 → M]. *)

(** 有限积中的内部幺半群是同一个幺半群对象定义的特化，乘法类型为 [M × M → M]，
    单位类型为 [1 → M]。 *)

Definition CartesianMonoid
  : Type
  := MonoidObject CartesianMonoidal.

(** In the familiar internal-monoid form, pairing with the unit on the
    left followed by multiplication is the identity. *)

(** 在通常的内部幺半群形式下，先在左侧与单位配对，再乘法，得到恒等。 *)

Lemma cartesian_monoid_unit_l (A : CartesianMonoid)
  : m[A] ∘ ⟨e[A] ∘ !, id⟩ ≈ id.
Proof.
  pose proof (monoid_object_unit_l A) as H.
  rewrite cartesian_tensor_map in H.
  change (m[A] ∘ (e[A] × id) ≈ π2) in H.
  transitivity ((m[A] ∘ (e[A] × id)) ∘
    (⟨!, id⟩ : Hom (MonoidCarrier A) (1 × MonoidCarrier A))).
  - symmetry. rewrite comp_assoc.
    apply comp_proper; [reflexivity |].
    etransitivity.
    + exact (product_comp_l (! : Hom (MonoidCarrier A) 1)
        (@id (MonoidCarrier A)) e[A] (@id (MonoidCarrier A))).
    + rewrite comp_id_l. reflexivity.
  - rewrite H. apply product_β2.
Qed.

(** The corresponding right unit equation uses the same chosen structure. *)

(** 右单位方程使用同一个选定结构。 *)

Lemma cartesian_monoid_unit_r (A : CartesianMonoid)
  : m[A] ∘ ⟨id, e[A] ∘ !⟩ ≈ id.
Proof.
  pose proof (monoid_object_unit_r A) as H.
  rewrite cartesian_tensor_map in H.
  change (m[A] ∘ (id × e[A]) ≈ π1) in H.
  transitivity ((m[A] ∘ (id × e[A])) ∘
    (⟨id, !⟩ : Hom (MonoidCarrier A) (MonoidCarrier A × 1))).
  - symmetry. rewrite comp_assoc.
    apply comp_proper; [reflexivity |].
    etransitivity.
    + exact (product_comp_l (@id (MonoidCarrier A))
        (! : Hom (MonoidCarrier A) 1) (@id (MonoidCarrier A)) e[A]).
    + rewrite comp_id_l. reflexivity.
  - rewrite H. apply product_β1.
Qed.

(** Associativity uses the canonical reassociation of chosen products. *)

(** 结合律使用选定积的规范括号重排。 *)

Lemma cartesian_monoid_assoc (A : CartesianMonoid)
  : m[A] ∘ (m[A] × id) ≈ m[A] ∘ (id × m[A]) ∘
      (@product_assoc C HP
        (MonoidCarrier A) (MonoidCarrier A) (MonoidCarrier A)).1.
Proof.
  pose proof (monoid_object_assoc A) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

End Cartesian.
