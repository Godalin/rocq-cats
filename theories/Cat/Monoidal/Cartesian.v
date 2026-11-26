From Cats Require Export
  Cat.Terminal
  Cat.Product.Core
  Cat.Monoidal.Monoid
  Cat.Monoidal.Lifting
  Cat.Monoidal.Strength
  Cat.Monoidal.Symmetric.
From Cats Require Import
  Cat.Monoidal.Bifct
  Cat.Product.Transport.

Local Open Scope monoidal_scope.

(** * Cartesian Monoidal Structure

    Chosen binary products and a terminal object supply the tensor and
    unit. All comparisons are built from their universal properties;
    pentagon and triangle follow by comparing projections. *)

(** * 笛卡尔幺半结构

    选定二元积及终对象提供张量和单位。全部比较由其泛性质构造，五边形与三角形
    通过比较投影证明。 *)

Section ProductTensor.
Context {C : Cat}
  `{HT : !HasTerminal C} `{HP : !HasProduct C}.

(** Product reassociation is natural in the three factors. *)

(** 积的括号重排在三个因子上自然。 *)

Program Definition CartAssociatorN
  : Tensor3LF ProductF ⇒ Tensor3RF ProductF
  :=
  {|nt '((X, Y), Z)
    := (@product_assoc C HP X Y Z).1
  |}.
Next Obligation.
  destruct X as [[A B] D], Y as [[A' B'] D'],
    f as [[a b] d]. cbn.
  repeat first [rewrite cross_η
    | rewrite product_comp_r | rewrite comp_assoc
    | rewrite product_β1 | rewrite product_β2].
  reflexivity.
Qed.

(** Projection from a product with the terminal object on the left. *)

(** 从左侧带终对象的积取投影。 *)

Program Definition CartUnitorLN
  : (1 ×-) ⇒ IdF
  :=
  {|nt X := π2
  |}.
Next Obligation.
  rewrite cross_η, product_β2. reflexivity.
Qed.

(** Projection from a product with the terminal object on the right. *)

(** 从右侧带终对象的积取投影。 *)

Program Definition CartUnitorRN
  : (-× 1) ⇒ IdF
  :=
  {|nt X := π1
  |}.
Next Obligation.
  rewrite cross_η, product_β1. reflexivity.
Qed.

(** The inverse left unitor pairs the terminal arrow and identity.
    This witness remains transparent, including in concrete models. *)

(** 左单位子的逆将终箭头与恒等配对；这个见证保持透明，也适用于具体模型计算。 *)

Definition CartUnitorLIso
  : (1 ×-) ≅N IdF.
Proof.
  exists CartUnitorLN. intros X.
  exists ⟨!, id⟩. split.
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

Definition CartUnitorRIso
  : (-× 1) ≅N IdF.
Proof.
  exists CartUnitorRN. intros X.
  exists ⟨id, !⟩. split.
  - change ((⟨id, !⟩ : Hom X (X × 1)) ∘ π1 ≈ id).
    rewrite product_comp_r, comp_id_l. symmetry.
    apply product_pair_unique. split.
    + apply comp_id_r.
    + transitivity (! : Hom (X × 1) 1);
        [apply term_η | symmetry; apply term_η].
  - apply product_β1.
Defined.

(** Pack the chosen finite products and terminal object as a monoidal
    category. *)

(** 将选定的有限积及终对象打包为幺半范畴。 *)

Program Definition CartMonoidal
  : MonoidalCat
  := BifctMonoidal ProductF 1
    (CartAssociatorN;
      λ '((X, Y), Z), (@product_assoc C HP X Y Z).2)
    CartUnitorLIso CartUnitorRIso _ _.
Next Obligation.
  unfold is_tensor_pentagon. intros W X Y Z. cbn.
  repeat first [rewrite cross_η | rewrite product_comp_r
    | rewrite comp_assoc | rewrite product_β1
    | rewrite product_β2 | rewrite comp_id_l
    | rewrite comp_id_r].
  reflexivity.
Qed.
Next Obligation.
  cbn. repeat first [rewrite cross_η
    | rewrite product_comp_r | rewrite comp_assoc
    | rewrite product_β1 | rewrite product_β2
    | rewrite comp_id_l | rewrite comp_id_r].
  reflexivity.
Qed.

(** Chosen finite products supply the cartesian monoidal structure on [C]. *)

(** 由 [C] 上选定的终对象和二元积推断笛卡尔幺半结构。 *)

Global Instance CartHasMonoidal
  : HasMonoidal C
  := MonoidalCatToHasMonoidal CartMonoidal.

(** The derived tensor action agrees with the selected product bimap. *)

(** 导出的张量作用与选定积的二元映射相等。 *)

Lemma cartesian_tensor_map {X X' Y Y' : C}
    (f : Hom X X') (g : Hom Y Y')
  : tensor_map f g
    ≈ f × g.
Proof. apply bifct_sequence. Qed.

(** Internal monoids for finite products are a specialization of the same
    monoid-object definition. Their multiplication has type [M × M → M]
    and their unit has type [1 → M]. *)

(** 有限积中的内部幺半群是同一个幺半群对象定义的特化，乘法类型为 [M × M → M]，
    单位类型为 [1 → M]。 *)

Definition CartMonoid
  : Type
  := MonoidObj C.

(** In the familiar internal-monoid form, pairing with the unit on the
    left followed by multiplication is the identity. *)

(** 在通常的内部幺半群形式下，先在左侧与单位配对，再乘法，得到恒等。 *)

Lemma cartesian_monoid_unit_l (A : CartMonoid)
  : m[A] ∘ ⟨e[A] ∘ !, id⟩ ≈ id.
Proof.
  pose proof (monoid_obj_unit_l (isMonoidObj A)) as H.
  rewrite cartesian_tensor_map in H.
  change (m[A] ∘ (e[A] × id) ≈ π2) in H.
  transitivity ((m[A] ∘ (e[A] × id)) ∘
    (⟨!, id⟩ : Hom A (1 × A))).
  - symmetry. rewrite comp_assoc.
    apply comp_proper; [reflexivity |].
    etransitivity.
    + exact (product_comp_l (! : Hom A 1) id[A] e[A] id[A]).
    + rewrite comp_id_l. reflexivity.
  - rewrite H. apply product_β2.
Qed.

(** The corresponding right unit equation uses the same chosen structure. *)

(** 右单位方程使用同一个选定结构。 *)

Lemma cartesian_monoid_unit_r (A : CartMonoid)
  : m[A] ∘ ⟨id, e[A] ∘ !⟩ ≈ id.
Proof.
  pose proof (monoid_obj_unit_r (isMonoidObj A)) as H.
  rewrite cartesian_tensor_map in H.
  change (m[A] ∘ (id × e[A]) ≈ π1) in H.
  transitivity ((m[A] ∘ (id × e[A])) ∘
    (⟨id, !⟩ : Hom A (A × 1))).
  - symmetry. rewrite comp_assoc.
    apply comp_proper; [reflexivity |].
    etransitivity.
    + exact (product_comp_l id[A] (! : Hom A 1) id[A] e[A]).
    + rewrite comp_id_l. reflexivity.
  - rewrite H. apply product_β1.
Qed.

(** Associativity uses the canonical reassociation of chosen products. *)

(** 结合律使用选定积的规范括号重排。 *)

Lemma cartesian_monoid_assoc (A : CartMonoid)
  : m[A] ∘ (m[A] × id) ≈ m[A] ∘ (id × m[A]) ∘
      (@product_assoc C HP A A A).1.
Proof.
  pose proof (monoid_obj_assoc (isMonoidObj A)) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** ** Cartesian Exchange

    Finite products extend their existing monoidal structure by canonical
    exchange. Only the new symmetry laws are proved here; all premonoidal
    data and coherence are inherited from the same cartesian parent. *)

(** ** 笛卡尔交换

    有限积通过规范交换扩展其已有幺半结构。此处仅证明新增对称定律，全部
    预幺半数据与相干性都继承自同一笛卡尔父结构。 *)

(** Canonical product exchange supplies an explicit symmetric structure.
    Importing this module selects no default structure on [C]. *)

(** 规范积交换给出显式对称结构；导入本模块不会为 [C] 选定默认结构。 *)

Program Definition CartHasTensorSym
  : HasTensorSym C
  :=
  {|tensor_sym X Y := ⟨π2, π1⟩
  ; tensor_sym_central X Y := tensor_arrow_central _
  |}.
Next Obligation.
  rewrite product_comp_r, product_β1, product_β2.
  apply product_pair_η.
Qed.
Next Obligation.
  change (⟨π2, π1⟩ ∘ (f × id[Y])
    ≈ (id[Y] × f) ∘ ⟨π2, π1⟩).
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** The cartesian exchange and product associator satisfy the hexagon. *)

(** 笛卡尔交换与积结合子满足六边形。 *)

Program Definition CartIsSymHexagon
  : @IsSymHexagon C _ CartHasTensorSym _
  :=
  {|tensor_sym_hexagon := _|}.
Next Obligation.
  change ((@product_assoc C HP Y Z X).1 ∘
    (⟨π2, π1⟩ ∘ (@product_assoc C HP X Y Z).1) ≈
    (id[Y] × ⟨π2, π1⟩) ∘
      ((@product_assoc C HP Y X Z).1 ∘ (⟨π2, π1⟩ × id[Z]))).
  unfold product_assoc. cbn.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** The cartesian exchange interchanges the two unitors. *)

(** 笛卡尔交换互换两个单位子。 *)

Program Definition CartIsSymUnit
  : @IsSymUnit C _ CartHasTensorSym _
  :=
  {|tensor_sym_unit := _|}.
Next Obligation. apply product_β2. Qed.

(** Finite products give a symmetric monoidal tensor with product swap. *)

(** 有限积给出对称幺半张量，其对称子交换两个积投影。 *)

Definition CartSymMonoidal
  : SymMonoidalCat
  := SymMonoidalCatOfMonoidalCat CartMonoidal
       CartHasTensorSym CartIsSymHexagon CartIsSymUnit.

(** Pack the exchange with the premonoidal view of the same finite products. *)

(** 将交换与同一份有限积的预幺半视图打包。 *)

Definition CartSymPremonoidal
  : SymPremonoidalCat
  := SymMonoidalCatToSymPremonoidalCat CartSymMonoidal.

End ProductTensor.

(** ** Cartesian Strength and Context Projection *)

(** ** 笛卡尔强度与上下文投影 *)

(** Discarding the ordinary context after strength preserves the effectful
    input. This follows from naturality into the terminal context and the
    strength unit law, without assuming the functor preserves products. *)

(** 强度之后丢弃通常上下文，保留带效应输入。这来自到终上下文的自然性及强度
    单位律，不假定函子保持积。 *)

Lemma cartesian_strength_projection {C : Cat}
    `{HT : !HasTerminal C} `{HP : !HasProduct C}
    {F : Fct C C} (S : HasStrength F)
    (X Y : C)
  : fmap F (π2 : Hom (X × Y) Y) ∘ st[X; Y] ≈ π2.
Proof.
  pose proof (strength_natural (! : Hom X 1) (id[Y])) as H.
  rewrite !cartesian_tensor_map in H.
  change (st[1; Y] ∘ (! × fmap F (id[Y]))
    ≈ fmap F (! × id[Y]) ∘ st[X; Y]) in H.
  rewrite fmap_id in H.
  transitivity ((fmap F (π2 : Hom (1 × Y) Y) ∘ st[1; Y]) ∘
    ((! : Hom X 1) × id[F Y])).
  - rewrite comp_assoc, H, <- comp_assoc, <- fmap_comp,
      cross_η, product_β2, comp_id_l. reflexivity.
  - rewrite (strength_unit S Y). cbn.
    rewrite cross_η, product_β2, comp_id_l.
    reflexivity.
Qed.

(** ** Cartesian Binary Lifting

    Transport generic lax lifting laws along the comparison between the
    derived tensor action and the selected product map. No pure map,
    exponentials or strength are needed. *)

(** ** 笛卡尔二元提升

    沿导出张量作用与选定积映射的比较运输一般 lax 提升定律。不要求纯值映射、
    指数或强度。 *)

Section Lifting.
Context {C D : Cat}
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{TD : !HasTerminal D} `{PD : !HasProduct D}
    (L : LaxMonoidalFct C D).

(** Naturality at the ordinary product maps of both categories. *)

(** 关于两个范畴中通常积映射的自然性。 *)

Lemma cartesian_lift2_pre {X Y X' Y' Z : C}
    (f : Hom (X' × Y') Z)
    (g : Hom X X') (h : Hom Y Y')
  : lift₂[L; f] ∘ (fmap L g × fmap L h)
    ≈ lift₂[L; f ∘ (g × h)].
Proof.
  pose proof (lax_lift2_pre L f g h) as H.
  rewrite !cartesian_tensor_map in H. exact H.
Qed.

(** A product associativity diagram lifts through the same lax structure. *)

(** 积的结合图通过同一个 lax 结构提升。 *)

Lemma cartesian_lift2_assoc {X Y Z U V T : C}
    (f : Hom (X × Y) U) (g : Hom (U × Z) T)
    (h : Hom (Y × Z) V) (k : Hom (X × V) T)
    (H : g ∘ (f × id)
      ≈ k ∘ (id × h) ∘ product_assoc.1)
  : lift₂[L; g] ∘ (lift₂[L; f] × id)
    ≈ lift₂[L; k] ∘ (id × lift₂[L; h]) ∘ product_assoc.1.
Proof.
  assert (K : g ∘ tensor_map f id
    ≈ k ∘ tensor_map id h ∘ α[X; Y; Z]).
  { rewrite !cartesian_tensor_map.
    exact H. }
  pose proof (lax_lift2_assoc L f g h k K) as E.
  rewrite !cartesian_tensor_map in E. exact E.
Qed.

End Lifting.
