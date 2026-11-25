From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Cat.CCC.Core
  Cat.CCC.Functor.

(** * Cartesian Closed Categories and Their Functors

    At each fixed universe profile, objects are complete CCC bundles and
    arrows preserve their selected finite products and exponentials up to
    the canonical isomorphisms. Arrow equality is natural isomorphism of
    the underlying functors, retaining its computational witnesses.
    This category lives at larger bounds than the categories it contains;
    it does not collect every universe in one small type. *)

(** * 笛卡尔闭范畴及其函子

    每组固定宇宙界内，对象为完整 CCC 结构包，态射通过规范同构保持其选定
    有限积及指数。态射相等为底层函子的自然同构，保留其计算见证。
    此范畴的大小界高于其对象范畴，不将全部宇宙收集到一个小类型中。 *)

(** Compare underlying functors without comparing preservation witnesses. *)

(** 比较底层函子，不比较保持性见证。 *)

Definition CCCFctEq {C D : CCC} (F G : CCCFct C D)
  : Type
  := (F : Fct C D) ≅N (G : Fct C D).

(** Natural-isomorphism equivalence restricts to the structured functors. *)

(** 自然同构的等价关系限制到保结构函子。 *)

Global Instance CCCFctEq_Equivalence {C D : CCC}
  : Equivalence (@CCCFctEq C D).
Proof.
  split; unfold CCCFctEq.
  - intro F. reflexivity.
  - intros F G H. symmetry. exact H.
  - intros F G H E K. transitivity (G : Fct C D); assumption.
Defined.

(** The hom-setoid retains the complete functor and its selected evidence. *)

(** Hom 广集保留完整函子及其选定证据。 *)

Canonical Structure CCCFctS (C D : CCC)
  : SetC
  :=
  {|carrier := CCCFct C D
  ; carrier_equiv := CCCFctEq
  ; carrier_setoid := CCCFctEq_Equivalence
  |}.

(** The category laws are the existing functor unit and associativity
    comparisons; they require no equality of object maps or proof fields. *)

(** 范畴律复用已有函子单位及结合比较，不要求对象映射或证明字段相等。 *)

Program Canonical CCCCat@{o h p l +}
  : Cat
  :=
  {|Ob := CCC@{o h p l l}
  ; HomSet := CCCFctS
  ; id := IdCCCF
  ; comp _ _ _ := CompCCCF
  |}.
Next Obligation.
  intros F F' HF G G' HG.
  exact (CompF_proper F F' HF G G' HG).
Defined.
Next Obligation. exact (CompF_id_r f). Defined.
Next Obligation. exact (CompF_id_l f). Defined.
Next Obligation. exact (CompF_assoc f g h). Defined.

(** This category of CCCs is an object of a larger [CatCat], itself an
    object of a still larger [CatCat]. Each right-associated annotation
    uses a fresh universe instance and the object-type coercion. *)

(** 此 CCC 组成的范畴是更大 [CatCat] 的对象，后者又是更大 [CatCat] 的对象；
    每个右结合的类型标注使用新的宇宙实例，并通过强制转换取得对象类型。 *)

Check CCCCat : CatCat : CatCat : CatCat.

(** Forget the chosen structures and preservation evidence, keeping the
    underlying category, functor and natural-isomorphism witnesses. *)

(** 忘掉选定结构及保持性证据，保留底层范畴、函子及自然同构见证。 *)

Program Definition CCCForgetF
  : Fct CCCCat CatCat
  :=
  {|fobj C := (C : Cat)
  ; fmap C D F := (F : Fct C D)
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros F G H. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Forgetting reflects the specified equality of CCC functors. *)

(** 忘却反映 CCC 函子的指定相等。 *)

Lemma ccc_forget_faithful
  : is_faithful CCCForgetF.
Proof. intros C D F G H. exact H. Defined.

(** Repackage a CCC functor at the hom-set's common proof bounds. Reuse
    [CatCatHom] for its ordinary functor, retaining the product witnesses
    and exponential inverses. Auxiliary proof bounds may be larger than
    the categories' law bounds; no resizing or equality of records is used. *)

(** 在 Hom 的共同证明界上重新组装 CCC 函子，普通函子复用 [CatCatHom]，
    保留积见证及指数的逆。辅助证明界可以高于范畴定律界，不使用大小重设，
    也不要求记录相等。 *)

Program Definition CCCCatHom@{o h p l m n +}
    {C D : CCC@{o h p l l}}
    (F : CCCFct@{l m n o h p l l o h p l} C D)
  : (@Hom CCCCat) C D
  := MakeCCCFct (CatCatHom (F : Fct C D))
      {|fct_terminal := @fct_terminal C D F
          (hasTerminal C) (hasProduct C) (isCartF (CCCFctToCartFct F))
      ; fct_product := @fct_product C D F
          (hasTerminal C) (hasProduct C) (isCartF (CCCFctToCartFct F))
      |}
    {|fct_exp := fct_exp (PreservesExp := CCCFct_preservesExp F)|}.
