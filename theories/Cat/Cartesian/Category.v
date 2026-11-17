From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Componentwise
  Cat.Functor.Core
  Cat.Functor.Cartesian
  Cat.Functor.Product
  Cat.Functor.Codiscrete
  Cat.Diagram.Core
  Cat.Natural
  Cat.Cartesian.Core
  Cat.Cartesian.Construction.

(** * Cartesian Categories as a Cartesian Category

    Objects are complete cartesian categories. Arrows preserve finite
    products, and equality retains natural-isomorphism witnesses. The
    terminal category and componentwise products give chosen finite products
    on this category itself. *)

(** * 笛卡尔范畴组成的笛卡尔范畴

    对象为完整笛卡尔范畴，态射保持有限积，相等保留自然同构见证。
    平凡终范畴及逐分量乘积为这个范畴自身提供选定有限积。 *)

(** Keep the original structured functor and compare its underlying functor. *)

(** 保留原保结构函子，比较其底层函子。 *)

Program Canonical CartFctS (C D : CartCat)
  : SetC
  :=
  {|carrier := @CartFct C D (hasTerminal C) (hasProduct C)
  ; carrier_equiv F G := (F : Fct C D) ≅N (G : Fct C D)
  |}.
Next Obligation.
  split.
  - intro F. reflexivity.
  - intros F G H. symmetry. exact H.
  - intros F G H E K. transitivity (G : Fct C D); assumption.
Defined.

(** Reuse cartesian identity and composition and the ordinary functor laws. *)

(** 复用笛卡尔恒等与复合，以及普通函子定律。 *)

Program Canonical CartCatCat@{o h p l +}
  : Cat
  :=
  {|Ob := CartCat@{l o h p l}
  ; HomSet := CartFctS
  ; id C := IdCartF C (hasTerminal C) (hasProduct C)
  ; comp C D E G F := CompCartF G F
  |}.
Next Obligation.
  intros F F' HF G G' HG. exact (CompF_proper F F' HF G G' HG).
Defined.
Next Obligation. exact (CompF_id_r f). Defined.
Next Obligation. exact (CompF_id_l f). Defined.
Next Obligation. exact (CompF_assoc f g h). Defined.

(** The one-point cartesian category inhabits each chosen universe profile. *)

(** 单点笛卡尔范畴属于每组选定宇宙配置。 *)

Definition TerminalCart@{o h p l}
  : CartCat@{l o h p l}
  := CodiscreteCart@{o h p l} unit tt.

(** The unique functor to the terminal cartesian category preserves products. *)

(** 到平凡终笛卡尔范畴的唯一函子保持积。 *)

Program Definition TerminalCartF@{o h p l +} (C : CartCat@{l o h p l})
  : CartFctS C TerminalCart@{o h p l}
  :=
  {|CartFctToFct := ConstF C (C := TerminalCart@{o h p l}) tt
  ; isCartF :=
    {|fct_terminal := @terminal_universal TerminalCart@{o h p l}
        (hasTerminal TerminalCart@{o h p l})
    ; fct_product X Y := @product_universal TerminalCart@{o h p l}
        (hasProduct TerminalCart@{o h p l}) tt tt
    |}
  |}.

(** Each product projection preserves its component's chosen finite products. *)

(** 每个乘积投影保持对应分量的选定有限积。 *)

Program Definition FstCartF (C D : CartCat)
  : CartFctS (ProdCart C D) C
  :=
  {|CartFctToFct := FstF C D
  ; isCartF :=
    {|fct_terminal := @terminal_universal C (hasTerminal C)
    ; fct_product X Y := @product_universal C (hasProduct C)
        (fst X) (fst Y)
    |}
  |}.

(** The second projection uses the same componentwise construction. *)

(** 第二投影使用同一个逐分量构造。 *)

Program Definition SndCartF (C D : CartCat)
  : CartFctS (ProdCart C D) D
  :=
  {|CartFctToFct := SndF C D
  ; isCartF :=
    {|fct_terminal := @terminal_universal D (hasTerminal D)
    ; fct_product X Y := @product_universal D (hasProduct D)
        (snd X) (snd Y)
    |}
  |}.

(** Pair preservation witnesses using the general product-cone theorem. *)

(** 使用一般积锥定理配对保持性见证。 *)

Program Definition PairCartF {S C D : CartCat}
    (F : CartFctS S C) (G : CartFctS S D)
  : CartFctS S (ProdCart C D)
  :=
  {|CartFctToFct := PairF F G
  ; isCartF :=
    {|fct_terminal := prod_is_terminal
        (@fct_terminal S C F (hasTerminal S) (hasProduct S)
          (isCartF F))
        (@fct_terminal S D G (hasTerminal S) (hasProduct S)
          (isCartF G))
    ; fct_product X Y := prod_is_product
        (@fct_product S C F (hasTerminal S) (hasProduct S)
          (isCartF F) X Y)
        (@fct_product S D G (hasTerminal S) (hasProduct S)
          (isCartF G) X Y)
    |}
  |}.

(** The single-point category is terminal up to natural isomorphism. *)

(** 单点范畴在自然同构下为终对象。 *)

Program Definition CartCatCat_HasTerminal@{o h p l +}
  : HasTerminal CartCatCat
  :=
  {|Term := TerminalCart@{o h p l}
  |}.
Next Obligation.
  intro C. exists (TerminalCartF C). split; [exact I |]. intros F _.
  exact (CodiscreteNatIso (F : Fct C TerminalCart@{o h p l})
    (TerminalCartF C)).
Defined.

(** Pairing is the product mediator; uniqueness uses its two projections. *)

(** 配对为积中介，唯一性由两个投影给出。 *)

Program Definition CartCatCat_HasProduct
  : HasProduct CartCatCat
  :=
  {|Prod := ProdCart
  ; π1 := FstCartF
  ; π2 := SndCartF
  |}.
Next Obligation.
  intros S F G. exists (PairCartF F G). split.
  - split; [exact (FstPairIso F G) | exact (SndPairIso F G)].
  - intros K [H1 H2].
    apply ProdNatIso.
    + transitivity (F : Fct S X).
      * exact H1.
      * symmetry. exact (FstPairIso F G).
    + transitivity (G : Fct S Y).
      * exact H2.
      * symmetry. exact (SndPairIso F G).
Defined.

(** A complete cartesian category whose objects are smaller cartesian
    categories. Its stored category and universal choices occur once. *)

(** 对象为较小笛卡尔范畴的完整笛卡尔范畴；底层范畴及泛性质选择均仅保存一次。 *)

Definition CartCatCartCat
  : CartCat
  := CartCatOfCat CartCatCat CartCatCat_HasTerminal CartCatCat_HasProduct.

(** Smaller instances are objects of larger ones. Each right-associated
    annotation uses a fresh universe instance and the object-type coercion. *)

(** 较小实例是较大实例的对象；每个右结合的类型标注使用新的宇宙实例，
    并通过强制转换取得对象类型。 *)

Check CartCatCartCat : CartCatCartCat : CartCatCartCat : CartCatCartCat.
