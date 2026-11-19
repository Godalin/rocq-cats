From Cats Require Export
  Cat.Coend.Core.
From Cats Require Import
  Cat.Core
  Cat.End.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Product.

(** * The Covariant Co-Yoneda Coend

    For a setoid-valued functor, pair a value with a raised arrow to the
    evaluation object. Evaluation itself is a universal cowedge, regardless
    of the object-index size. Hom carriers and equality must fit their
    respective value bounds; no order between those bounds is imposed. *)

(** * 协变 co-Yoneda Coend

    对广集值函子，将值与通往求值对象的提升箭头配对。求值本身就是泛余楔，不受
    对象指标大小限制。Hom 载体和相等须分别容纳于对应值界，不要求两值界间有次序。 *)

(** The covariant value is first and the contravariant Hom weight second.
    The data retain the supplied functor's independent auxiliary law bounds. *)

(** 协变值在前，反变 Hom 权重在后；数据保留给定函子的独立辅助定律界。 *)

Program Definition CoyonedaKernel@{u p a b +} {C : Cat}
    (F : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _}))
    (Z : @Ob C)
  : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})
  :=
  {|F0 AB := F (snd AB) ×S LiftS (@HomSet C (fst AB) Z)
  ; F1 AB AB' fg :=
      {|func w := (fmap F (snd fg) (fst w),
          {|lower := lower (snd w) ∘ fst fg|})
      |}
  |}.
Next Obligation.
  intros [x h] [y k] [Hx Hh]. split.
  - exact (@func_proper _ _ (fmap F (snd fg)) x y Hx).
  - refine {|lower := _|}. apply comp_proper; [exact (lower Hh) | reflexivity].
Defined.
Next Obligation.
  intros [f g] [f' g'] [H K] [x h]. split.
  - exact (@fct_fmap_proper C SetCat F _ _ g g' K x).
  - refine {|lower := _|}. apply comp_proper; [reflexivity | exact H].
Defined.
Next Obligation.
  intros [x h]. split.
  - exact (@fct_id C SetCat F _ x).
  - exact {|lower := comp_id_r (lower h)|}.
Defined.
Next Obligation.
  intros [x h]. split.
  - exact (@fct_comp C SetCat F _ _ _ (snd f) (snd g) x).
  - refine {|lower := _|}. symmetry. apply comp_assoc.
Defined.

(** ** Evaluation and Its Universal Property

    Fix the functor, its independent value levels and the evaluation object.
    Every balanced operation factors through evaluation by insertion of the
    identity arrow. This proves existence for this particular kernel without
    a general chosen-coend or small-index assumption. *)

(** ** 求值及其泛性质

    固定函子、独立值层级及求值对象。每个平衡操作通过插入恒等箭头分解为求值之后
    的操作，从而证明这个特殊核的存在，不要求一般选定 coend 或小指标假设。 *)

Section Evaluation.
Universes u p a b.
Context {C : Cat}.
Context (F : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _}))
    (Z : @Ob C).

(** Evaluate a value along its represented arrow. *)

(** 沿所表示的箭头求值一个值。 *)

Program Definition coyoneda_eval (Y : @Ob C)
  : CoyonedaKernel F Z (Y,Y) →r F Z
  :=
  {|func w := fmap F (lower (snd w)) (fst w)
  |}.
Next Obligation.
  intros [x h] [y k] [Hx Hh].
  transitivity (fmap F (lower k) x).
  - exact (@fct_fmap_proper C SetCat F _ _ _ _ (lower Hh) x).
  - exact (@func_proper _ _ (fmap F (lower k)) x y Hx).
Defined.

(** Evaluation balances arrow substitution in the two coordinates. *)

(** 求值使两个坐标上的箭头代入平衡。 *)

Program Definition CoyonedaCowedge
  : Cowedge (CoyonedaKernel F Z) (F Z)
  := CowedgeOf (D := SetCat) (coyoneda_eval) _.
Next Obligation.
  intros [x [h]].
  change (fmap F (h ∘ f) (fmap F (id[X]) x) ≈S
    fmap F (h ∘ (id[Y])) (fmap F f x)).
  transitivity (fmap F (h ∘ f) x).
  - exact (@func_proper _ _ (fmap F (h ∘ f)) _ _
      (@fct_id C SetCat F X x)).
  - transitivity (fmap F h (fmap F f x)).
    + exact (@fct_comp C SetCat F X Y Z h f x).
    + symmetry. exact (@fct_fmap_proper C SetCat F Y Z _ _
        (comp_id_r h) (fmap F f x)).
Defined.

(** Insert the identity as a transparent respectful seed. *)

(** 将恒等作为透明尊重种子插入。 *)

Program Definition coyoneda_seed
  : F Z →r CoyonedaKernel F Z (Z,Z)
  :=
  {|func x := (x,{|lower := id[Z]|})
  |}.
Next Obligation.
  intros x y H. split; [exact H | exact {|lower := reflexivity (id[Z])|}].
Defined.

(** Every cowedge value is determined by its identity component. *)

(** 每个余楔值由其恒等分量确定。 *)

Lemma coyoneda_cowedge_factor {W : SetC}
    (κ : Cowedge (CoyonedaKernel F Z) W) (Y : @Ob C)
    (x : F Y) (h : Hom Y Z)
  : κ Z (coyoneda_seed (fmap F h x)) ≈S κ Y (x,{|lower := h|}).
Proof.
  transitivity (κ Z (fmap F h x,{|lower := (id[Z]) ∘ (id[Z])|})).
  - apply (@func_proper _ _ (κ Z)). split; [reflexivity |].
    refine {|lower := _|}. symmetry. apply comp_id_l.
  - transitivity (κ Y (fmap F (id[Y]) x,{|lower := (id[Z]) ∘ h|})).
    + symmetry. exact (cowedge_comm κ h (x,{|lower := id[Z]|})).
    + apply (@func_proper _ _ (κ Y)). split.
      * exact (@fct_id C SetCat F Y x).
      * exact {|lower := comp_id_l h|}.
Defined.

(** Any balanced operation extends by its identity component. *)

(** 任意平衡操作通过其恒等分量延拓。 *)

Definition coyoneda_desc {W : SetC} (κ : Cowedge (CoyonedaKernel F Z) W)
  : F Z →r W
  := κ Z ∘r coyoneda_seed.

(** The extension computes on evaluation of any generator. *)

(** 延拓在任意生成元求值上计算为原操作。 *)

Lemma coyoneda_desc_β {W : SetC} (κ : Cowedge (CoyonedaKernel F Z) W)
    (Y : @Ob C)
  : (coyoneda_desc κ ∘r coyoneda_eval Y) ≈f κ Y.
Proof. intros [x [h]]. exact (coyoneda_cowedge_factor κ Y x h). Defined.

(** The same identity component makes this extension unique in FunEq. *)

(** 同一恒等分量使该延拓在指定函数相等下唯一。 *)

Definition coyoneda_desc_unique {W : SetC}
    (κ : Cowedge (CoyonedaKernel F Z) W)
  : is_unique (λ f, ∀ Y, (f ∘r coyoneda_eval Y) ≈f κ Y) (coyoneda_desc κ).
Proof.
  refine {|this := coyoneda_desc_β κ; that := _|}.
  intros f H x.
  transitivity (f (fmap F (id[Z]) x)).
  - apply (@func_proper _ _ f). symmetry. exact (@fct_id C SetCat F Z x).
  - exact (H Z (coyoneda_seed x)).
Defined.

(** The ordinary coend universal property reads the existing opposite-end
    interface; it does not introduce a second coend representation. *)

(** 通常 coend 泛性质使用已有反 end 接口，不引入第二种 coend 表示。 *)

Definition coyoneda_universal
  : is_coend CoyonedaCowedge.
Proof.
  apply (snd (coend_universal_iff CoyonedaCowedge)).
  intros W κ. exists (coyoneda_desc κ). exact (coyoneda_desc_unique κ).
Defined.

(** Enable just this coend explicitly on the original value F Z. Importing
    the module makes no global choice of coends or complete model. *)

(** 只在原值 F Z 上显式启用此 coend；导入模块不作全局 coend 或完备模型选择。 *)

Program Definition CoyonedaCoend
  : HasCoend SetCat (CoyonedaKernel F Z)
  :=
  {|hasOpEnd :=
      {|EndObj := F Z
      ; end_wedge := op_wedge CoyonedaCowedge
      ; end_universal := coyoneda_universal
      |}
  |}.

End Evaluation.

(** ** Comparison with Any Supplied Coend

    Now select just this kernel's coend. Its ordinary descent map evaluates
    generators; reinserting the identity gives the transparent inverse.
    Both inverse laws use specified equality, not equality of representatives. *)

(** ** 与任意给定 Coend 比较

    现在只选择此核的 coend。其通常下降映射求值生成元，重新插入恒等给出透明逆。
    两条互逆定律使用指定相等，不使用代表的原生相等。 *)

Section ChosenCoend.
Universes u p a b.
Context {C : Cat}.
Context (F : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _}))
    (Z : @Ob C).
Context `{HC : !HasCoend SetCat (CoyonedaKernel F Z)}.

(** The chosen coend evaluates by its existing universal mediator. *)

(** 选定 coend 通过其已有泛中介求值。 *)

Definition coyoneda_out
  : coend[CoyonedaKernel F Z] →r F Z
  := coend⟨CoyonedaCowedge F Z⟩.

(** Evaluation computes to the original functor action on each generator. *)

(** 求值在每个生成元上计算为原函子作用。 *)

Lemma coyoneda_out_β (Y : @Ob C) (x : F Y) (h : Hom Y Z)
  : coyoneda_out (ιcoend[CoyonedaKernel F Z] Y (x,{|lower := h|})) ≈S
      fmap F h x.
Proof. exact (coend_β (CoyonedaCowedge F Z) Y (x,{|lower := h|})). Defined.

(** Reinsert at the evaluation object using its identity weight. *)

(** 在求值对象处以其恒等权重重新插入。 *)

Definition coyoneda_in
  : F Z →r coend[CoyonedaKernel F Z]
  := ιcoend[CoyonedaKernel F Z] Z ∘r coyoneda_seed F Z.

(** Identity insertion followed by evaluation is the original identity law. *)

(** 恒等插入后求值就是原恒等律。 *)

Lemma coyoneda_out_in
  : (coyoneda_out ∘r coyoneda_in) ≈f id_resp.
Proof.
  intros x. transitivity (fmap F (id[Z]) x).
  - exact (coyoneda_out_β Z x (id[Z])).
  - exact (@fct_id C SetCat F Z x).
Defined.

(** Evaluation followed by insertion fixes the whole coend by generator
    extensionality and the previously proved cowedge factorization. *)

(** 求值后插入由生成元外延性及前述余楔分解固定整个 coend。 *)

Lemma coyoneda_in_out
  : (coyoneda_in ∘r coyoneda_out) ≈f id_resp.
Proof.
  apply (@coend_hom_ext C SetCat (CoyonedaKernel F Z) HC).
  intros Y [x [h]].
  transitivity (coyoneda_in (fmap F h x)).
  - exact (@func_proper _ _ coyoneda_in _ _ (coyoneda_out_β Y x h)).
  - exact (coyoneda_cowedge_factor F Z ιcoend[CoyonedaKernel F Z] Y x h).
Defined.

(** Package these same forward and inverse maps, retaining transparent
    computation and the originally supplied coend choice. *)

(** 打包同一正逆映射，保留透明计算及原来给定的 coend 选择。 *)

Definition CoyonedaIso
  : coend[CoyonedaKernel F Z] ≅[SetCat] F Z
  := (coyoneda_out; (coyoneda_in; (coyoneda_in_out,coyoneda_out_in))).

End ChosenCoend.

(** ** Changing the Functor and the Evaluation Object

    These kernel maps need no selected coends. Their evaluation equations
    are ordinary naturality and functor composition, respectively. *)

(** ** 改变函子及求值对象

    这些核映射不要求选定 coend，其求值方程分别为通常自然性及函子复合。 *)

Section KernelMaps.
Universes u p a b.
Context {C : Cat}.

(** Transform the value coordinate while retaining the same Hom weight. *)

(** 变换值坐标，保留相同 Hom 权重。 *)

Program Definition CoyonedaInputN
    {F G : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ G) (Z : @Ob C)
  : CoyonedaKernel F Z ⇒ CoyonedaKernel G Z
  :=
  {|nt AB :=
      {|func w := (α (snd AB) (fst w),snd w)
      |}
  |}.
Next Obligation.
  intros [x h] [y k] [Hx Hh]. split.
  - exact (@func_proper _ _ (α (snd AB)) x y Hx).
  - exact Hh.
Defined.
Next Obligation.
  intros [x h]. split; [exact (nat_naturality α (snd f) x) | reflexivity].
Defined.

(** Postcompose the represented arrow with a target arrow. *)

(** 将所表示箭头与目标箭头后合成。 *)

Program Definition CoyonedaPostN
    (F : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _}))
    {Z Z' : @Ob C} (f : Hom Z Z')
  : CoyonedaKernel F Z ⇒ CoyonedaKernel F Z'
  :=
  {|nt AB :=
      {|func w := (fst w,{|lower := f ∘ lower (snd w)|})
      |}
  |}.
Next Obligation.
  intros [x h] [y k] [Hx Hh]. split; [exact Hx |].
  refine {|lower := _|}. apply comp_proper; [reflexivity | exact (lower Hh)].
Defined.
Next Obligation.
  intros [x h]. split; [reflexivity |].
  refine {|lower := _|}. symmetry. apply comp_assoc.
Defined.

(** Evaluation commutes with an input natural transformation. *)

(** 求值与输入自然变换交换。 *)

Lemma coyoneda_eval_input
    {F G : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ G) (Z Y : @Ob C)
  : (α Z ∘r coyoneda_eval F Z Y) ≈f
      (coyoneda_eval G Z Y ∘r CoyonedaInputN α Z (Y,Y)).
Proof. intros [x [h]]. exact (nat_naturality α h x). Defined.

(** Evaluation of a postcomposed weight is functor composition. *)

(** 对后合成权重求值就是函子复合。 *)

Lemma coyoneda_eval_post
    (F : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _}))
    {Z Z' : @Ob C} (f : Hom Z Z') (Y : @Ob C)
  : (fmap F f ∘r coyoneda_eval F Z Y) ≈f
      (coyoneda_eval F Z' Y ∘r CoyonedaPostN F f (Y,Y)).
Proof.
  intros [x [h]]. symmetry. exact (@fct_comp C SetCat F Y Z Z' f h x).
Defined.

End KernelMaps.

(** ** Naturality for the Supplied Coends

    Choose only the two coends occurring in each comparison square. Coend
    injection equations extend the preceding evaluation laws to the whole
    coends, with no uniform choice family. *)

(** ** 关于给定 Coend 的自然性

    只选择每个比较方块中的两个 coend。coend 注入方程将前述求值定律延拓到整个
    coend，不要求统一选择族。 *)

Section Naturality.
Universes u p a b.
Context {C : Cat}.

(** The chosen evaluation comparison is natural in the input functor. *)

(** 选定求值比较关于输入函子自然。 *)

Lemma coyoneda_out_input
    {F G : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ G) (Z : @Ob C)
    `{HF : !HasCoend SetCat (CoyonedaKernel F Z)}
    `{HG : !HasCoend SetCat (CoyonedaKernel G Z)}
  : (α Z ∘r coyoneda_out F Z) ≈f
      (coyoneda_out G Z ∘r coend_map (CoyonedaInputN α Z)).
Proof.
  apply (@coend_hom_ext C SetCat (CoyonedaKernel F Z) HF).
  intros Y [x [h]].
  transitivity (α Z (fmap F h x)).
  - exact (@func_proper _ _ (α Z) _ _ (coyoneda_out_β F Z Y x h)).
  - transitivity (fmap G h (α Y x)).
    + exact (coyoneda_eval_input α Z Y (x,{|lower := h|})).
    + transitivity (coyoneda_out G Z
        (ιcoend[CoyonedaKernel G Z] Y (α Y x,{|lower := h|}))).
      * symmetry. exact (coyoneda_out_β G Z Y (α Y x) h).
      * symmetry. exact (@func_proper _ _ (coyoneda_out G Z) _ _
          (coend_map_β (CoyonedaInputN α Z) Y (x,{|lower := h|}))).
Defined.

(** The chosen comparison is natural in its evaluation object as well. *)

(** 选定比较也关于其求值对象自然。 *)

Lemma coyoneda_out_post
    (F : Fct@{_ _ _ _ a b _ _ _ _} C (SetCat@{u p _ _ _ _ _}))
    {Z Z' : @Ob C} (f : Hom Z Z')
    `{HF : !HasCoend SetCat (CoyonedaKernel F Z)}
    `{HG : !HasCoend SetCat (CoyonedaKernel F Z')}
  : (fmap F f ∘r coyoneda_out F Z) ≈f
      (coyoneda_out F Z' ∘r coend_map (CoyonedaPostN F f)).
Proof.
  apply (@coend_hom_ext C SetCat (CoyonedaKernel F Z) HF).
  intros Y [x [h]].
  transitivity (fmap F f (fmap F h x)).
  - exact (@func_proper _ _ (fmap F f) _ _ (coyoneda_out_β F Z Y x h)).
  - transitivity (fmap F (f ∘ h) x).
    + exact (coyoneda_eval_post F f Y (x,{|lower := h|})).
    + transitivity (coyoneda_out F Z'
        (ιcoend[CoyonedaKernel F Z'] Y (x,{|lower := f ∘ h|}))).
      * symmetry. exact (coyoneda_out_β F Z' Y x (f ∘ h)).
      * symmetry. exact (@func_proper _ _ (coyoneda_out F Z') _ _
          (coend_map_β (CoyonedaPostN F f) Y (x,{|lower := h|}))).
Defined.

End Naturality.
