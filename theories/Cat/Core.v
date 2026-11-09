From Cats.Set Require Export Morphism.

Declare Scope ob_scope.
Delimit Scope ob_scope with ob.
Open Scope ob_scope.

Declare Scope hom_scope.
Delimit Scope hom_scope with hom.
Open Scope hom_scope.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Open Scope cat_scope.



(** * Categories over the Foundational Sets

    A category has a type of objects and, for each pair [X], [Y], a set
    [HomSet X Y] of morphisms. Here set means exactly the foundational
    [SetC]: a carrier with a specified, Type-valued equivalence relation.
    Thus category theory uses the same equality foundation as sets and
    respectful maps; it does not introduce a parallel notion of equality.

    [Hom X Y] reads the carrier of this set, and [HomEq] reads its equality.
    These are computed fields, not additional data to choose. The notation
    [f ≈ g] is precisely the specified set equality on parallel morphisms.
    Identity and associativity are strict laws in this equality.

    Objects form a type [Ob]; this interface does not equip them with a
    specified set equality. Equality of parallel morphisms, native equality
    of objects, and object isomorphism therefore have different roles.
    In particular, an isomorphism need not be a native object equality. *)

(** * 基于基础广集的范畴

    范畴具有一个对象类型，并为每对对象 [X]、[Y] 指定态射集合 [HomSet X Y]。
    这里的集合就是基础层的广集 [SetC]：载体及 Type 值指定等价关系。因此，
    范畴论与集合、保相等映射共用同一套相等基础，不另设平行的相等机制。

    [Hom X Y] 读取这个集合的载体，[HomEq] 读取其相等。它们是计算字段，不是
    另外选取的数据。记号 [f ≈ g] 就是平行态射所在广集的指定相等，单位律和
    结合律都是这个相等下的严格定律。

    对象组成类型 [Ob]，本接口不为其配备指定的广集相等。因此，平行态射相等、
    对象原生相等及对象同构各有不同作用；特别地，对象同构不必是原生相等。 *)

(** ** Reading the Category Interface

    A model must construct all these witnesses. Class law fields are
    requirements on a structure, not globally asserted axioms. For example,
    replacing a factor in a composite uses [comp_proper], while removing an
    identity uses one of the unit laws. The equivalence laws needed to join
    such steps already belong to [HomSet].

    In [Cat@{o h p}], [o] is the object level, [h] the hom carrier level,
    and [p] the hom-equality witness level. Morphisms and their equality
    witnesses have independent sizes. Equivalence and properness laws may
    inhabit larger auxiliary universes, without forcing these levels equal.

    For example, the later category [SetCat] chooses the respectful-function
    set [X →S Y] as [HomSet X Y]. Its arrows are respectful maps and its
    equations are pointwise set equality. General results here already
    operate on hom-sets directly, without importing that concrete model. *)

(** ** 范畴接口逐项解读

    模型必须构造全部见证；类的定律字段是结构应满足的要求，不是全局断言的
    公理。例如，替换复合中的因子使用 [comp_proper]，去掉恒等箭头使用相应的
    单位律；串接这些推理步骤所需的等价律已由 [HomSet] 提供。

    在 [Cat@{o h p}] 中，[o] 是对象层级，[h] 是 Hom 载体层级，[p] 是 Hom 相等
    见证层级。态射与其相等见证的大小独立，等价律及保相等定律可位于更大的
    辅助宇宙，不迫使这些层级相等。

    例如，后面的集合范畴 [SetCat] 以保相等函数广集 [X →S Y] 为 [HomSet X Y]；
    它的箭头是保相等映射，方程就是逐点集合相等。此处的一般理论已能直接操作
    Hom 广集，不必导入这个具体模型。 *)

Class Cat@{o h p +}
  :=
  (** [Ob] is the type of objects. A term [X : @Ob C] is an object of [C]. *)

  (** [Ob] 是对象类型。[X : @Ob C] 表示 [C] 的一个对象。 *)

  { Ob : Type@{o}
  (** [HomSet X Y] is the set of arrows from [X] to [Y], including its
      specified equivalence relation and equivalence laws. *)

  (** [HomSet X Y] 是从 [X] 到 [Y] 的箭头广集，包含指定等价关系及其等价律。 *)

  ; HomSet : Ob → Ob → SetC@{h p}
  (** [Hom X Y] is the carrier of the hom-set: the type of individual arrows.
      It is computed from [HomSet], rather than supplied separately. *)

  (** [Hom X Y] 是 Hom 广集的载体，即单条箭头所属的类型。它由 [HomSet]
      计算得到，无须单独提供。 *)

  ; Hom (X Y : Ob) : Type@{h} := carrier (HomSet X Y)
  (** [HomEq f g] is the specified equality of parallel arrows, written
      [f ≈ g] below. It is computed from [HomSet]. Its witnesses live in
      [Type], so the interface retains their data. *)

  (** [HomEq f g] 是平行箭头的指定相等，下文记为 [f ≈ g]。它由 [HomSet]
      计算得到；相等见证位于 [Type]，接口保留其数据。 *)

  ; HomEq {X Y} : Hom X Y → Hom X Y → Type@{p}
  := carrier_equiv (HomSet X Y)

  (** [id] selects an identity arrow for each object. The object argument
      is implicit; [@id X] below makes the intended object explicit. *)

  (** [id] 为每个对象选定恒等箭头。对象参数隐含传入；下文的 [@id X]
      显式指定这个对象。 *)

  ; id {X} : Hom X X

  (** [comp] composes [g : Hom X Y] with [f : Hom Y Z], producing
      [f ∘ g : Hom X Z]. The right-hand arrow acts first. *)

  (** [comp] 将 [g : Hom X Y] 与 [f : Hom Y Z] 复合，得到
      [f ∘ g : Hom X Z]，右侧箭头先作用。 *)

  ; comp {X Y Z} : Hom Y Z → Hom X Y → Hom X Z

  (** [comp_proper] makes composition respectful in both arguments:
      [f ≈ f'] and [g ≈ g'] imply [f ∘ g ≈ f' ∘ g']. The [::] registers
      this field as an inherited instance for setoid rewriting. *)

  (** [comp_proper] 要求复合对两个参数都保相等：由 [f ≈ f'] 和 [g ≈ g']
      得到 [f ∘ g ≈ f' ∘ g']。[::] 将此字段注册为继承实例，供广集重写使用。 *)

  ; comp_proper {X Y Z}
    :: Proper (@HomEq Y Z ==> @HomEq X Y ==> @HomEq X Z) comp

  (** [comp_id_r] states [f ∘ id ≈ f], using the identity at the source. *)

  (** [comp_id_r] 给出 [f ∘ id ≈ f]，其中恒等箭头位于源对象。 *)

  ; comp_id_r {X Y : Ob} (f : Hom X Y)
    : HomEq (comp f id) f

  (** [comp_id_l] states [id ∘ f ≈ f], using the identity at the target. *)

  (** [comp_id_l] 给出 [id ∘ f ≈ f]，其中恒等箭头位于目标对象。 *)

  ; comp_id_l {X Y : Ob} (f : Hom X Y)
    : HomEq (comp id f) f

  (** [comp_assoc] states [(f ∘ g) ∘ h ≈ f ∘ (g ∘ h)]. It permits
      regrouping a composable chain without changing its order. *)

  (** [comp_assoc] 给出 [(f ∘ g) ∘ h ≈ f ∘ (g ∘ h)]，允许改变可复合箭头链
      的括号，而不改变箭头顺序。 *)

  ; comp_assoc {X Y Z W}
      (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y)
    : HomEq (comp (comp f g) h) (comp f (comp g h))
  }.

(** Reflexivity, symmetry and transitivity come directly from the hom-set.
    A category need not provide a second equivalence structure for [HomEq].
    This instance lets setoid reasoning and rewriting use the equality
    already supplied by [HomSet]. *)

(** 自反、对称与传递律直接来自 Hom 广集，范畴无须为 [HomEq] 再提供一套等价
    结构。这个实例使广集推理和重写直接使用 [HomSet] 已有的相等。 *)

Global Instance HomEq_Equivalence {C : Cat} {X Y : @Ob C}
  : Equivalence (@HomEq C X Y)
  := carrier_setoid (HomSet X Y).

(** Read the specified set between two fixed objects. This transparent
    alias preserves both its carrier and its equality. Merely viewing homs
    as sets needs no additional category of sets or choice of equality. *)

(** 读取两个固定对象之间的指定集合。这个透明别名保留其载体及相等，将 Hom
    视为集合不需要额外的集合范畴，也无须重新选择相等。 *)

Definition Hom_SetC {C : Cat} {X Y : @Ob C}
  : SetC
  := HomSet X Y.

Arguments HomEq {_ _%_ob _%_ob} _%_hom _%_hom.
Arguments comp_id_l {_ _ _} _.
Arguments comp_id_r {_ _ _} _.
Arguments comp_assoc {_ _ _ _ _} _ _ _.

Bind Scope ob_scope with Ob.
Bind Scope hom_scope with Hom.

Notation "'@Ob' C" := (@Ob C)
  (at level 35) : cat_scope.

Notation "'@Hom' C" := (@Hom C)
  (at level 35) : cat_scope.

Notation "'@HomEq[' X ',' Y  ']'" := (@HomEq _ X Y) : cat_scope.

(** [f ≈ g] compares parallel arrows using their hom-set equality, the
    same relation that [≈S] reads from [HomSet]. Composition [f ∘ g]
    applies [g] first. The [Proper] field makes replacement of equal
    arrows in compositions valid. *)

(** [f ≈ g] 使用所在 Hom 广集的相等比较平行箭头，与 [≈S] 从 [HomSet] 读取的
    关系相同。复合 [f ∘ g] 先应用 [g]；[Proper] 字段保证可以在复合中替换
    相等箭头。 *)

Infix "≈" := HomEq
  (at level 50, no associativity) : cat_scope.

Notation "f '≈' g '⦂' 'Hom(' X ',' Y ')'" := (@HomEq _ X Y f g)
  (at level 50, no associativity, only printing,
    format "f  '≈'  g  '⦂'  'Hom(' X  ','  Y )") : cat_scope.

Notation "f '≉' g" := (¬ HomEq f g)
  (at level 50, no associativity) : cat_scope.

Notation "f '≉' g '⦂' 'Hom(' X ',' Y ')'" := (¬ @HomEq _ X Y f g)
  (at level 50, no associativity, only printing,
    format "f  '≉'  g  '⦂'  'Hom(' X  ','  Y )") : cat_scope.

Notation "'@id' X" := (@id _ X)
  (at level 35) : hom_scope.

Notation "f '∘' g" := (comp f g)
  (at level 40, left associativity) : hom_scope.

(** Category auto & eauto *)

(** 用于范畴目标的自动搜索策略。 *)

Ltac cato := auto with cat; try reflexivity.
Ltac cate := eauto with cat; try reflexivity.

(** Category auto rewriting, eagerly simplifies the goal (with β rules and
    simple η rules) *)

(** 范畴自动重写策略，主动化简目标，使用 β 律及简单 η 律。 *)

Ltac carw := autorewrite with cat using try reflexivity.

(** Category association rewriting *)

(** 调整复合结合方向的范畴重写策略。 *)

Ltac rw_assoc_r args := rewrite (comp_assoc args); cato.
Ltac rw_assoc_l args := rewrite <- (comp_assoc args); cato.

Tactic Notation "cacr" := rewrite comp_assoc; cato.
Tactic Notation "cacr" constr(t) := rw_assoc_r t.
Tactic Notation "cacl" := rewrite <- comp_assoc; cato.
Tactic Notation "cacl" constr(t) := rw_assoc_l t.

Hint Resolve comp_id_l : cat.
Hint Resolve comp_id_r : cat.

Hint Rewrite @comp_id_l : cat.
Hint Rewrite @comp_id_r : cat.



Section CatBasic.
Context {C : Cat} {X Y : Ob}.

(** Reverse the left identity equation. *)

(** 反向使用左单位方程。 *)

Theorem symm_id_l {x : Hom X Y}
  : x ≈ id ∘ x.
Proof. symmetry. cato. Qed.

(** Reverse the right identity equation. *)

(** 反向使用右单位方程。 *)

Theorem symm_id_r {x : Hom X Y}
  : x ≈ x ∘ id.
Proof. symmetry. cato. Qed.

End CatBasic.

Hint Resolve symm_id_l : cat.
Hint Resolve symm_id_r : cat.



(** ** Morphisms induced by object equality

    Since [Ob] is a Rocq type, a native equality [p : X = Y] allows the
    identity at [X] to be transported to an arrow [X → Y]. Equality
    elimination constructs this arrow and proves its laws; no uniqueness
    of identity proofs or identification of distinct witnesses is needed.

    These lemmas concern native object equality only. They do not turn
    arbitrary object isomorphisms into native equalities. Their conclusions
    still use the specified equality of the appropriate hom-set. *)

(** ** 由对象原生相等诱导的态射

    [Ob] 是 Rocq 类型，因此原生相等 [p : X = Y] 允许将 [X] 的恒等态射运输为
    [X → Y] 的箭头。相等消去即可构造箭头并证明定律，无须恒等证明唯一性，也
    不要求不同相等见证一致。

    这些引理只处理对象的原生相等，不将任意对象同构转为原生相等；结论中的
    态射方程仍使用对应 Hom 广集的指定相等。 *)

Definition eq_to_hom {C : Cat} {X Y : @Ob C} (p : X = Y)
  : Hom X Y
  := match p with eq_refl => id end.

(** Compatibility with composition for [eq_to_hom]. *)

(** [eq_to_hom] 与复合的相容性。 *)

Lemma eq_to_hom_comp {C : Cat} {X Y Z : @Ob C} (p : X = Y) (q : Y = Z)
  : eq_to_hom (eq_trans p q) ≈ eq_to_hom q ∘ eq_to_hom p.
Proof. destruct p, q. simpl. symmetry. apply comp_id_l. Qed.

(** Transported identities along opposite native equalities cancel on the
    left. *)

(** 沿反向原生相等运输的恒等态射在左侧抵消。 *)

Lemma eq_to_hom_inv_l {C : Cat} {X Y : @Ob C} (p : X = Y)
  : eq_to_hom (eq_sym p) ∘ eq_to_hom p ≈ id.
Proof. destruct p. simpl. apply comp_id_l. Qed.

(** Transported identities along opposite native equalities cancel on the
    right. *)

(** 沿反向原生相等运输的恒等态射在右侧抵消。 *)

Lemma eq_to_hom_inv_r {C : Cat} {X Y : @Ob C} (p : X = Y)
  : eq_to_hom p ∘ eq_to_hom (eq_sym p) ≈ id.
Proof. destruct p. simpl. apply comp_id_l. Qed.



(** Precompose a morphism with a fixed arrow. *)

(** 将态射与固定箭头预合成。 *)

Definition comp_pre `{C : Cat} {X Y Z : Ob} (f : Hom X Y)
  := (λ g : Hom Y Z, g ∘ f).

(** Postcompose a morphism with a fixed arrow. *)

(** 将态射与固定箭头后合成。 *)

Definition comp_post `{C : Cat} {X Y Z : Ob} (f : Hom Y Z)
  := (λ g : Hom X Y, f ∘ g).

Arguments comp_pre {_ _ _ _} _ _ /.
Arguments comp_post {_ _ _ _} _ _ /.

Notation "f ^*" := (comp_pre f) (at level 35).
Notation "f _*" := (comp_post f) (at level 35).

(** Postcomposition by a fixed [f : Hom Y Z], bundled as a respectful
    map [HomSet X Y →r HomSet X Z]. Its preservation proof comes from
    [comp_proper]. This exposes the set-level action of any category's
    composition, before constructing a Hom functor into a category of sets. *)

(** 固定 [f : Hom Y Z] 后的后合成，打包为保相等映射
    [HomSet X Y →r HomSet X Z]。其保相等证明来自 [comp_proper]。这在构造以
    集合范畴为目标的 Hom 函子之前，就给出了任意范畴复合的集合层作用。 *)

Program Canonical comp_l_resp {C : Cat} {X Y Z : Ob}
    {f : Hom Y Z}
  : HomSet X Y →r HomSet X Z
  :=
  {|func := f _*
  |}.

(** Precomposition by a fixed [f : Hom X Y], as a respectful map
    [HomSet Y Z →r HomSet X Z]. The direction reverses the varying source
    object, as needed by contravariant Hom constructions. *)

(** 固定 [f : Hom X Y] 后的预合成，作为保相等映射
    [HomSet Y Z →r HomSet X Z]。它反转变动来源对象的方向，为反变 Hom 构造
    提供所需作用。 *)

Program Canonical comp_r_resp {C : Cat} {X Y Z : Ob}
    {f : Hom X Y}
  : HomSet Y Z →r HomSet X Z
  :=
  {|func := f ^*
  |}.
Next Obligation.
  intros g1 g2 Hg. unfold comp_pre. rewrite Hg. reflexivity.
Qed.



(** ** Dual Category *)

(** ** 对偶范畴 *)

(** Reverse homs and composition to form [C^op]. Each hom-set is exactly
    an existing hom-set with its endpoints exchanged, so its carrier and
    specified equality are reused. Unit laws exchange sides; associativity
    follows by symmetry. No new equality or additional assumption is needed.

    Later dual constructions reuse the original theory on this opposite
    category and expose ordinary names for the resulting operations. *)

(** 反转 Hom 与复合，构造 [C^op]。每个 Hom 广集就是交换端点后的原 Hom 广集，
    载体及指定相等直接复用。单位律交换两侧，结合律由对称性得到，无须新的
    相等或额外假设。

    后续对偶构造在这个反范畴上复用原理论，再以通常名称提供所得运算。 *)

Program Definition op (C : Cat)
  : Cat
  :=
  {|Ob := Ob
  ; HomSet X Y := HomSet Y X
  ; id _ := id
  ; comp _ _ _ f g := comp g f
  |}.
Next Obligation.
  intros x x' Hx y y' Hy.
  rewrite Hx, Hy.
  reflexivity.
Qed.
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_id_r. Qed.
Next Obligation.
  symmetry. apply comp_assoc.
Qed.

Notation "C '^op'" := (op C)
  (at level 60).

(** View an object in the opposite category. *)

(** 将对象视为反范畴中的对象。 *)

Definition ob_op {C : Cat} (X : @Ob C)
  : (@Ob (C ^op))
  := X.

(** Transport in the opposite category uses the reversed object equality. *)

(** 反范畴中的运输使用反向对象相等。 *)

Lemma eq_to_hom_op {C : Cat} {X Y : @Ob C} (p : X = Y)
  : @eq_to_hom (C ^op) X Y p ≈ eq_to_hom (eq_sym p).
Proof. destruct p. reflexivity. Qed.



(** ** Prod Category *)

(** ** 乘积范畴 *)

(** The componentwise product of two categories. Objects and morphisms
    are pairs; equality of morphisms is [ProdEq HomEq HomEq], a pair of
    component equality witnesses. Identity, composition and their laws are
    computed componentwise. This needs neither native equality of the
    component arrows nor equality of their law proofs. *)

(** 两个范畴的逐分量乘积。对象及态射都是对，态射相等为
    [ProdEq HomEq HomEq]，即一对分量相等见证。恒等、复合及其定律逐分量构造，
    不需要分量箭头的原生相等，也不比较其定律证明是否相等。 *)

Program Definition ProdCat (C D : Cat)
  : Cat
  :=
  {|Ob := @Ob C * @Ob D
  ; HomSet X Y :=
      {|carrier := Hom (fst X) (fst Y) * Hom (snd X) (snd Y)
      ; carrier_equiv := ProdEq HomEq HomEq
      ; carrier_setoid := ProdEq_Equivalence _ _
      |}
  ; id _ := (id, id)
  ; comp _ _ _ f g := (fst f ∘ fst g, snd f ∘ snd g)
  |}.
Next Obligation. intros [fc fd] [gc gd] [H1c H1d].
  intros [hc hd] [jc jd] [H2c H2d]. split; simpl.
  rewrite H1c, H2c. reflexivity. rewrite H2d, H1d. reflexivity.
Qed.
Next Obligation. destruct f. simpl. split; apply comp_id_r. Qed.
Next Obligation. destruct f. simpl. split; apply comp_id_l. Qed.
Next Obligation. destruct f, g, h. simpl. split; apply comp_assoc. Qed.

Infix "×C" := ProdCat
  (at level 41).



Section Cat.
Context {C : Cat}.

(** ** Composition *)

(** ** 复合 *)

(** Postcomposition preserves the specified morphism equality. *)

(** 后合成保持指定态射相等。 *)

Proposition comp_l {X Y Z} (f : Hom Y Z) {x y : Hom X Y}
  : x ≈ y → f ∘ x ≈ f ∘ y.
Proof. intros Heq. rewrite Heq. cato. Qed.

(** Precomposition preserves the specified morphism equality. *)

(** 预合成保持指定态射相等。 *)

Proposition comp_r {X Y Z} (f : Hom X Y) {x y : Hom Y Z}
  : x ≈ y → x ∘ f ≈ y ∘ f.
Proof. intros Heq. rewrite Heq. cato. Qed.



(** ** Inversion & Isomorphism *)

(** ** 逆与同构 *)

(** The second arrow is a left inverse of the first. *)

(** 第二条箭头是第一条的左逆。 *)

Definition is_linv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := g ∘ f ≈ id.

(** The second arrow is a right inverse of the first. *)

(** 第二条箭头是第一条的右逆。 *)

Definition is_rinv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := f ∘ g ≈ id.

(** The two arrows are mutually inverse under specified hom equality. *)

(** 两条箭头在指定 Hom 相等下互逆。 *)

Definition is_inv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := is_linv_of f g ∧ is_rinv_of f g.

(** An arrow with a chosen inverse and both inverse equations. The
    existential notation is Type-valued: a witness of [is_iso f] stores
    an actual inverse, rather than only asserting its existence in [Prop].
    Both inverse equations use the specified hom-set equality. *)

(** 带选定逆及两条互逆方程的箭头。存在记号取值于 [Type]：[is_iso f] 的见证
    保存实际的逆，不只是 [Prop] 中的存在断言。两条互逆方程均使用 Hom 广集
    的指定相等。 *)

Definition is_iso {X Y} (f : Hom X Y)
  := ∃ g, is_inv_of f g.

(** An isomorphism retains its forward arrow, inverse and inverse laws.
    For [i : X ≅ Y], [i.1] is the forward arrow, [i.2.1] its inverse,
    and [i.2.2] the inverse equations. Reading the inverse is projection
    of supplied data and requires no choice axiom.

    This compares objects by invertible arrows, without asserting native
    object equality or forming a quotient of the object type. *)

(** 同构保留正向箭头、逆及互逆定律。对于 [i : X ≅ Y]，[i.1] 是正向箭头，
    [i.2.1] 是逆，[i.2.2] 是互逆方程。取逆只是投影已有数据，不需要选择公理。

    这里通过可逆箭头比较对象，不断言对象原生相等，也不构造对象类型的商。 *)

Definition iso X Y
  := ∃ f : Hom X Y, is_iso f.

(** Interchange the two arrows of an inverse pair. *)

(** 交换互逆对中的两条箭头。 *)

Theorem is_inv_of_comm {X Y} (f : Hom X Y) (g : Hom Y X)
  : is_inv_of f g → is_inv_of g f.
Proof. intros [H1 H2]. split; auto. Qed.

End Cat.

Hint Unfold is_linv_of : cat.
Hint Unfold is_rinv_of : cat.
Hint Unfold is_inv_of : cat.

Arguments is_linv_of {_ _ _} _ _ /.
Arguments is_rinv_of {_ _ _} _ _ /.
Arguments is_inv_of {_ _ _} _ _ /.

Arguments iso {_} _%_ob _%_ob.

Notation "X '≅' Y" := (iso X Y)
  (at level 70, no associativity) : type_scope.

Notation "X '≅[' C ']' Y" := (@iso C X Y)
  (at level 70, no associativity,
    format "X  ≅[ C ]  Y") : type_scope.

Notation "f '⦂' X '≅' Y" := (@is_iso _ X Y f)
  (at level 50, no associativity,
    X at level 49, Y at level 49).

Tactic Notation "elim_iso" ident(f) :=
  let fi := fresh f "i" in
  let Hfif := fresh "H" fi f in
  let Hffi := fresh "H" f fi in
  intros (f & fi & Hfif & Hffi).



Section Iso.
Context {C : Cat}.

(** Every object is isomorphic to itself. *)

(** 每个对象都与自身同构。 *)

Theorem iso_refl {X}
  : X ≅ X.
Proof. exists id, id. cato. Defined.

(** Reverse an object isomorphism, keeping the swapped witness arrows
    computational. *)

(** 反转对象同构，保持交换后的见证箭头可计算。 *)

Theorem iso_symm {X Y}
  : X ≅ Y → Y ≅ X.
Proof.
  intros i. exists i.2.1, i.1.
  destruct i as [f [fi [H1 H2]]]; cbn. split; assumption.
Defined.

(** Compose object isomorphisms. Forward arrows compose in order and
    inverse arrows in reverse order. The transparent proof retains these
    computed arrows; the inverse equations follow from the category laws. *)

(** 复合对象同构：正向箭头顺序复合，逆箭头逆序复合。透明证明保留这些计算
    得到的箭头，互逆方程由范畴定律推出。 *)

Theorem iso_trans {X Y Z}
  : X ≅ Y → Y ≅ Z → X ≅ Z.
Proof.
  intros i j. exists (j.1 ∘ i.1), (i.2.1 ∘ j.2.1).
  destruct i as [f [fi [Hf Hfi]]], j as [g [gi [Hg Hgi]]]; cbn.
  split; simpl.
  - rewrite comp_assoc.
    rewrite <- (comp_assoc gi).
    rewrite Hg, comp_id_l. auto.
  - rewrite comp_assoc.
    rewrite <- (comp_assoc f).
    rewrite Hfi, comp_id_l. auto.
Defined.

(** [iso] is an equivalence relation. *)

(** [iso] 是等价关系。 *)

Global Instance iso_Equivalence
  : Equivalence iso.
Proof.
  split.
  - intros x. apply iso_refl.
  - intros x y. apply iso_symm.
  - intros x y z. apply iso_trans.
Qed.

End Iso.
