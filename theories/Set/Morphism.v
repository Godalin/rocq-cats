From Cats.Set Require Export Core.

(** * Respectful Maps

    A map between mathematical sets must preserve their specified equality.
    This module bundles a function with that preservation proof, then makes
    these maps into a set with pointwise equality in the codomain. This is
    the same set-based foundation later used for category homs.

    Pointwise equality is our equality of maps. We prove its laws directly;
    we do not need an axiom converting it to Rocq's equality of functions.
    Nor do we compare the stored preservation proofs by native equality. *)

(** * 保相等映射

    数学集合之间的映射必须保持各自指定的相等。本模块将函数及其保相等证明
    打包，再以目标中的逐点相等将这些映射组成广集。这也是后续范畴 Hom 使用
    的集合基础。

    逐点相等就是本库的映射相等，其定律直接证明，不需要将它转为 Rocq 函数
    相等的公理，也不使用原生相等比较所保存的保相等证明。 *)

(** [f ≈f g] means that [f x ≈S g x] for every representative [x]. The
    definition applies even to bare functions; preservation of source
    equality is a separate requirement, supplied by [FunS_resp] below. *)

(** [f ≈f g] 表示每个代表 [x] 都满足 [f x ≈S g x]。这个定义也适用于未打包
    的函数；保持来源相等是另一项要求，由下方的 [FunS_resp] 提供。 *)

Definition FunEq {X Y : SetC} (f g : X → Y)
  := ∀ x : X, f x ≈S g x.

Infix "≈f" := FunEq (at level 50).

(** [FunEq] is an equivalence relation. *)

(** [FunEq] 是等价关系。 *)

Program Instance FunEq_Equivalence {X Y}
  : Equivalence (@FunEq X Y).
Next Obligation. intros f x. reflexivity. Defined.
Next Obligation. intros f g H x. symmetry. apply H. Defined.
Next Obligation. intros f g h H1 H2 x. transitivity (g x); auto. Defined.

(** A function together with preservation of specified equality. The
    coercion [func] lets a bundled map be applied directly to an element.
    Its [func_proper] field sends [x ≈S x'] to [func x ≈S func x'].
    Constructing a map requires supplying this proof; it is not assumed.

    [X →r Y] denotes the type of these bundled maps. Later, [X →S Y] will
    denote the set whose carrier is that type and whose equality is [FunEq]. *)

(** 函数及其保持指定相等的见证。强制转换 [func] 使打包后的映射可以直接作用于
    元素；字段 [func_proper] 将 [x ≈S x'] 送到 [func x ≈S func x']。构造映射
    时必须提供这个证明，不能将它视为假定。

    [X →r Y] 表示这些打包映射的类型；后面的 [X →S Y] 则表示以该类型为载体、
    以 [FunEq] 为相等的广集。 *)

Record FunS_resp (X Y : SetC)
  :=
  { func :> carrier X → carrier Y
  ; func_proper :: Proper (carrier_equiv X ==> carrier_equiv Y) func
  }.

Infix "→r" := FunS_resp (at level 99).

(** Lift a respectful map by unwrapping its input, applying the original
    map, and wrapping the result. Preservation likewise wraps the original
    proof, so the construction retains the specified equality and computes.

    The input map's Proper carrier bound [s] is independent of the target
    carrier level [v]; lifting a native hom-map must not identify them. *)

(** 提升保相等映射：拆开输入包装，应用原映射，再包装结果。保相等性同样通过
    包装原证明得到，因此构造保留指定相等，并保持可计算。

    输入映射的 Proper 载体上界 [s] 独立于目标载体层级 [v]；提升原生 Hom 映射
    时不能把两者等同。 *)

Program Definition lift_resp@{v q s +} {X Y : SetC}
    (f : FunS_resp@{s _ _ _ _ _} X Y)
  : LiftS@{_ _ v q} X →r LiftS@{_ _ v q} Y
  :=
  {|func x :=
     {|lower := f (lower x)
     |}
  |}.
Next Obligation.
  intros [x] [y] [H]. exact {|lower := @func_proper _ _ f x y H
                            |}.
Defined.

Notation "f '^↑S'" := (lift_resp f) (at level 35) : set_scope.

(** The set of respectful maps, with pointwise equality. Equal maps need
    not be native-equal records: equality examines their values, without
    comparing their [func_proper] fields. This does not assert proof
    irrelevance; those fields remain stored data.

    Reflexivity, symmetry and transitivity are inherited pointwise from the
    target set. Thus the function set needs no function-extensionality axiom. *)

(** 以逐点相等比较保相等映射的集合。相等映射不必是原生相等的记录：这里比较
    各点的值，不比较 [func_proper] 字段。这没有断言证明无关性，这些字段仍是
    保存的数据。

    自反、对称及传递律逐点继承自目标集合，因此构造函数集合不需要函数外延性
    公理。 *)

Program Canonical FunS (X Y : SetC)
  : SetC
  :=
  {|carrier := X →r Y
  ; carrier_equiv := FunEq
  |}.
Next Obligation. split.
  - intros f x. reflexivity.
  - intros f g H x. symmetry. apply H.
  - intros f g h H1 H2 x. transitivity (g x); auto.
Defined.

Infix "→S" := FunS (at level 99).

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance lift_resp_proper@{v q +} {X Y : SetC}
  : Proper (carrier_equiv (X →S Y) ==>
      carrier_equiv (LiftS@{_ _ v q} X →S LiftS@{_ _ v q} Y))
      (λ f, (f^↑S : LiftS@{_ _ v q} X →r LiftS@{_ _ v q} Y)).
Proof. intros f g H [x]. exact {|lower := H x
                               |}. Defined.

(** The identity respectful map returns its input and preserves each
    equality witness unchanged. *)

(** 恒等保相等映射返回输入，并原样保留每个相等见证。 *)

Program Definition id_resp {X}
  : X →r X
  :=
  {|func (x : X) := x
  |}.
Next Obligation. intros x x' Hx. exact Hx. Defined.

(** Composition applies the right map first: [(f ∘r g) x] computes to
    [f (g x)]. Preservation follows by applying the preservation proofs
    of [g] and then [f]. *)

(** 复合先应用右侧映射：[(f ∘r g) x] 计算为 [f (g x)]。依次应用 [g] 与 [f]
    的保相等证明即可得到复合的保相等性。 *)

Program Definition comp_resp {X Y Z} (f : Y →r Z) (g : X →r Y)
  : X →r Z
  :=
  {|func (x : X) := f (g x)
  |}.
Next Obligation. intros x x' Hx. rewrite Hx. reflexivity. Defined.

Infix "∘r" := comp_resp (at level 50).

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance comp_resp_proper {X Y Z}
  : Proper (carrier_equiv (Y →S Z) ==> carrier_equiv (X →S Y)
      ==> carrier_equiv (X →S Z)) (@comp_resp X Y Z).
Proof.
  intros f f' Hf g g' Hg x. cbn.
  rewrite (Hg x), (Hf (g' x)). reflexivity.
Qed.

(** Right identity law in the specified equality of maps. As with the
    following left identity and associativity laws, evaluation at an
    arbitrary input reduces both sides to the same value; reflexivity in
    the target set completes the proof. No equality of functions or of
    record fields is required. *)

(** 映射指定相等下的右单位律。与后面的左单位律、结合律一样，对任意输入求值
    后两侧归约为同一个值，再应用目标集合的自反性即可。不需要函数或记录字段
    的原生相等。 *)

Theorem comp_resp_id_r {X Y} (f : X →r Y)
  : f ∘r id_resp ≈f f.
Proof. intros x. reflexivity. Qed.

(** Left identity law for [comp_resp]. *)

(** [comp_resp] 左单位律。 *)

Theorem comp_resp_id_l {X Y} (f : X →r Y)
  : id_resp ∘r f ≈f f.
Proof. intros x. reflexivity. Qed.

(** Associativity law for [comp_resp]. *)

(** [comp_resp] 结合律。 *)

Theorem comp_resp_assoc {W X Y Z} (f : Y →r Z) (g : X →r Y) (h : W →r X)
  : ((f ∘r g) ∘r h) ≈f (f ∘r (g ∘r h)).
Proof. intros x. reflexivity. Qed.
