# Universes of structured categories

# 结构范畴的宇宙

The complete bundles now support two further constructions with the shape
`X : X`. Each occurrence has its own universe instance: a small structured
category is an object of a larger one. These are ordinary universe-polymorphic
families, with no additional axioms or universe self-containment.

完整结构包现在支持另外两个形如 `X : X` 的构造。各处采用不同宇宙实例：
小的结构范畴是更大结构范畴的对象。这些都是普通宇宙多态族，不增加公理，
也不要求某个宇宙包含自身。

```coq
From Cats Require Import
  Cat.Core
  Cat.Cartesian.Core
  Cat.Cartesian.Category
  Cat.Groupoid.Core
  Cat.Groupoid.Category.

Check CartCatCartCat : CartCatCartCat : CartCatCartCat : CartCatCartCat.
Check GpdGpd : GpdGpd : GpdGpd : GpdGpd.
```

These checks appear immediately after the corresponding constructions.
The annotations associate to the right, and each occurrence receives a fresh
universe instance subject to the required size bounds.
The type coercion interprets the right-hand bundle as its object type, so
`CartCatCartCat : CartCatCartCat` elaborates to `CartCatCartCat : @Ob CartCatCartCat`; similarly for
`GpdGpd`. Import the corresponding `Core` modules to bring the coercions
into scope in clients.

这两个检查直接放在对应构造之后。类型标注按右结合解释，每处取得受所需大小
约束的新宇宙实例。类型强制转换将右侧结构包解释为其对象类型，
因此 `CartCatCartCat : CartCatCartCat` 展开为 `CartCatCartCat : @Ob CartCatCartCat`，
`GpdGpd` 同理。客户端导入相应 `Core` 模块以启用这些强制转换。

## Cartesian categories

## 笛卡尔范畴

[CartCatCat](../theories/Cat/Cartesian/Category.v) has complete `CartCat`
bundles as objects and finite-product-preserving `CartFct` values as arrows.
Its hom equality is natural isomorphism of the underlying functors, retaining
components and their inverses without comparing preservation records.
`CartFctS C D` uses exactly the terminal and product choices stored in `C`.

[CartCatCat](../theories/Cat/Cartesian/Category.v) 的对象为完整 `CartCat`
结构包，态射为保持有限积的 `CartFct` 值。Hom 相等为底层函子的自然同构，
保留分量及其逆，不比较保持性记录。`CartFctS C D` 恰好使用 `C` 保存的
终对象及积选择。

`TerminalCart` is the one-point category, and `ProdCart C D` has the
componentwise finite products of its two parents. `TerminalCartF`,
`FstCartF`, `SndCartF` and `PairCartF` provide the terminal arrow, projections
and product mediator. Their universal properties compare functors by natural
isomorphism. `CartCatCartCat : CartCat` packages these choices over `CartCatCat`
through its single inherited category; importing the module registers no
chosen `HasTerminal` or `HasProduct` model on an unrelated category.

`TerminalCart` 为单点范畴，`ProdCart C D` 逐分量使用两个父结构的有限积。
`TerminalCartF`、`FstCartF`、`SndCartF` 和 `PairCartF` 分别给出终箭头、
两个投影及积中介；其泛性质通过自然同构比较函子。`CartCatCartCat : CartCat`
通过唯一继承范畴，将这些选择连同 `CartCatCat` 打包。导入模块不为无关范畴
注册选定的 `HasTerminal` 或 `HasProduct` 模型。

The universal-property proofs are reusable before bundling:
[Product.Componentwise](../theories/Cat/Product/Componentwise.v) combines
terminal and product candidates in arbitrary product categories;
[Functor.Product](../theories/Cat/Functor/Product.v) combines natural
isomorphisms into a product category. The pointed codiscrete and bundled
product constructions live in
[Cartesian.Construction](../theories/Cat/Cartesian/Construction.v).

泛性质证明在打包前即可复用：
[Product.Componentwise](../theories/Cat/Product/Componentwise.v) 组合任意
乘积范畴中的终候选及积候选；
[Functor.Product](../theories/Cat/Functor/Product.v) 组合到乘积范畴的自然同构。
带点余离散构造及打包乘积位于
[Cartesian.Construction](../theories/Cat/Cartesian/Construction.v)。

## Groupoids and equivalences

## 群胚及等价

[CoreGpd C](../theories/Cat/Groupoid/CoreGpd.v) is the core of any category:
objects stay unchanged, and arrows retain precisely the isomorphisms together
with their chosen inverse data. Hom equality is inherited from `C`, so it
does not compare inverse witnesses. `CoreInclusionF` forgets that data and is
faithful. Specify the ambient category explicitly when the original category
and its core share the same object type.

[CoreGpd C](../theories/Cat/Groupoid/CoreGpd.v) 为任意范畴的核心：对象不变，
态射恰好保留同构及其选定逆数据。Hom 相等继承自 `C`，不比较逆见证。
`CoreInclusionF` 忘掉这些数据且忠实。原范畴与核心共享对象类型时，
客户端须显式指定环境范畴。

[GpdCat](../theories/Cat/Groupoid/Category.v) has groupoids as objects and
ordinary functors as arrows, compared by natural isomorphism. Consequently
`GpdGpd := CoreGpd GpdCat` has groupoid equivalences as arrows: each
carries a quasi-inverse and two natural isomorphisms. This reuses the existing
isomorphism theory rather than defining a second equivalence interface.
`GpdForgetF : Fct GpdGpd CatCat` retains the forward functor.

[GpdCat](../theories/Cat/Groupoid/Category.v) 以群胚为对象、普通函子为态射，
通过自然同构比较函子。因此 `GpdGpd := CoreGpd GpdCat` 的态射为群胚
等价，每条均携带拟逆及两份自然同构。这复用已有同构理论，不另定义一份等价
接口。`GpdForgetF : Fct GpdGpd CatCat` 保留正向函子。

## Checks

## 检查

[StructureUniverses](../tests/category/StructureUniverses.v) checks ordinary product
laws and rewriting, computation with distinct
terminal/product choices on the same category, a nontrivial groupoid
self-equivalence and its selected inverse, and both strict orders of hom and
equality sizes. Products also accept parents with different size profiles.

[StructureUniverses](../tests/category/StructureUniverses.v) 检查普通积定律与重写、
同一范畴上不同终对象／积选择的计算、非平凡群胚自等价及其
选定逆，以及 Hom 与相等大小的两种严格次序。乘积也接受大小配置不同的父结构。
