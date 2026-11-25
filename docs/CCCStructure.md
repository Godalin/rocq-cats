# Basic CCC structure and hom equations

# CCC 基础结构及 Hom 等式

The first structural milestone of [#23](https://github.com/Godalin/rocq-cats/issues/23)
connects exponential identities, their hom-setoid computations, limit preservation,
cartesian closed functor composition and internal composition. The selected
[CCC interface](../theories/Cat/CCC/Core.v) extends a chosen
[cartesian structure](../theories/Cat/Cartesian/Core.v) by exponentials for
its inherited products. The unique underlying-view chain is
`CCC → CartCat → Cat`. Individual theorems use weaker assumptions
where possible; extracting this parent does not add hypotheses to them.

[#23](https://github.com/Godalin/rocq-cats/issues/23) 的首个结构里程碑连接指数恒等、
Hom 广集计算、极限保持性、笛卡尔闭函子复合及内部复合。
[CCC 接口](../theories/Cat/CCC/Core.v) 为选定的
[笛卡尔结构](../theories/Cat/Cartesian/Core.v) 增加相对于继承积的指数，
唯一底层视图链为 `CCC → CartCat → Cat`。各个定理在可行时仍使用
更弱的假设；抽取父结构不为它们增加前提。

Minks packs the underlying category, terminal object, products and
exponentials in `CCC`. The exponential mixin depends on the stored products.
`CCCToCartCat` recovers the cartesian parent from the same selections.

`CCC` 平铺保存底层范畴、终对象、积与指数。指数 Mixin 依赖保存的积，
`CCCToCartCat` 从同一组选择还原笛卡尔父结构。

`CCCFct` extends `CartFct` with `PreservesExp`, the invertibility of the
exponential comparison for the stored cartesian witness. Fixing its functor
exports `IsCCCF`. The generated `CCCFctToIsCCCF` and `CCCFctOfIsCCCF`
extract and reassemble that interface.
`exp_cmp` names the general exponential comparison, and `fct_exp_cmp`
is its cartesian-functor adapter. Other lowercase
functor/exponential identifier segments use `fct`/`exp`; module paths and
`HasExponential` stay unchanged.

`CCCFct` 在 `CartFct` 上增加 `PreservesExp`，即相对于保存的笛卡尔见证的
指数比较可逆性。固定底层函子后导出 `IsCCCF`。生成的 `CCCFctToIsCCCF`
与 `CCCFctOfIsCCCF` 提取、重新打包这份接口。
`exp_cmp` 命名通用指数比较，`fct_exp_cmp` 为其笛卡尔函子适配，其余小写函子／指数标识符
词段使用 `fct`／`exp`；模块路径及 `HasExponential` 不变。

The cartesian and CCC functor modules, product preservation and exponential
comparison now locally default to object notation. Expressions such as
`F (X × Y)` and `fmap F (f × g)` coexist without `%ob` or `%hom`; the latter
uses the existing hom argument scope of `fmap`. These local settings do not
change the importing module's default. See the
[object/morphism notation convention](./CodeStyle.md#object-and-morphism-products--对象积与态射积).

笛卡尔／CCC 函子、积保持及指数比较模块现局部默认使用对象记号，
`F (X × Y)` 与 `fmap F (f × g)` 可不加 `%ob`、`%hom` 地共存，后者沿用
`fmap` 的 Hom 参数作用域。局部设置不改变导入模块的默认解释，详见
[对象／态射记号约定](./CodeStyle.md#object-and-morphism-products--对象积与态射积)。

## CCC modules and the category of CCCs

## CCC 模块及 CCC 的范畴

The theory is organized by mathematical subject:

这条理论按数学主题组织：

| Module / 模块 | Responsibility / 职责 |
| --- | --- |
| [CCC/Core.v](../theories/Cat/CCC/Core.v) | The complete CCC record and inherited choices / 完整 CCC 记录及继承选择 |
| [CCC/Functor.v](../theories/Cat/CCC/Functor.v) | `IsCCCF`, `CCCFct`, its parent view `CCCFctToCartFct`, identity and composition / 保持性、打包函子、父视图及恒等与复合 |
| [CCC/Category.v](../theories/Cat/CCC/Category.v) | `CCCCat`, hom equality and the forgetful functor / CCC 范畴、Hom 相等及忘却函子 |
| [Functor/ExponentialComparison.v](../theories/Cat/Functor/ExponentialComparison.v) | General comparison, evaluation and currying, with weaker hypotheses / 较弱假设下的一般比较、求值及柯里化 |

`CCCCat` has complete `CCC` bundles as objects and `CCCFct C D` as
arrows. `CCCFctEq` compares only their underlying functors by a Type-valued
natural isomorphism. Preservation witnesses remain stored but are not
compared. Identity and composition reuse `IdCCCF` and `CompCCCF`; the
unit/associativity laws reuse the existing natural comparisons for `CompF`.
No native equality of object maps, functors or law records is required.

`CCCCat` 以完整 `CCC` 结构包为对象，以 `CCCFct C D` 为态射；
`CCCFctEq` 只通过 Type 值自然同构比较底层函子，保留但不比较保持性见证。
恒等及复合复用 `IdCCCF`、`CompCCCF`，单位及结合律复用 `CompF` 的
已有自然比较，不要求对象映射、函子或定律记录原生相等。

`CCCForgetF : Fct CCCCat CatCat` keeps the underlying category and functor.
It is faithful for the specified natural-isomorphism equality. Both its
respectfulness and `ccc_forget_faithful` retain the comparison components
and their selected inverses transparently. `CCCCatHom` reuses `CatCatHom`
to admit existing CCC functors with larger auxiliary proof bounds, keeping
object/arrow maps, product witnesses and exponential inverses.

`CCCForgetF : Fct CCCCat CatCat` 保留底层范畴及函子，对指定的自然同构
相等忠实。其保相等性及 `ccc_forget_faithful` 透明保留比较分量及选定逆。
`CCCCatHom` 复用 `CatCatHom`，将辅助证明界较大的已有 CCC 函子装入 Hom，
保留对象／箭头映射、积见证及指数逆。

For each universe profile `o h p l`, `CCCCat` contains CCCs at
`CCC@{o h p l l}` and itself lives at larger bounds. This is a
universe-polymorphic family, not a type containing categories from every
universe. Both strict hom/equality size orders remain supported.
`tests/category/CCCCategory.v` exercises categorical notation and composition
rewriting, distinct terminal choices over one category, concrete forgetting
and the larger auxiliary-bound interface.

每个宇宙配置 `o h p l` 下，`CCCCat` 包含 `CCC@{o h p l l}` 的结构包，
自身位于更大的大小界。这是宇宙多态的一族，不将全部宇宙的范畴放入一个类型。
Hom／相等大小的两种严格次序均保留。`tests/category/CCCCategory.v` 检查普通范畴
记号、复合重写、同一范畴上的不同终对象选择、具体忘却计算及较大辅助界接口。

The object-level universe checks
`Check CatCat : CatCat : CatCat : CatCat` and
`Check CCCCat : CatCat : CatCat : CatCat` now appear immediately below
their constructions
in `Cat.CatCat` and `Cat.CCC.Category`. They use the object-type coercion
and distinct universe instances; the latter does not assert a CCC structure
on CCCCat. At published checkpoint `70792e0`, local validation passed all
606 theory and 174 test modules, followed by the affected test after adding
the original two probes. The 23 temporary universe, assumption and
witness-computation checks are closed.

两个对象级宇宙检查
`Check CatCat : CatCat : CatCat : CatCat`、
`Check CCCCat : CatCat : CatCat : CatCat`
现直接放在 `Cat.CatCat`、`Cat.CCC.Category` 的对应构造下方，使用对象类型
强制转换及不同宇宙实例；后者不声称 CCCCat 自身具有 CCC 结构。已发布检查点
`70792e0` 本地通过全部 606 个理论及 174 个测试模块，随后补验新增原两个
检查的测试文件；二十三项临时宇宙、假设及见证计算检查全部闭合。

For self-membership within a complete cartesian structure, use
`CartCatCartCat : CartCatCartCat`; groupoids admit the analogous
`GpdGpd : GpdGpd`. See the
[constructions and universe distinction](./StructureUniverses.md).

完整笛卡尔结构内的自身成员关系使用 `CartCatCartCat : CartCatCartCat`；
群胚有对应的 `GpdGpd : GpdGpd`。
[构造及宇宙区别](./StructureUniverses.md)另行说明。

## Classical isomorphisms

## 经典同构

[Exponential.Laws](../theories/Cat/Exponential/Laws.v) provides:

[Exponential.Laws](../theories/Cat/Exponential/Laws.v) 提供：

| Isomorphism / 同构 | Construction / 构造 |
| --- | --- |
| `(X × Y)^A ≅ X^A × Y^A` | `exp_product_iso A X Y` |
| `(Y^A)^B ≅ Y^(A × B)` | `exp_iterated_iso A B Y` |
| `Y^1 ≅ Y` | `exp_unit_iso Y` |
| `1^A ≅ 1` | `exp_terminal_iso A` |

The product and terminal-result isomorphisms come from the existing
product–exponential adjunction and the general right-adjoint preservation
theorem. The product comparison has exponentiated projections as components;
its inverse abstracts paired evaluations. Both curry and evaluation equations
are public. Only the two unit laws need a terminal object.

积同构及终结果同构来自已有积／指数伴随与一般右伴随保持定理。
积比较的分量为取指数后的投影，其逆抽象配对后的求值；柯里化及求值方程都提供
公共接口。仅两条单位规律需要终对象。

The product comparison is a natural isomorphism in both result factors.
The iterated comparison is natural in the result object; its hom maps are also
natural in the context. Evaluation at the terminal argument is naturally the
identity. These statements retain explicit component arrows and inverses.

积比较在两个结果因子上为自然同构。迭代比较在结果对象上自然，其 Hom 映射也在
上下文上自然。终参数处的求值自然同构于恒等函子。这些陈述都保留显式分量箭头
及其逆。

## Iterated transposition

## 迭代转置

[Exponential.Currying](../theories/Cat/Exponential/Currying.v) supplies
`ƛ₂ f` and `g^♭₂`. Their types and equations are:

[Exponential.Currying](../theories/Cat/Exponential/Currying.v) 提供
`ƛ₂ f` 及 `g^♭₂`，其类型与方程为：

```text
f : Hom (Z × (A × B)) Y
ƛ₂ f : Hom Z ((Y^A)^B)

g : Hom Z ((Y^A)^B)
g^♭₂ : Hom (Z × (A × B)) Y

(ƛ₂ f)^♭₂ ≈ f
ƛ₂ (g^♭₂) ≈ g
(g ∘ σ)^♭₂ ≈ g^♭₂ ∘ (σ × id)
```

[Product.Transport](../theories/Cat/Product/Transport.v) constructs the explicit
associator and the permutation `((Z × B) × A) ≅ Z × (A × B)`, with forward and
inverse naturality. This accounts for the argument order rather than treating
product objects as definitionally equal. Flattening/expanding the hom maps
are inverse, respectful and natural; their action is the iterated isomorphism.

[Product.Transport](../theories/Cat/Product/Transport.v) 构造显式结合同构及
置换 `((Z × B) × A) ≅ Z × (A × B)`，并证明正向及逆向自然性。
它们负责参数顺序，不要求积对象定义相等。Hom 映射的展平与展开互逆、保相等且
自然，其作用就是迭代同构。

## Equations and native hom-setoids

## 等式及原生 Hom 广集

The following interfaces avoid unfolding universal-property witnesses during
routine calculations. All equalities are the designated setoid/hom equality.

下列接口使日常计算无需展开泛性质见证。所有相等均为指定广集／Hom 相等。

| Interface / 接口 | Use / 用途 |
| --- | --- |
| [`iso_cancel_l`, `iso_cancel_r`](../theories/Cat/Isomorphism.v) | Cancel an invertible composite / 消去可逆复合 |
| [`iso_move_l`, `iso_move_r`](../theories/Cat/Isomorphism.v) | Move an isomorphism across an equation / 同构移项 |
| [`product_eq_iff`](../theories/Cat/Product/Transport.v) | Split an equation into projection equations / 将等式拆成投影等式 |
| [`exp_curry_iff`](../theories/Cat/Exponential/Core.v) | `ƛ f ≈ g ↔ f ≈ uncurry g` |
| [`exp_curry_eq_iff`, `exp_uncurry_eq_iff`](../theories/Cat/Exponential/Core.v) | Detect equations before/after transposition / 在转置前后检测等式 |
| [`exp_uncurry_app`](../theories/Cat/Exponential/Core.v) | Express uncurrying by contextual application / 以上下文应用表达反柯里化 |

[ProductHom](../theories/Instance/Set/ProductHom.v) and
[ExponentialHom](../theories/Instance/Set/ExponentialHom.v) package the actual
respectful maps as native hom-setoid isomorphisms:

[ProductHom](../theories/Instance/Set/ProductHom.v) 与
[ExponentialHom](../theories/Instance/Set/ExponentialHom.v) 将实际保相等映射组织为
原生 Hom 广集同构：

```text
HomSet Z (X × Y) ≅[SetCat] (HomSet Z X ×S HomSet Z Y)
HomSet (Z × X) Y ≅[SetCat] HomSet Z (Y^X)
HomSet Z ((Y^A)^B) ≅[SetCat] HomSet Z (Y^(A × B))
```

These interfaces use `SetCat` to express setoid isomorphisms without activating
a chosen CCC model. The general `hom_iso` in [Hom](../theories/Instance/Set/Hom.v) changes
source and target by isomorphisms through the existing Hom bifunctor.

这些接口使用 `SetCat` 表达广集同构，不启用选定 CCC 模型。
[Hom](../theories/Instance/Set/Hom.v) 中的一般
`hom_iso` 通过已有 Hom 双函子，沿同构变换源及目标。

## Limits and functor composition

## 极限及函子复合

[Limit.Exponential](../theories/Cat/Limit/Exponential.v) applies the existing
right-adjoint theorem to each specified limiting cone. Terminal, product,
equalizer and pullback preservation reuse their existing limit characterizations.
Equalizer/pullback theorems take the candidate universal property as an argument.
The source only needs chosen products and exponentials; shape sizes remain
independent of its hom carrier/equality levels.

[Limit.Exponential](../theories/Cat/Limit/Exponential.v) 对每个指定极限锥应用
已有右伴随定理；终对象、积、等化子及拉回保持性复用已有极限刻画。
等化子／拉回定理以候选泛性质为参数。源范畴只需要选定积及指数，形状大小与
其 Hom 载体／相等层级保持独立。

[Functor.Cartesian](../theories/Cat/Functor/Cartesian.v) first extends preservation
of the selected terminal/product objects to arbitrary candidates using their
universal isomorphisms. This gives `CompF_IsCartF` and the inverse-product
comparison equation. [CCC.Functor](../theories/Cat/CCC/Functor.v) proves:

[Functor.Cartesian](../theories/Cat/Functor/Cartesian.v) 先通过泛同构，将选定
终对象／积的保持性推广到任意候选，进而得到 `CompF_IsCartF` 及逆向积比较
的复合方程。[CCC.Functor](../theories/Cat/CCC/Functor.v) 证明：

```text
comparison_(G∘F)(X,Y) ≈ comparison_G(FX,FY) ∘ G(comparison_F(X,Y))
```

Invertibility then supplies `CompF_IsCCCF`. Terminal comparison composition is
already terminal-arrow uniqueness. All chosen structures and preservation
proofs remain explicitly enabled.

可逆性随后给出 `CompF_IsCCCF`。终比较的复合已由终箭头唯一性保证。
所有选定结构及保持证明仍须显式启用。

## Bundled preservation

## 打包保持性

[CartFct](../theories/Cat/Functor/Cartesian.v) stores one underlying
`Fct` and its `IsCartF` evidence for named source terminal and product
structures. No chosen target products are needed until an operation uses them.
[CCCFct](../theories/Cat/CCC/Functor.v) adds invertibility of the canonical
exponential comparison to that same cartesian bundle. Its unique coercion chain
is `CCCFct → CartFct → Fct`; the derived `CCCFctToIsCCCF`
instance reuses the stored cartesian witnesses.

[CartFct](../theories/Cat/Functor/Cartesian.v) 保存一个底层 `Fct`
及其相对于具名来源终对象和积结构的 `IsCartF` 证据；仅在运算实际需要时
才引入目标选定积。[CCCFct](../theories/Cat/CCC/Functor.v) 在同一个
笛卡尔包上增加规范指数比较的可逆性。唯一强制转换链为
`CCCFct → CartFct → Fct`；派生实例 `CCCFctToIsCCCF`
复用保存的笛卡尔见证。

`MakeCartFct` and `CCCFctOfIsCCCF` package
existing evidence transparently. `IdCartF`, `CompCartF`, `IdCCCF`
and `CompCCCF` reuse the identity and composition theorems above. Clients can
write `F X`, `fmap F f` and apply the existing comparison/curry laws directly.
The fixed-functor interfaces remain available to general theorems and STLC
clients; constructors do not register chosen model functors globally.

`MakeCartFct` 及 `CCCFctOfIsCCCF` 透明地
打包已有证据。`IdCartF`、`CompCartF`、`IdCCCF`、`CompCCCF` 复用
上述恒等和复合定理。客户端可直接写 `F X`、`fmap F f` 并应用已有比较／
柯里化定律。固定函子接口继续服务于一般定理和 STLC 客户端；构造器不会全局
注册选定模型函子。

## Internal hom equations

## 内部 Hom 等式

[Exponential.InternalHom](../theories/Cat/Exponential/InternalHom.v) supplies
`idᴱ[X]` and contextual composition `g ∘ᴱ f`. Their application, context
substitution, left/right unit and associativity equations follow from
transposition. The internal arrow `internal_comp X Y Z` has type
`Hom ((Z^Y) × (Y^X)) (Z^X)`. Its associativity diagram includes the explicit
product associator; unit diagrams use the two projection unitors. Internal
identities work in any context; specializing to the terminal context gives
`1 → X^X`.

[Exponential.InternalHom](../theories/Cat/Exponential/InternalHom.v) 提供
`idᴱ[X]` 及上下文复合 `g ∘ᴱ f`，应用、上下文替换、左右单位及结合方程均来自
转置。内部箭头 `internal_comp X Y Z` 的类型为
`Hom ((Z^Y) × (Y^X)) (Z^X)`。其结合图包含显式积结合同构，单位图使用两个
投影单位同构。内部恒等适用于任意上下文，特化为终上下文即得到 `1 → X^X`。

## Validation and remaining extensions

## 验证及后续扩展

Permanent [universe/interface checks](../tests/Universes.v) cover both hom/equality
orderings, native hom correspondences, exported notation, mixed-level CCC
functor composition and limit preservation for larger shapes. Concrete
proof-relevant setoid computations and assumption audits remain temporary.

永久[宇宙／接口检查](../tests/Universes.v) 覆盖两种 Hom／相等排列、原生 Hom
对应、公共记号、不同层级的 CCC 函子复合及更大形状上的极限保持性。
带额外相等见证的具体广集计算及公理审计仍作为临时检查。

On Rocq 9.0.1, OCaml 5.3.0 and Nix Dune 3.23.1, the full build, test and
install targets pass. Eleven additional permanent checks cover the interfaces
above. The temporary audit covers 155 declarations, all closed under the global
context. Fourteen temporary computations check the actual comparison arrows,
argument order, native hom maps and internal composition on a setoid with boolean
equality witnesses. Thirteen coqdoc pages were generated and parsed successfully.
These are local results.

在 Rocq 9.0.1、OCaml 5.3.0 与 Nix Dune 3.23.1 下，完整构建、测试及安装目标通过。
新增 11 项永久检查覆盖上述接口。临时审计覆盖 155 项声明，均无额外假设。
14 项临时计算在相等见证为布尔值的广集上，检查实际比较箭头、参数顺序、原生
Hom 映射及内部复合。13 个 coqdoc 页面生成并解析通过。这些结果属于本地验证。

The bundled-functor follow-up also passes the full build, test and install
targets with the same toolchain. Added interface, computation and universe
regressions cover inheritance, explicit selection, transparent composite
inverses and separated STLC interpretation adapters. Its seven new adapters,
identity/composition constructors and inherited instance are closed under the
global context. Strict bilingual HTML export checked 507 pages.

打包函子后续工作也在同一工具链下通过完整构建、测试及安装目标。新增接口、
计算及宇宙回归覆盖继承、显式选择、透明的复合逆及分离层级的 STLC 解释适配。
七项新增适配器、恒等／复合构造及继承实例均无额外假设；严格双语 HTML 导出
检查了 507 页。

The independent follow-ups in #23 are transfer of chosen CCC structures across
arbitrary category equivalences and packaging self-enrichment through the general
interface of #10. The basic exponential, preservation, composition and internal
hom equations above are available without those developments.

#23 中独立的后续工作为沿任意范畴等价运输选定 CCC 结构，以及通过 #10 的一般
接口组织自富集。上述基础指数、保持性、复合及内部 Hom 方程已可独立使用。
