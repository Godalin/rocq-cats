# Basic CCC structure and hom equations

# CCC 基础结构及 Hom 等式

The first structural milestone of [#23](https://github.com/Godalin/rocq-cats/issues/23)
connects exponential identities, their hom-setoid computations, limit preservation,
cartesian closed functor composition and internal composition. The selected
[CCC interface](../theories/Cat/CCC.v) remains the small assembly of terminal,
product and exponential structures. Individual theorems use weaker assumptions
where possible.

[#23](https://github.com/Godalin/rocq-cats/issues/23) 的首个结构里程碑连接指数恒等、
Hom 广集计算、极限保持性、笛卡尔闭函子复合及内部复合。
[CCC 接口](../theories/Cat/CCC.v) 仍然只是终对象、积和指数结构的小型组合；
各个定理在可行时使用更弱的假设。

## Classical isomorphisms

## 经典同构

[Exponential.Laws](../theories/Cat/Exponential/Laws.v) provides:

[Exponential.Laws](../theories/Cat/Exponential/Laws.v) 提供：

| Isomorphism / 同构 | Construction / 构造 |
| --- | --- |
| `(X × Y)^A ≅ X^A × Y^A` | `exponential_product_iso A X Y` |
| `(Y^A)^B ≅ Y^(A × B)` | `exponential_iterated_iso A B Y` |
| `Y^1 ≅ Y` | `exponential_unit_iso Y` |
| `1^A ≅ 1` | `exponential_terminal_iso A` |

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
| [`exponential_curry_iff`](../theories/Cat/Exponential/Core.v) | `ƛ f ≈ g ↔ f ≈ uncurry g` |
| [`exponential_curry_eq_iff`, `exponential_uncurry_eq_iff`](../theories/Cat/Exponential/Core.v) | Detect equations before/after transposition / 在转置前后检测等式 |
| [`exponential_uncurry_app`](../theories/Cat/Exponential/Core.v) | Express uncurrying by contextual application / 以上下文应用表达反柯里化 |

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
universal isomorphisms. This gives `CompF_IsCartesianF` and the inverse-product
comparison equation. [Functor.Closed](../theories/Cat/Functor/Closed.v) proves:

[Functor.Cartesian](../theories/Cat/Functor/Cartesian.v) 先通过泛同构，将选定
终对象／积的保持性推广到任意候选，进而得到 `CompF_IsCartesianF` 及逆向积比较
的复合方程。[Functor.Closed](../theories/Cat/Functor/Closed.v) 证明：

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

[CartesianFunctor](../theories/Cat/Functor/Cartesian.v) stores one underlying
`Functor` and its `IsCartesianF` evidence for named source terminal and product
structures. No chosen target products are needed until an operation uses them.
[CCCFunctor](../theories/Cat/Functor/Closed.v) adds invertibility of the canonical
exponential comparison to that same cartesian bundle. Its unique coercion chain
is `CCCFunctor → CartesianFunctor → Functor`; the derived `CCCFunctor_IsCCCF`
instance reuses the stored cartesian witnesses.

[CartesianFunctor](../theories/Cat/Functor/Cartesian.v) 保存一个底层 `Functor`
及其相对于具名来源终对象和积结构的 `IsCartesianF` 证据；仅在运算实际需要时
才引入目标选定积。[CCCFunctor](../theories/Cat/Functor/Closed.v) 在同一个
笛卡尔包上增加规范指数比较的可逆性。唯一强制转换链为
`CCCFunctor → CartesianFunctor → Functor`；派生实例 `CCCFunctor_IsCCCF`
复用保存的笛卡尔见证。

`CartesianFunctorFromPreservation` and `CCCFunctorFromPreservation` package
existing evidence transparently. `IdCartesianF`, `CompCartesianF`, `IdCCCF`
and `CompCCCF` reuse the identity and composition theorems above. Clients can
write `F X`, `fmap F f` and apply the existing comparison/curry laws directly.
The fixed-functor interfaces remain available to general theorems and STLC
clients; constructors do not register chosen model functors globally.

`CartesianFunctorFromPreservation` 及 `CCCFunctorFromPreservation` 透明地
打包已有证据。`IdCartesianF`、`CompCartesianF`、`IdCCCF`、`CompCCCF` 复用
上述恒等和复合定理。客户端可直接写 `F X`、`fmap F f` 并应用已有比较／
柯里化定律。固定函子接口继续服务于一般定理和 STLC 客户端；构造器不会全局
注册选定模型函子。

## Transport across specified equivalences

## 沿指定等价运输

[Equivalence.CCC](../theories/Cat/Equivalence/CCC.v) explicitly constructs
`EquivalenceCCC e HC` for a specified `e : C ≃C D` and `HC : CCC C`.
It also exposes the general `QuasiInverseCCC F G u v HC`, where
`u : G ∘F F ≅N IdF` and `v : F ∘F G ≅N IdF`. The latter preserves
independent native hom/equality universes of the two categories. The supplied
isomorphisms need not satisfy triangle equations; no additional choice,
function equality or proof-field equality is assumed.

[Equivalence.CCC](../theories/Cat/Equivalence/CCC.v) 对指定的
`e : C ≃C D` 及 `HC : CCC C` 显式构造 `EquivalenceCCC e HC`，并提供一般
版本 `QuasiInverseCCC F G u v HC`，其中 `u : G ∘F F ≅N IdF`、
`v : F ∘F G ≅N IdF`。一般版本保持两侧原生 Hom／相等宇宙独立。
给定同构无须满足三角方程，也不假设额外选择、函数相等或证明字段相等。

The construction has reusable prerequisites rather than model-specific proofs:

构造通过可复用前置理论完成，不依赖具体模型证明：

1. [Equivalence.Core](../theories/Cat/Equivalence/Core.v) derives full
   faithfulness and specified object representatives from the quasi-inverse
   isomorphisms. [Equivalence.Adjunction](../theories/Cat/Equivalence/Adjunction.v)
   builds both adjunction directions from actual full preimages.
2. [Limit.Equivalence](../theories/Cat/Limit/Equivalence.v) reuses right-adjoint
   limit preservation and diagram-isomorphism transport for every specified
   shape; fully faithful reflection needs no essential surjectivity.
   [Equivalence.Cartesian](../theories/Cat/Equivalence/Cartesian.v) specializes
   this to empty and pair-shaped limits, choosing terminal objects and products
   independently.
3. [Functor.Product](../theories/Cat/Functor/Product.v) extracts product
   comparison maps and naturality without terminal assumptions; the existing
   cartesian-functor interface delegates to it.
   [Exponential.Preservation](../theories/Cat/Exponential/Preservation.v)
   reflects exponential candidates under fully faithful product-preserving
   functors, and preserves them when essential surjectivity is also specified.

1. [Equivalence.Core](../theories/Cat/Equivalence/Core.v) 从拟逆同构导出全忠实性
   及指定对象代表；[Equivalence.Adjunction](../theories/Cat/Equivalence/Adjunction.v)
   由实际满性原像构造两个方向的伴随。
2. [Limit.Equivalence](../theories/Cat/Limit/Equivalence.v) 对任意指定形状复用
   右伴随极限保持性及图式同构运输；全忠实反映不要求本质满性。
   [Equivalence.Cartesian](../theories/Cat/Equivalence/Cartesian.v) 将其特化为
   空形状及对象对形状的极限，分别选择终对象及积。
3. [Functor.Product](../theories/Cat/Functor/Product.v) 抽取不要求终对象的积比较
   及自然性，原笛卡尔函子接口委托它实现。
   [Exponential.Preservation](../theories/Cat/Exponential/Preservation.v) 在
   全忠实且保持积的函子下反映指数候选；加入指定本质满性后也保持指数。

The transported choices have these underlying objects:

运输选择具有以下底层对象：

```text
T_D       := F T_C
X ×_D Y   := F (G X ×_C G Y)
Y ^_D X   := F (G Y ^_C G X)
```

For `E := G Y ^ G X`, evaluation is lifted through the fully faithful `G`.
Its image is source evaluation after `u E` and the forward product comparison.
The exponential universal property follows by changing its representing object
along `u E`, then reflecting it through `G`. All mediators remain transparent.
`EquivalenceCCCF e HC` and `EquivalenceInverseCCCF e HC` bundle the two
preserving functors. More generally `QuasiInverseIsCCCF` preserves any specified
CCC choices on both sides: exponential candidate uniqueness makes the usual
canonical comparison invertible. Existing product-comparison, evaluation and
curry laws apply directly to these bundles.

令 `E := G Y ^ G X`，求值通过全忠实 `G` 提升；其像为来源求值与 `u E` 及正向
积比较的复合。指数泛性质先沿 `u E` 更换表示对象，再经 `G` 反映得到；所有
中介保持透明。`EquivalenceCCCF e HC` 及 `EquivalenceInverseCCCF e HC` 打包
两个保持函子。更一般的 `QuasiInverseIsCCCF` 保持两侧任意指定 CCC 选择：
指数候选唯一性使通常的规范比较可逆。已有积比较、求值及柯里化定律可直接用于
这些函子包。

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

The specified-equivalence transfer passed
`opam exec --switch=rocq-cats -- dune build @all @runtest @install tests/CCCTransport.vo`
with Rocq/Stdlib 9.2.0, OCaml 5.3.0 and Dune 3.23.1.
The dedicated [CCCTransport regressions](../tests/CCCTransport.v) retain explicit
selection, both strict hom/equality universe orders, and transparent product,
evaluation, curry and inverse-comparison computations through double opposition.
The shared test files and alias are unchanged; the dedicated target is included
by `@all` and can also be built explicitly as above.

指定等价运输已在 Rocq/Stdlib 9.2.0、OCaml 5.3.0、Dune 3.23.1 下通过
`opam exec --switch=rocq-cats -- dune build @all @runtest @install tests/CCCTransport.vo`。
专用 [CCCTransport 回归](../tests/CCCTransport.v) 保留显式选择、两种严格
Hom／相等宇宙排列，以及经过双重反范畴的积、求值、柯里化和比较逆计算。
共享测试文件及别名未改；专用目标由 `@all` 包含，也可按上文显式构建。

All 58 temporary assumption checks are closed under the global context.
Temporary checks also cover larger indexing categories, quasi-inverse data
whose original triangle fails, and a redundant-object presentation of setoids
with Boolean equality witnesses. In the last check the chosen representative
has a different object tag, while evaluation, curry and inverse comparisons
compute. Strict bilingual HTML export produced 263 modules per language and
checked links/anchors in 531 pages. These are local task results; audit scripts
are not compiled regression sources, and batch PDFs are left to integration.

全部 58 项临时公理检查均无额外假设。临时检查还覆盖更大的索引范畴、原始三角律
不成立的拟逆数据，以及相等见证为布尔值的广集的重复对象呈现；后者的选定代表
具有不同对象标签，求值、柯里化及比较逆仍计算。严格双语 HTML 导出为每种语言
生成 263 个模块，并检查 531 页的链接及锚点。这些是任务本地结果；审计脚本
不是编译回归源码，批次 PDF 留待集成阶段导出。

The specified-equivalence transfer is implemented on `ccc-equivalence-23`,
based on integrated `a7c849423f6f03193c82d5f6bb20230acf63d0a0`. Its general
foundation was delivered separately in `c7007e9`. The remaining independent
follow-up in #23 is packaging self-enrichment through the general interface
of #10. STLC client migration remains a separate task.

指定等价运输已在 `ccc-equivalence-23` 上实现，基于集成版本
`a7c849423f6f03193c82d5f6bb20230acf63d0a0`；一般基础已作为 `c7007e9` 独立交付。
#23 剩余的独立后续工作是通过 #10 的一般接口组织自富集。STLC 客户端迁移仍是
独立任务。
