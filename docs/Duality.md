# Dual constructions and their ordinary interfaces

# 对偶构造及其通常接口

## One underlying construction

## 只保留一份底层构造

A dual construction uses the original theory on opposite categories. Ordinary
names, notation and arrow directions form an interface to that construction;
there is no independently rebuilt dual object and subsequent comparison theorem.
This rule is recorded in [AGENTS.md](../AGENTS.md).

对偶构造直接使用反范畴中的原理论。通常的名称、记号与箭头方向只构成该构造的
使用接口；不独立重建余对象，也不再证明两套构造的比较定理。
这一原则已记入 [AGENTS.md](../AGENTS.md)。

## Cocones

## 余锥

[Diagram.Dual](../theories/Cat/Diagram/Dual.v) stores a cocone `D ⇒∇ X`
through one field, `op_cone : Cone (D^opF) X`. `CoconeN` reads its legs
as the ordinary natural transformation `D ⇒ ConstF J X` and is a coercion,
so components and pointwise equality still use the ordinary interface.
`CoconeOfN` supplies ordinary natural-transformation data to this representation.
Neither adapter introduces a second cocone structure or universal property.

[Diagram.Dual](../theories/Cat/Diagram/Dual.v) 的余锥 `D ⇒∇ X`
只存储一个字段 `op_cone : Cone (D^opF) X`。`CoconeN` 将锥腿读作通常的
自然变换 `D ⇒ ConstF J X`，并作为强制转换，使分量及逐点相等继续使用通常接口。
`CoconeOfN` 将通常自然变换的数据送入该表示；两者都不引入第二种余锥结构或泛性质。

Postcomposition `f ∘Cocone κ` is opposite-cone precomposition. The action
`κ ∘∇ α` of a diagram transformation uses its opposite transformation and
the original vertical composition. `MapCocone F κ` uses `MapCone (F^opF)`
and the existing composition comparison. Laws reuse their original counterparts.
`CoconeCat D` and `CoconeApexF` likewise come from the cone category and apex
functor by opposition. A cocone is represented there by `(X; op_cone κ)`.

后合成 `f ∘Cocone κ` 就是反锥的预合成。图式自然变换的作用 `κ ∘∇ α`
使用其反变换及原来的垂直复合。`MapCocone F κ` 使用 `MapCone (F^opF)`
及已有复合比较；定律复用原来的对应定律。
`CoconeCat D` 与 `CoconeApexF` 同样由锥范畴及顶点函子取反得到，
余锥在其中表示为 `(X; op_cone κ)`。

## Colimits

## 余极限

[Colimit.Core](../theories/Cat/Colimit/Core.v) defines
`is_colimit κ := is_limit (op_cone κ)`. `HasColimit C D` contains only
`hasOpLimit : HasLimit (C^op) (D^opF)`. Object `colim D`, injections
`ιcolim[D]`, mediator `colim⟨κ⟩` and their universal laws read the original
limit data and theorems; the data are not reconstructed in a parallel record.

[Colimit.Core](../theories/Cat/Colimit/Core.v) 定义
`is_colimit κ := is_limit (op_cone κ)`。`HasColimit C D` 只包含
`hasOpLimit : HasLimit (C^op) (D^opF)`。对象 `colim D`、注入 `ιcolim[D]`、
中介 `colim⟨κ⟩` 及其泛性质定律直接读取原极限的数据与定理，
不在另一套平行记录中重建这些数据。

`HasColimitsOfShape C J` contains only the original selected structure
`HasLimitsOfShape (C^op) (J^op)`. `ColimitF` is constructed by taking the
opposite of `LimitF ∘F OpFctF` and adapting the double-opposite endpoints.
Its identity, composition and respectfulness are inherited functor laws.
Importing the modules does not choose any model structures.

`HasColimitsOfShape C J` 只包含原选定结构
`HasLimitsOfShape (C^op) (J^op)`。`ColimitF` 由 `LimitF ∘F OpFctF`
取反后适配双重反范畴端点得到；恒等、复合与保相等性直接继承已有函子律。
导入模块不会为具体模型选择结构。

## Adjunction and preservation interfaces

## 伴随与保持性接口

[Colimit.Adjunction](../theories/Cat/Colimit/Adjunction.v) exposes
`ColimitF ⊣ Δ[J,C]`. Its two hom maps are the inverse and forward maps of
the original opposite-limit adjunction, read at the ordinary endpoints.
The inverse and naturality laws use the original adjunction laws. Conversely,
`adjunction_unit_universal` supplies the stored opposite limit directly.
It is not necessary to prove a separate colimit mediator uniqueness theorem.

[Colimit.Adjunction](../theories/Cat/Colimit/Adjunction.v) 提供
`ColimitF ⊣ Δ[J,C]`。两个 Hom 映射是原反范畴极限伴随的逆、正向映射，
读回通常端点；互逆律及自然性使用原伴随定律。反向构造由
`adjunction_unit_universal` 直接给出存储的反范畴极限，无须另证余极限中介唯一性。

For arbitrary opposite-shape diagrams, `UnopF` reads a functor between
opposite categories in the original categories. `OpUnopF` supplies the
identity-component comparison back to the original diagram.
[TransportedLimit](../theories/Cat/Limit/Transport.v) reuses the existing
limit-transport theorem to expose the selected structure at that endpoint.
These are general functor/limit adapters, rather than duplicate dual constructions.

对于任意反形状图式，`UnopF` 将反范畴之间的函子读回原范畴，`OpUnopF`
提供返回原图式的恒等分量比较。
[TransportedLimit](../theories/Cat/Limit/Transport.v) 复用已有极限运输定理，
在该端点提供选定结构。它们是通用函子／极限适配，不是独立重建的对偶构造。

[Colimit.Preservation](../theories/Cat/Colimit/Preservation.v) directly
uses `right_adjoint_preserves_limit` with `OpAdjunction` on the stored cone,
then the composition comparison already used by `MapCocone`. The input
assumption is only that the specified source cocone is colimiting.

[Colimit.Preservation](../theories/Cat/Colimit/Preservation.v) 将
`OpAdjunction` 与 `right_adjoint_preserves_limit` 直接用于存储的锥，
再使用 `MapCocone` 中同一个复合比较；输入只要求指定源余锥为余极限。

## Named constructions and their shapes

## 命名构造及其形状

[Terminal](../theories/Cat/Terminal.v),
[Coproduct](../theories/Cat/Coproduct/Core.v) and
[Coequalizer](../theories/Cat/Coequalizer.v) expose `HasInitial`,
`HasCoproduct` and `HasCoequalizer`. Each contains just the selected terminal,
product or equalizer structure on `C^op`. Their candidate `is_*` properties
are the original properties on `C^op`. Ordinary maps `¡`, `ι1`, `ι2`,
`⦗f,g⦘`, `πcoeq[f,g]` and `coeq⟨q,H⟩` read the original maps directly.
Objects are written `0`, `X ⊔ Y` and `Coeq[f,g]`.

[Terminal](../theories/Cat/Terminal.v)、
[Coproduct](../theories/Cat/Coproduct/Core.v) 与
[Coequalizer](../theories/Cat/Coequalizer.v) 提供 `HasInitial`、
`HasCoproduct` 与 `HasCoequalizer`，各自仅包含 `C^op` 上选定的终对象、积或
等化子结构；候选 `is_*` 性质就是 `C^op` 上的原性质。通常映射 `¡`、`ι1`、
`ι2`、`⦗f,g⦘`、`πcoeq[f,g]` 与 `coeq⟨q,H⟩` 直接读取原映射；
对象写作 `0`、`X ⊔ Y` 与 `Coeq[f,g]`。

Mediator uniqueness, β/η, respectfulness and composition laws reuse the
original laws. In particular, coequalizer respectfulness compares arrows
without comparing their commutativity witnesses. Initial-object model
construction now supplies its original opposite-terminal data through the
named field `hasOpTerminal`; importing it still makes no model choice.

中介唯一性、β/η、保相等性及复合律均复用原定律。尤其是余等化子的保相等性
比较箭头而不比较交换性见证。始对象模型现在通过具名字段 `hasOpTerminal`
提供原反范畴终对象数据；导入仍不会自动选择具体模型结构。

| Construction / 构造 | Colimit shape / 余极限形状 | Characterization / 刻画 |
| --- | --- | --- |
| Initial / 始对象 | `EmptyShape^op` | [`initial_iff_empty_colimit`](../theories/Cat/Colimit/Initial.v) |
| Binary coproduct / 二元余积 | `PairShape^op` | [`coproduct_iff_colimit`](../theories/Cat/Colimit/Coproduct.v) |
| Coequalizer / 余等化子 | `ParallelShape^op` | [`coequalizer_iff_colimit`](../theories/Cat/Colimit/Coequalizer.v) |
| Pushout / 推出 | `SpanShape` | [`pushout_iff_colimit`](../theories/Cat/Colimit/Pushout.v) |

The opposite of a discrete pair is still discrete. In the opposite parallel
shape, the arrows run from `true` to `false`, so the coequalizer projection
is the cocone's `false` component. [Diagram.DualShape](../theories/Cat/Diagram/DualShape.v)
offers `EmptyCodiagram`, `⟨X,Y⟩CoD`, `⟨f ⇉ g⟩CoD` and the corresponding
`EmptyCocone`, `PairCocone`, `ParallelCocone`, obtained from the original
diagrams and cones through the shared `DualDiagram`/`DualCone` adapters.

离散二点形状取反后仍然离散。反平行箭头形状中的箭头从 `true` 指向 `false`，
所以余等化子投影为余锥的 `false` 分量。
[Diagram.DualShape](../theories/Cat/Diagram/DualShape.v) 提供
`EmptyCodiagram`、`⟨X,Y⟩CoD`、`⟨f ⇉ g⟩CoD` 及对应的
`EmptyCocone`、`PairCocone`、`ParallelCocone`，均由原图式及锥经共用的
`DualDiagram`／`DualCone` 适配得到。

[Colimit.Shape](../theories/Cat/Colimit/Shape.v) restricts the stored
double-opposite cone along `ToDoubleOpF`. This functor is full and essentially
surjective with identity preimages and representative isomorphisms. The
existing limit reindexing theorem then permits direct use of the original
terminal/product/equalizer limit characterizations. Selected structures
convert in both directions through the same reindexing theory; there is no
claim that round-trip selected records are equal. Left-adjoint preservation
likewise applies original right-adjoint preservation to `OpAdjunction`.

[Colimit.Shape](../theories/Cat/Colimit/Shape.v) 沿 `ToDoubleOpF` 限制
存储的双重反锥。该函子以恒等原像和恒等代表同构具有满性及本质满性，因而已有
极限重索引定理允许直接使用原终对象／积／等化子的极限刻画。选定结构的双向
转换也经过同一重索引理论，不声称往返后的选定记录相等。左伴随保持性同样将
原右伴随保持定理用于 `OpAdjunction`。

## Pushouts and finite-colimit bases

## 推出与有限余极限基础

[Pushout](../theories/Cat/Pushout.v) stores only
`hasOpPullback : HasPullback (C^op)`. The ordinary object `X ⊔[f,g] Y`,
injections `ιpo1[f,g]`, `ιpo2[f,g]` and mediator `po⟨i,j,H⟩` are the original
opposite pullback data. Its universal property, β/η, respectfulness, witness
independence, uniqueness and square pasting reuse the original theorems.
Pullback uniqueness is transparent so that its inherited isomorphism arrows
remain computational.

[Pushout](../theories/Cat/Pushout.v) 只存储
`hasOpPullback : HasPullback (C^op)`。通常对象 `X ⊔[f,g] Y`、注入
`ιpo1[f,g]`、`ιpo2[f,g]` 及中介 `po⟨i,j,H⟩` 就是原反范畴拉回数据。
泛性质、β/η、保相等性、见证独立性、唯一性及方形粘合均复用原定理。
拉回唯一性保持透明，使继承的同构箭头仍可计算。

[Colimit.Pushout](../theories/Cat/Colimit/Pushout.v) characterizes arbitrary
span cocones, converts chosen pushouts and span colimits in both directions,
and exposes left-adjoint preservation. `SpanShape` is `CospanShape^op`;
`SpanCocone i j H` uses the shared `DualCone` adapter. These constructions
reuse the same shape-reindexing bridge as the other named colimits.

[Colimit.Pushout](../theories/Cat/Colimit/Pushout.v) 刻画任意跨度余锥，
双向转换选定推出与跨度余极限，并提供左伴随保持性。
`SpanShape` 就是 `CospanShape^op`；`SpanCocone i j H` 使用共用的
`DualCone` 适配，构造复用其他命名余极限的同一形状重索引桥梁。

[Colimit.Finite](../theories/Cat/Colimit/Finite.v) reads the original
finite-limit constructions in the opposite category:

[Colimit.Finite](../theories/Cat/Colimit/Finite.v) 在反范畴中读取原有限极限构造：

- Coproducts and coequalizers give pushouts (`CoproductCoequalizerPushout`).
- Initial objects and pushouts give coproducts (`PushoutCoproduct`).
- Coproducts and pushouts give coequalizers (`CoproductPushoutCoequalizer`),
  hence initial objects and pushouts suffice (`PushoutCoequalizer`).

- 余积与余等化子给出推出（`CoproductCoequalizerPushout`）。
- 始对象与推出给出余积（`PushoutCoproduct`）。
- 余积与推出给出余等化子（`CoproductPushoutCoequalizer`），
  因而始对象与推出已经足够（`PushoutCoequalizer`）。

`finite_colimit_bases` converts these two bases in both directions, retaining
the supplied initial structure. It asserts neither equality of selected
records after round trips nor finite colimits from finite limits of `C`.
All selected structures remain opt-in.

`finite_colimit_bases` 双向转换这两套基础，保留给定始对象结构；
不要求往返后选定记录相等，也不从 `C` 的有限极限推出其有限余极限。
所有选定结构仍须显式启用。

## Indexed coproducts and general colimit constructors

## 指标余积与一般余极限构造

[Coproduct.Indexed](../theories/Cat/Coproduct/Indexed.v) uses the existing
`HasColimit C (DiscreteF D)` as its chosen structure. Write `∐[D]` for the
object, `ι∐[D] i` for an injection and `∐⟨κ⟩` for copairing. The β/η,
respectfulness, composition and arrow-extensionality laws reuse colimit laws.
`IndexedCoproductOpProduct` reads a single coproduct as an opposite indexed
product, retaining its apex definitionally. Discrete self-duality and the
identity-component comparison of discrete diagrams only adapt its diagram.

[Coproduct.Indexed](../theories/Cat/Coproduct/Indexed.v) 使用已有
`HasColimit C (DiscreteF D)` 作为选定结构。对象记为 `∐[D]`，注入记为
`ι∐[D] i`，余配对记为 `∐⟨κ⟩`；β/η、保相等性、复合及箭头外延律复用余极限定律。
`IndexedCoproductOpProduct` 将单个余积读作反指标积，定义上保留顶点；
离散自对偶及离散图式的恒等分量比较只负责适配其图式。

[Coproduct.Finite](../theories/Cat/Coproduct/Finite.v) exposes the original
recursive opposite finite product, including its injections and copairing;
the empty family uses the selected initial object.
[Coproduct.Sigma](../theories/Cat/Coproduct/Sigma.v) reads the original nested
sigma-product construction as a coproduct over a dependent sum of indices.
[Coproduct.Transport](../theories/Cat/Coproduct/Transport.v) inherits change
of injections, isomorphisms of summands and detection of arrow equality from
the original product transport theory. The foundational module is now
[Coproduct.Core](../theories/Cat/Coproduct/Core.v).

[Coproduct.Finite](../theories/Cat/Coproduct/Finite.v) 提供原递归反有限积的
通常接口，包括注入及余配对；空族使用选定始对象。
[Coproduct.Sigma](../theories/Cat/Coproduct/Sigma.v) 将原嵌套依赖和积构造
读作依赖和索引上的余积。
[Coproduct.Transport](../theories/Cat/Coproduct/Transport.v) 从原积运输理论
继承注入替换、加数同构及箭头相等检测。基础模块现为
[Coproduct.Core](../theories/Cat/Coproduct/Core.v)。

[Colimit.Construction](../theories/Cat/Colimit/Construction.v) requires only
two particular coproducts for an individual diagram, plus coequalizers:
the coproduct over its objects and the coproduct over the sources of its
arrows. For an arrow `f : i → j`, the two maps send its source summand by
the injection at `i` or by `D(f)` followed by the injection at `j`.
Their coequalizer is the original product/equalizer limit in the opposite
category. Ordinary constraint maps, candidate cocones and their colimit
property are wrappers of the original constraint maps, cones and theorem.
The uniform version asks for choices over those two discrete index types.

[Colimit.Construction](../theories/Cat/Colimit/Construction.v) 对单个图式
仅要求两个特定余积及余等化子：对象余积与箭头源对象余积。对箭头
`f : i → j`，两条映射分别用 `i` 处注入，或用 `D(f)` 后接 `j` 处注入。
其余等化子就是反范畴中的原积／等化子极限；通常约束映射、候选余锥及其余极限
性质均包装原约束映射、锥与定理。一致版本要求为这两个离散索引类型选择余积。

Internally, source summands are indexed by `ArrowOb (J^op)`; its `arrow_cod`
is the source in `J`. This reverses dependent endpoint data directly, without
an equality of arrow records or an additional quotient. Likewise,
[Colimit.Graph.Core](../theories/Cat/Colimit/Graph/Core.v) indexes coproducts
only by vertices and reversed generators, using `OpFreeF` to transfer the
original graph limit to the opposite free shape.

内部以 `ArrowOb (J^op)` 索引源加数，其中的 `arrow_cod` 就是 `J` 中的源。
这样直接反转依赖端点数据，不要求箭头记录相等，也不构造额外的商。
同样，[Colimit.Graph.Core](../theories/Cat/Colimit/Graph/Core.v) 只按顶点
与反向生成边索引余积，用 `OpFreeF` 将原图极限传递到反自由形状。

## Finite shapes, transport and reindexing

## 有限形状、运输与重索引

[Graph.Opposite](../theories/Graph/Opposite.v) defines `G^opG`, path reversal
`p^opP` and reading back `p^unopP`, with respectful round trips by specified
path equality. [Free](../theories/Cat/Free.v) supplies the full, essentially
surjective comparison of `FreeCat (G^opG)` and `(FreeCat G)^op`, in both
directions. No equality of graph or category records is required.

[Graph.Opposite](../theories/Graph/Opposite.v) 定义 `G^opG`、路径反转
`p^opP` 与读回 `p^unopP`，并按指定路径相等给出保相等往返律。
[Free](../theories/Cat/Free.v) 提供 `FreeCat (G^opG)` 与
`(FreeCat G)^op` 之间双向满且本质满的比较，不要求图或范畴记录相等。

[Shape.Finite](../theories/Cat/Shape/Finite.v) reverses finite hom covers
and finite generating graphs through `OpFiniteHomCover` and
`OpFiniteGenerators`. [Colimit.Finite](../theories/Cat/Colimit/Finite.v)
then wraps the original opposite `FiniteLimits` and `GeneratedLimits`.
Both initial+coproducts+coequalizers and initial+pushouts supply colimits
for finite **and finitely generated** shapes.
[Colimit.Graph.Finite](../theories/Cat/Colimit/Graph/Finite.v) supplies the
finite-free-graph interface and coproducts over its total generator index.
Cycles and additional path equations remain allowed; finite generation
does not assert a finite hom cover or a finite presentation.

[Shape.Finite](../theories/Cat/Shape/Finite.v) 通过 `OpFiniteHomCover` 与
`OpFiniteGenerators` 反转有限 Hom 覆盖及有限生成图。
[Colimit.Finite](../theories/Cat/Colimit/Finite.v) 据此包装原反
`FiniteLimits` 与 `GeneratedLimits`。始对象＋余积＋余等化子和始对象＋推出
两套基础都给出有限及**有限生成**形状的余极限。
[Colimit.Graph.Finite](../theories/Cat/Colimit/Graph/Finite.v) 提供有限自由图
接口及其总生成边索引上的余积。仍允许环与额外路径方程；有限生成不声称具有
有限 Hom 覆盖或有限展示。

[Colimit.Transport](../theories/Cat/Colimit/Transport.v) uses original limit
transport for equal cocones and invertible diagram transformations.
[Colimit.Reindex](../theories/Cat/Colimit/Reindex.v) transfers colimits along
full, essentially surjective shape functors, with selected structures in both
directions. Detection alone requires essential surjectivity.
[Diagram.Reindex](../theories/Cat/Diagram/Reindex.v) exposes `κ ∘∇F Q` and
`ExtendCocone`, respectfulness and pointwise round trips through the original
opposite cone operations. Composition comparisons use natural isomorphisms,
not equality of functor records.

[Colimit.Transport](../theories/Cat/Colimit/Transport.v) 通过原极限运输
处理相等余锥及可逆图式变换。
[Colimit.Reindex](../theories/Cat/Colimit/Reindex.v) 沿满且本质满的形状函子
传递余极限，选定结构提供双向转换；仅检测余极限时只需本质满。
[Diagram.Reindex](../theories/Cat/Diagram/Reindex.v) 通过原反锥操作提供
`κ ∘∇F Q`、`ExtendCocone`、保相等性及逐点往返律；复合比较使用自然同构，
不要求函子记录相等。

## Validation and scope

## 验证与范围

Equalities use the designated setoid relations. Witnesses remain Type-valued
and computational maps transparent. The existing five permanent checks in
[Universes](../tests/Universes.v) cover independent hom/equality levels,
larger shapes and mixed-category preservation. Four additional permanent
checks cover the named structure/shape conversions in both directions and
both hom/equality orderings, now including pushouts. Two checks cover the
finite-colimit basis conversions in the same orderings. Concrete computations
and assumption audits remain temporary.

相等使用指定广集关系，见证保留在 Type 中，计算映射保持透明。
[Universes](../tests/Universes.v) 中已有五项永久检查覆盖独立 Hom／相等层级、
更大的形状及混合范畴保持性；另外四项永久检查覆盖命名结构／形状的双向转换
及两种 Hom／相等大小排列，现也包含推出；两项检查覆盖相同排列下的有限余极限
基础转换。具体计算与公理审计仍作为临时检查。

The named initial/coproduct/coequalizer modules have been checked locally
with Rocq 9.0.1, OCaml 5.3.0 and Nix Dune 3.23.1. Full build, test and install
targets pass. Twenty-seven temporary assumption checks have no additional
assumptions. Temporary computations use distinct representatives and
extra Type-valued equality witnesses, including a parallel pair with
different raw outputs coequalized by specified setoid equality; its cocone
and colimit mediator reduce directly. Direct backend identity checks also
confirm that copairing and coequalizer factors are the original maps.

命名始对象／余积／余等化子模块已在 Rocq 9.0.1、OCaml 5.3.0 与
Nix Dune 3.23.1 下完成本地检查；完整构建、测试及安装目标通过。
27 项临时公理检查均无额外假设。临时计算使用不同代表及额外 Type 值相等见证，
其中一对具有不同原始输出的平行箭头按指定广集相等被余等化，其余锥与余极限
中介均可直接归约；底层数据的直接同一性检查也确认余配对及余等化子分解就是原映射。

The pushout and finite-basis additions pass the same full local build, test
and install targets. Twenty-four temporary assumption checks have no additional
assumptions. Temporary computations check pushout mediators with distinct
setoid representatives and extra Type-valued equality witnesses, plus direct
identity with the original pullback mediator. The selected span-colimit
mediator also reduces to the expected coordinates through the shared shape
adapter.

推出与有限基础增补也通过同一工具链的完整本地构建、测试及安装目标；
24 项临时公理检查均无额外假设。临时计算使用不同广集代表及额外 Type 值
相等见证检查推出中介，并直接验证它就是原拉回中介；
通过共用形状适配得到的选定跨度余极限中介也能归约到预期坐标。

The completed constructor layer passes the same full local build, test and
install targets. Eight additional permanent universe checks cover both size
orderings for finite/generated, general-diagram, graph-generated and reindexed
colimits. Seventy-six temporary assumption checks have no additional assumptions.
Temporary computations include finite/indexed copairing, general and graph
colimit mediators, a cyclic generating graph whose edge changes raw setoid
representatives, path reversal, and preservation of a selected indexed apex.
Dependent-index coproducts, transported colimits and reindexed colimits also
reduce to the expected injection/mediator composites.

补齐后的构造层通过同一工具链的完整本地构建、测试及安装目标。另有八项永久
宇宙检查，覆盖有限／有限生成、一般图式、图生成及重索引余极限的两种大小排列。
76 项临时公理检查均无额外假设。临时计算包括有限／指标余配对、一般与图生成
余极限中介、边会改变原始广集代表的含环生成图、路径反转及选定指标顶点的保留。
依赖和索引余积、运输后及重索引后的余极限也能将注入／中介复合归约到预期结果。

This completes the named, indexed, finite/generated and product/equalizer-based
duality milestone in issue #22. It does not assert that finite limits of a
category give its finite colimits. General Kan extensions and unrelated
categorical structures require separately scoped developments.

至此完成 #22 中命名构造、指标构造、有限／有限生成及积／等化子构造的对偶里程碑。
这不声称一个范畴的有限极限给出其有限余极限；一般 Kan 扩张及其他范畴结构仍需
独立界定开发范围。
