# Public abbreviation map

# 公共缩写对照

This is the maintained identifier map for [issue #38](https://github.com/Godalin/rocq-cats/issues/38).
The first batch starts from `5c2ba4c71882ad4851f1ca6a6aeac8b18486e651`
on `agents/refactor-issue-abbreviation-standards`. On 2026-11-15 the user
authorized naming work on this branch independently of the three mathematical
tracks. Work here is manually directed. On 2026-11-15 the user authorized committing,
pushing and submitting the two completed batches to the existing integrator.
After that handoff, preserve the frozen source and await further instructions.

本文维护 [#38](https://github.com/Godalin/rocq-cats/issues/38) 的标识符缩写对照。
第一批从上述提交和分支开始。用户于 2026-11-15 指定本分支先开展命名整理，
不等待三条数学支线。本分支由用户直接安排；用户随后授权将完成的两批提交、
推送并发送至既有集成会话。交接后保全冻结来源，等待后续安排。

Batch 4's combined Clos/ClosOp, Exp, remaining Cart and Prof migration is
integrated as `76642d4`: frozen `315dbda` was rebased to `98dec6e`, followed by
the owner's upstream-client compatibility repair. Both sources remain preserved.
Earlier batches were integrated as `0f18829` and `6ec6c06`. The user-authorized
[complete-structure migration](./BundledInterfaces.md#complete-category-bundles-first-slice)
now starts separately from this naming baseline; it does not extend the exact
195-entry Batch 4 map or replay its patches.

第四批 Clos/ClosOp、Exp、剩余 Cart 与 Prof 已集成为 `76642d4`：冻结来源
`315dbda` 重基得到 `98dec6e`，再由命名负责人修复上游客户端。来源均保全，
前序批次分别已集成至 `0f18829` 和 `6ec6c06`。用户授权的
[完整结构打包迁移](./BundledInterfaces.md#complete-category-bundles-first-slice)
现从此命名基线独立开始，不扩充第四批 195 项精确表，也不重放其补丁。

## Reading and maintenance / 阅读与维护

The old-name column refers to the batch's starting baseline, and the new-name
column to the local implementation. In particular, old `Fct` means a functor
category; new `Fct` means a functor. Apply the map simultaneously, never as
successive textual replacements. Each implemented row is an exact identifier,
including instance names, projections and reviewed laws. A row does not rename
its source module. There are no compatibility aliases.

旧名栏对应本批起点，新名栏对应本地实现。尤其要区分旧 `Fct`（函子范畴）与
新 `Fct`（函子）；迁移必须同时替换，不能连续套用文本替换。已实现表中每行
都是一个精确标识符，包含实例名、投影及已审阅的定律名；该行不改变所在模块，
也不保留兼容别名。

For each later batch, add the exact old/new pairs and source links, distinguish
implemented names from candidates, record actual validation, and update current
bilingual clients/docs together. Historical source-pinned audit evidence keeps
its original names; use this document to translate it to the current API.

后续每批须补充精确旧名／新名及源码链接，区分已实现与候选，记录实际验证，
并同步更新双语说明及客户端。固定历史版本的审计证据保留当时名称，阅读当前
API 时按本文对照。

When a later batch shortens an earlier target again, the earlier row is
updated to the current final name; the later table also records the intermediate
name being replaced. These are migration entries, not compatibility aliases.

后续批次继续缩短先前目标时，旧表的新名栏同步更新到当前最终名称；新批次也
记录被替换的中间名称。这些是迁移对照，不是兼容别名。

## Stem policy / 词根规范

The stems below follow the naming discussion in #38. Only the exact rows in
the implemented batch have migrated; the remaining families are tracked below.

下表沿用 #38 已确认的词根；只有已实现批次中的精确条目已经迁移，其余词族
列在后续工作中。

| Term / 术语 | Stem / 词根 | Boundary / 边界 |
| --- | --- | --- |
| Category / 范畴 | `Cat` | Keep existing complete structures until individually reviewed / 完整结构逐项审阅 |
| Functor / 函子 | `Fct` | `F` remains the construction suffix / 构造后缀仍用 `F` |
| Functor category / 函子范畴 | `FctCat` | Distinct from the functor type / 区别于函子类型 |
| Natural transformation and isomorphism / 自然变换及同构 | `Nat`, `NatIso` | Retain suffix `N` / 保留 `N` 后缀 |
| Adjunction / 伴随 | `Adj` | Retain notation `⊣` / 保留记号 |
| Cartesian / 笛卡尔 | `Cart` | Retain the complete `CartesianCat` hierarchy / 完整结构层级另行审阅 |
| Diagonal / 对角 | `Diag` | Keep the existing diagonal notation / 保留已有对角记号 |
| Generator and generators / 生成元 | `Gen` | Singular and plural use the same stem / 单复数使用同一词根 |
| Object and objects / 对象 | `Obj` | Singular and plural use the same stem; preserve kind suffixes / 单复数统一，保留种类后缀 |
| Limit and colimit / 极限与余极限 | `Lim`, `Colim` | Keep `HasLimit`, `HasColimit` / 保留选定构造接口 |
| Presheaf / 预层 | `Psh` | Existing category name stays / 保留已有范畴名 |
| Vertex / 顶点 | `Vtx` | Public declarations and fields use this stem; module paths stay unchanged / 公共声明及字段统一，模块路径保留 |
| Closure / 闭包 | `Clos` | Generic operators and raw relations; do not conflate with Closed / 一般算子及底层关系，不与 Closed 混写 |
| Packaged relation-closure operator / 打包关系闭包算子 | `*ClosOp` | Includes fiberwise, compatible and congruence operators; raw relations use `*Clos` / 含逐纤维、相容及合同算子，底层关系用 `*Clos` |
| Exponential constructions / 指数构造 | `Exp` | Retain `HasExponential` and descriptive helpers / 保留选定结构及描述性辅助名 |
| Profunctors / Profunctor 词族 | `Prof`, `prof_` | Includes reviewed public operations, laws, fields and scope; retain module paths / 含公开操作、定律、字段及 scope，保留模块路径 |
| Subobject / 子对象 | `SubObj` | A setoid of subobjects needs `S` / 子对象广集须体现 `S` |
| Groupoid / 群胚 | `Gpd` | No change to `IsGroupoid C` in this batch / 本批不改固定范畴上的接口 |
| Monoid, monoidal, monad / 幺半群、幺半、单子 | `Monoid`, `Monoidal`, `Monad` | Keep complete stems / 保留完整词根 |

## Batch 1: implemented locally / 第一批：已在本地实现

All rows below are implemented; the delivery checkpoint includes both batches.
The batch covers 69 exact identifiers. The functor-category clients migrate
with the functor type to avoid capturing their old `Fct` references. Related
cartesian preservation names and limit-functor names are included so the
renamed bundles and adjunctions have consistent direct clients.

下表共 69 个精确标识符均已实现，与第二批一同交付。函子类型与函子范畴
客户端同步迁移，以免旧 `Fct` 引用被新类型捕获；相关笛卡尔保持性及极限函子名
一并整理，使函子包和伴随的直接客户端使用一致名称。

### Functor interfaces / 函子接口

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `Functor` | `Fct` | [Cat/Functor/Core.v](../theories/Cat/Functor/Core.v) |
| `Fct` | `FctCat` | [Cat/Natural.v](../theories/Cat/Natural.v) |
| `FunctorS` | `FctS` | [Instance/Set/Functor.v](../theories/Instance/Set/Functor.v) |
| `FunctorPresheaf` | `FctPsh` | [Instance/Set/Functor.v](../theories/Instance/Set/Functor.v) |
| `FunctorPresheafN` | `FctPshN` | [Instance/Set/Functor.v](../theories/Instance/Set/Functor.v) |
| `FunctorPresheafF` | `FctPshF` | [Instance/Set/Functor.v](../theories/Instance/Set/Functor.v) |
| `FreeFunctor` | `FreeFct` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `FreeFunctorChoiceN` | `FreeFctChoiceN` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `CartesianFunctor` | `CartFct` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `CartesianFunctorFromPreservation` | `CartFctFromPreservation` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `CCCFunctor` | `CCCFct` | [Cat/Functor/Closed.v](../theories/Cat/Functor/Closed.v) |
| `CCCFunctorFromPreservation` | `CCCFctFromPreservation` | [Cat/Functor/Closed.v](../theories/Cat/Functor/Closed.v) |
| `CCCFunctor_IsCCCF` | `CCCFct_IsCCCF` | [Cat/Functor/Closed.v](../theories/Cat/Functor/Closed.v) |
| `LaxMonoidalFunctor` | `LaxMonoidalFct` | [Cat/Monoidal/Functor.v](../theories/Cat/Monoidal/Functor.v) |
| `IdF_LaxMonoidalFunctor` | `IdF_LaxMonoidalFct` | [Cat/Monoidal/Functor.v](../theories/Cat/Monoidal/Functor.v) |
| `ConstF_LaxMonoidalFunctor` | `ConstF_LaxMonoidalFct` | [Cat/Monoidal/Constant.v](../theories/Cat/Monoidal/Constant.v) |
| `VertexFunctor` | `VtxFct` | [Instance/Set/Vertex/Functor.v](../theories/Instance/Set/Vertex/Functor.v) |
| `VertexFunctorEq` | `VtxFctEq` | [Instance/Set/Vertex/Functor.v](../theories/Instance/Set/Vertex/Functor.v) |
| `VertexFunctorEq_Equivalence` | `VtxFctEq_Equivalence` | [Instance/Set/Vertex/Functor.v](../theories/Instance/Set/Vertex/Functor.v) |
| `VertexFunctorS` | `VtxFctS` | [Instance/Set/Vertex/Functor.v](../theories/Instance/Set/Vertex/Functor.v) |

### Functor-category clients / 函子范畴客户端

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `Fct_HasTerminal` | `FctCat_HasTerminal` | [Cat/Functor/FiniteProducts.v](../theories/Cat/Functor/FiniteProducts.v) |
| `Fct_HasProduct` | `FctCat_HasProduct` | [Cat/Functor/FiniteProducts.v](../theories/Cat/Functor/FiniteProducts.v) |
| `Fct_IsGroupoid` | `FctCat_IsGroupoid` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `OpFctF` | `OpFctCatF` | [Cat/Natural.v](../theories/Cat/Natural.v) |

### Cartesian functor preservation / 笛卡尔函子保持性

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `IsCartesianF` | `IsCartF` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `IdF_IsCartesianF` | `IdF_IsCartF` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `CompF_IsCartesianF` | `CompF_IsCartF` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `CartesianF` | `CartF` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `IdCartesianF` | `IdCartF` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `CompCartesianF` | `CompCartF` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `cartesian_isCartesianF` | `cartesian_isCartF` | [Cat/Functor/Cartesian.v](../theories/Cat/Functor/Cartesian.v) |
| `isCartesianF` | `isCartF` | [Cat/Functor/Closed.v](../theories/Cat/Functor/Closed.v) |
| `TypeInterpretF_IsCartesianF` | `TypeInterpretF_IsCartF` | [STLC/TypeInterpretation.v](../theories/STLC/TypeInterpretation.v) |
| `VertexNerveF_IsCartesianF` | `VtxNerveF_IsCartF` | [Instance/Set/Simplicial/Vertex/Cartesian.v](../theories/Instance/Set/Simplicial/Vertex/Cartesian.v) |
| `ExponentialF_IsCartesianF` | `ExpF_IsCartF` | [Cat/Limit/Exponential.v](../theories/Cat/Limit/Exponential.v) |

### Adjunctions and induced constructions / 伴随及其诱导构造

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `Adjunction` | `Adj` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `AdjunctionFromHom` | `AdjFromHom` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `OpAdjunction` | `OpAdj` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `IdAdjunction` | `IdAdj` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `CompAdjunction` | `CompAdj` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `AdjunctionMonad` | `AdjMonad` | [Cat/Monad/Adjunction.v](../theories/Cat/Monad/Adjunction.v) |
| `AdjunctionMonadMul` | `AdjMonadMul` | [Cat/Monad/Adjunction.v](../theories/Cat/Monad/Adjunction.v) |
| `AdjunctionKleisliF` | `AdjKleisliF` | [Cat/Monad/KleisliComparison.v](../theories/Cat/Monad/KleisliComparison.v) |
| `KleisliAdjunction` | `KleisliAdj` | [Cat/Monad/KleisliAdjunction.v](../theories/Cat/Monad/KleisliAdjunction.v) |
| `ArrowApplyAdjunction` | `ArrowApplyAdj` | [Cat/Computational/Arrow/Monad.v](../theories/Cat/Computational/Arrow/Monad.v) |
| `FreeAdjunction` | `FreeAdj` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `CofreeAdjunction` | `CofreeAdj` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `AdjunctionFreeObjects` | `AdjFreeObj` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `AdjunctionFreeRoundtripN` | `AdjFreeRoundtripN` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `GeneratorFreeAdjunction` | `GenFreeAdj` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `ProductExponentialAdjunction` | `ProdExpAdj` | [Cat/Exponential/Core.v](../theories/Cat/Exponential/Core.v) |
| `ClosureAdjunction` | `ClosAdj` | [Instance/Preorder/Closure.v](../theories/Instance/Preorder/Closure.v) |
| `LimitAdjunction` | `LimAdj` | [Cat/Limit/Adjunction.v](../theories/Cat/Limit/Adjunction.v) |
| `ColimitAdjunction` | `ColimAdj` | [Cat/Colimit/Adjunction.v](../theories/Cat/Colimit/Adjunction.v) |
| `DiagonalAdjunctionLimit` | `DiagAdjLim` | [Cat/Limit/Adjunction.v](../theories/Cat/Limit/Adjunction.v) |
| `DiagonalAdjunctionLimits` | `DiagAdjLims` | [Cat/Limit/Adjunction.v](../theories/Cat/Limit/Adjunction.v) |
| `DiagonalAdjunctionColimit` | `DiagAdjColim` | [Cat/Colimit/Adjunction.v](../theories/Cat/Colimit/Adjunction.v) |
| `DiagonalAdjunctionColimits` | `DiagAdjColims` | [Cat/Colimit/Adjunction.v](../theories/Cat/Colimit/Adjunction.v) |

### Adjunction projections and laws / 伴随投影与定律

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `adjunction_hom` | `adj_hom` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_unit` | `adj_unit` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_counit` | `adj_counit` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_triangle_l` | `adj_triangle_l` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_triangle_r` | `adj_triangle_r` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_unit_universal` | `adj_unit_universal` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_counit_universal` | `adj_counit_universal` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_op_unit` | `adj_op_unit` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_op_counit` | `adj_op_counit` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |

### Limit functors / 极限函子

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `LimitF` | `LimF` | [Cat/Limit/Core.v](../theories/Cat/Limit/Core.v) |
| `ColimitF` | `ColimF` | [Cat/Colimit/Core.v](../theories/Cat/Colimit/Core.v) |

The `adj_*` rows are deliberately reviewed projections and their immediate
laws. Other descriptive names such as `functor_comp`, `adjunction_β`,
`adjunction_hom_nat_iso` and `adjunction_monad_mul_computes` remain unchanged;
this is not a blanket substitution of every lowercase subject. `fmap`, `F0`,
`F1`, `IdF`, `CompF`, `Nat`, `NatIso` and existing mathematical notation retain
their meanings. `FreeFct` avoids the existing, different `FreeF`; `OpFctCatF`
explicitly identifies its source and target as functor categories.

`adj_*` 条目是逐项审阅的投影及直接定律；`functor_comp`、`adjunction_β`、
`adjunction_hom_nat_iso`、`adjunction_monad_mul_computes` 等描述性名称保留，
不对所有小写主题进行机械替换。`fmap`、`F0`、`F1`、`IdF`、`CompF`、`Nat`、
`NatIso` 及已有数学记号含义不变。`FreeFct` 避开已有的不同构造 `FreeF`；
`OpFctCatF` 明确说明其源、目标为函子范畴。

## Batch 2: Diag, Gen and Obj / 第二批：Diag、Gen 与 Obj

On 2026-11-15 the user added `Diagonal → Diag`, `Generator`/`Generators → Gen`
and `Object`/`Objects → Obj`. The 45 exact rows below are relative to the
first-batch working tree before submission; six further shorten its targets.
Source modules and descriptive lowercase helpers retain their names. The
subobject setoid uses the already agreed `SubObjS`, and its classifier class
and inherited ETCS field migrate together. `Obj` is not a replacement for
existing concise `Ob` projections.

用户于 2026-11-15 增补上述三组词根，单复数统一。以下 45 条精确映射以交付前的
首批工作区为起点，其中六条进一步缩短首批目标。源码模块及描述性小写
辅助名保留；子对象广集采用已确认的 `SubObjS`，分类子类与 ETCS 继承字段
一并迁移。已有简洁的 `Ob` 投影不在本次替换范围内。

### Diagonal constructions / 对角构造

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `CoendDiagonal` | `CoendDiag` | [Cat/Coend/Construction.v](../theories/Cat/Coend/Construction.v) |
| `DiagonalAdjColim` | `DiagAdjColim` | [Cat/Colimit/Adjunction.v](../theories/Cat/Colimit/Adjunction.v) |
| `DiagonalAdjColims` | `DiagAdjColims` | [Cat/Colimit/Adjunction.v](../theories/Cat/Colimit/Adjunction.v) |
| `DiagonalAdjLim` | `DiagAdjLim` | [Cat/Limit/Adjunction.v](../theories/Cat/Limit/Adjunction.v) |
| `DiagonalAdjLims` | `DiagAdjLims` | [Cat/Limit/Adjunction.v](../theories/Cat/Limit/Adjunction.v) |
| `DiagonalF` | `DiagF` | [Cat/Diagram/Core.v](../theories/Cat/Diagram/Core.v) |
| `EndDiagonal` | `EndDiag` | [Cat/End/Construction.v](../theories/Cat/End/Construction.v) |

### Generators / 生成元

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `DayGeneratorN` | `DayGenN` | [Cat/Day/Universal.v](../theories/Cat/Day/Universal.v) |
| `ExtendGeneratorF` | `ExtendGenF` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `FiniteGraphGenerators` | `FiniteGraphGen` | [Cat/Shape/Finite.v](../theories/Cat/Shape/Finite.v) |
| `FiniteHomGenerators` | `FiniteHomGen` | [Cat/Shape/Finite.v](../theories/Cat/Shape/Finite.v) |
| `GeneratorComp` | `GenComp` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorDiagramCat` | `GenDiagramCat` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorExtendN` | `GenExtendN` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorFreeAdj` | `GenFreeAdj` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorFreeObjects` | `GenFreeObj` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorId` | `GenId` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorNat` | `GenNat` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorNatEq` | `GenNatEq` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorNatEq_Equivalence` | `GenNatEq_Equivalence` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorNatS` | `GenNatS` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `GeneratorUnit` | `GenUnit` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `HasFiniteGenerators` | `HasFiniteGen` | [Cat/Shape/Finite.v](../theories/Cat/Shape/Finite.v) |
| `OpFiniteGenerators` | `OpFiniteGen` | [Cat/Shape/Finite.v](../theories/Cat/Shape/Finite.v) |
| `RestrictGeneratorF` | `RestrictGenF` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |

### Objects and selected structures / 对象及选定结构

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `AdjFreeObjects` | `AdjFreeObj` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `CodiagramObjects` | `CodiagramObj` | [Cat/Colimit/Construction.v](../theories/Cat/Colimit/Construction.v) |
| `CompositeFreeObjects` | `CompositeFreeObj` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `DiagramObjects` | `DiagramObj` | [Cat/Limit/Construction.v](../theories/Cat/Limit/Construction.v) |
| `FreeObjectsFromUniversal` | `FreeObjFromUniversal` | [Cat/FreeObject/Core.v](../theories/Cat/FreeObject/Core.v) |
| `HasFreeObjects` | `HasFreeObj` | [Cat/FreeObject/Core.v](../theories/Cat/FreeObject/Core.v) |
| `HasNaturalNumbersObject` | `HasNaturalNumbersObj` | [Topos/Nat.v](../theories/Topos/Nat.v) |
| `HasSubObjectClassifier` | `HasSubObjClassifier` | [Topos/Sub.v](../theories/Topos/Sub.v) |
| `LaxMonoidObject` | `LaxMonoidObj` | [Cat/Monoidal/Transport.v](../theories/Cat/Monoidal/Transport.v) |
| `MonoidObject` | `MonoidObj` | [Cat/Monoidal/Monoid.v](../theories/Cat/Monoidal/Monoid.v) |
| `MonoidObjectsF` | `MonoidObjF` | [Instance/Set/Simplicial/Vertex/Monoid.v](../theories/Instance/Set/Simplicial/Vertex/Monoid.v) |
| `OrdinalObjectsF` | `OrdinalObjF` | [Instance/Set/Vertex/Ordinal.v](../theories/Instance/Set/Vertex/Ordinal.v) |
| `PointwiseFreeObjects` | `PointwiseFreeObj` | [Cat/FreeObject/Representable.v](../theories/Cat/FreeObject/Representable.v) |
| `SetCat_HasNaturalNumbersObject` | `SetCat_HasNaturalNumbersObj` | [Instance/Set/Nat.v](../theories/Instance/Set/Nat.v) |
| `SetMonoidObject` | `SetMonoidObj` | [Instance/Set/Monoid.v](../theories/Instance/Set/Monoid.v) |
| `SubObject` | `SubObjS` | [Instance/Set/Subobject.v](../theories/Instance/Set/Subobject.v) |
| `VertexProductObjectsF` | `VtxProductObjF` | [Instance/Set/Vertex/Product.v](../theories/Instance/Set/Vertex/Product.v) |
| `VertexTerminalObjectsF` | `VtxTerminalObjF` | [Instance/Set/Vertex/Terminal.v](../theories/Instance/Set/Vertex/Terminal.v) |
| `hasNaturalNumbersObject` | `hasNaturalNumbersObj` | [Topos/ETCS.v](../theories/Topos/ETCS.v) |
| `hasSubObjectClassifier` | `hasSubObjClassifier` | [Topos/Core.v](../theories/Topos/Core.v) |

### Batch 2 validation / 第二批验证

- `opam exec --switch=rocq-cats -- dune build @all` passed with Rocq/Stdlib
  9.2, OCaml 5.3.0 and Dune 3.23.1, including existing regression modules.
- All 56 Rocq files changed in Batch 2 reverse exactly to the first-batch
  snapshot by the 45-name map. Across both batches, 108 distinct original
  public identifiers migrate in 292 Rocq files; reversing the combined map
  recovers the initial baseline apart from the eight previously recorded
  nested-record closing indents. Import commands are unchanged.
- Temporary compilations checked all 45 second-batch signatures/assumptions,
  then all 108 final signatures/assumptions with universes printed. Every
  assumption report was closed under the global context. The final audit also
  passed 113 retired/intermediate-name checks, functor-category definitional
  comparisons, cartesian-functor coercion and preservation probes, and ETCS
  fields using the same terminal choice through explicit parent projections.
- All 114 historical/intermediate table rows point to the current 108 names;
  every owner link and new declaration name resolves. `git diff --check`
  passed. Temporary checks are not committed tests; no HTML/PDF export ran.
- The user authorized submitting this completed checkpoint to the existing
  integrator. Git and #38 record the source commit and integration result.
  Keep the submitted source frozen and await further user instructions.

- 项目 switch 下全库构建及已有回归模块通过，工具链为 Rocq/Stdlib 9.2、
  OCaml 5.3.0、Dune 3.23.1。
- 第二批 56 个 Rocq 文件按 45 项映射可精确恢复首批快照；累计两批在 292 个
  Rocq 文件中规范化 108 个不同的原始公开名称。按合并映射反向替换可恢复初始
  基线，仅保留已记录的八处嵌套记录结束符缩进调整；导入命令全部保持原样。
- 临时编译先检查第二批 45 项签名／假设，再打印宇宙检查最终 108 项签名／
  假设，报告全部闭合。最终审计另通过 113 项旧名／中间名退役检查、函子范畴
  定义相等、笛卡尔函子包强制转换及保持性检查，并经显式父投影核对 ETCS
  继承字段使用同一终对象选择。
- 文档 114 条历史／中间映射均指向当前 108 个名称；源码链接及所属模块中的
  新名称均已核对，差异格式检查通过。临时检查不作为已提交测试；未导出 HTML/PDF。
- 用户已授权向既有集成会话提交本检查点；来源提交与集成结果由 Git 和 #38
  记录。交接后保全冻结来源，等待用户后续安排。

## Upstream-client compatibility repair / 基线后客户端兼容修订

The original frozen source `6314f0d4c7d49d828b71a3d6cbe9f925d70a6a28`
remains unchanged on `agents/refactor-issue-abbreviation-standards`. The
integrator's ordinary rebase onto `typeprop@72d9aed` produced
`91f4d64349b86f9d5fbe71b80a8d1696d3fe6bb3` without text conflicts, but
clients added after the original baseline still referenced retired names.
The source owner repairs these clients on `abbreviations-38-upstream-compat`,
starting from that temporary result in the source owner's own worktree.

原冻结来源及原分支保持不变。集成者在其自有工作区将来源普通重基到 `72d9aed`，
得到无文本冲突的临时结果 `91f4d6`；原基线后新增的客户端仍引用已退役名称，
因而构建失败。来源 owner 从该临时结果在自己的工作区另建兼容修订分支，
只补齐原批准表对这些客户端的迁移。

This repair changes exactly 60 `Functor → Fct` references in the following
11 files. Their proofs, declarations, universes and import commands otherwise
remain byte-for-byte identical. The actual temporary baseline already uses
`DayGenN` for the Day generator declaration and its references. Coqdoc code
references were checked in both languages; ordinary mathematical prose and
source paths retain their original wording. The 108-name map and all pending
families are unchanged.

修订仅替换下表 11 个文件中的 60 处函子类型引用；除此之外，证明、声明、宇宙
及导入命令逐字保持原样。实际临时基线中的 Day 生成元声明及引用已使用
`DayGenN`。双语 coqdoc 代码引用一并核对，普通数学叙述及源码路径保留。
108 项原映射和后续词族清单不变。

| Client / 客户端 | Replacements / 替换数 |
| --- | --- |
| [tests/cocycle-homotopy/Universes.v](../tests/cocycle-homotopy/Universes.v) | 11 |
| [tests/sphere-class-map/Computations.v](../tests/sphere-class-map/Computations.v) | 1 |
| [tests/sphere-class-map/Universes.v](../tests/sphere-class-map/Universes.v) | 8 |
| [theories/Cat/Day/Unit.v](../theories/Cat/Day/Unit.v) | 15 |
| [theories/Cat/Day/Universal.v](../theories/Cat/Day/Universal.v) | 2 |
| [theories/Instance/Bool/CocycleHomotopy.v](../theories/Instance/Bool/CocycleHomotopy.v) | 3 |
| [theories/Instance/Set/Simplicial/Cocycle/Homotopy.v](../theories/Instance/Set/Simplicial/Cocycle/Homotopy.v) | 8 |
| [theories/Instance/Set/Simplicial/Cocycle/Nerve.v](../theories/Instance/Set/Simplicial/Cocycle/Nerve.v) | 3 |
| [theories/Instance/Set/Simplicial/Homotopy/OneReduced.v](../theories/Instance/Set/Simplicial/Homotopy/OneReduced.v) | 4 |
| [theories/Instance/Set/Simplicial/Homotopy/SphereCylinder.v](../theories/Instance/Set/Simplicial/Homotopy/SphereCylinder.v) | 1 |
| [theories/Instance/Set/Simplicial/Homotopy/SphereMap.v](../theories/Instance/Set/Simplicial/Homotopy/SphereMap.v) | 4 |

`opam exec --switch=rocq-cats -- dune build @all` passed with Rocq/Stdlib
9.2, OCaml 5.3.0 and Dune 3.23.1, including the added upstream regression
modules. The original final audit was rerun unchanged: 108 signatures with
universes printed, 108 closed assumption reports, 113 retired/intermediate-name
checks and its definitional/coercion/selected-parent probes all passed.
A whole-source lexer scan found no approved retired names in executable code
or coqdoc code references. The exact diff reverses to `91f4d6` by replacing
only those 60 type references; `git diff --check` passed. These audits are
temporary checks, not added regression files. No HTML/PDF export was run.

项目 switch 下全库及新增上游回归模块构建通过，工具链为 Rocq/Stdlib 9.2、
OCaml 5.3.0、Dune 3.23.1。原最终审计原样重跑通过：108 项签名打印宇宙，
108 项假设报告全部闭合，113 项退役／中间名及原有定义相等、强制转换、选定
父结构检查均通过。全源词法扫描确认执行代码及 coqdoc 代码引用无已批准退役名
遗留；差异按这 60 处类型替换可精确恢复 `91f4d6`，格式检查通过。审计仍为
临时检查，不添加重复回归文件，未运行 HTML/PDF 导出。

This is a compatibility repair required for accepting the existing L2 naming
change, with no new mathematical/API design or abbreviation family. The new
candidate is committed and frozen for the existing integrator's revalidation;
the original source stays preserved, and further work awaits user instructions.

这是完成既有 L2 命名变更验收所需的兼容修复，不增加数学／API 设计或缩写词族。
新候选提交后冻结，交由既有集成者复验；原来源保全，后续工作等待用户安排。

## Batch 3: the Vtx family / 第三批：Vtx 词族

The user requested the next naming step after the updated #38 coverage audit.
This bounded batch starts from integrated
`9f7024af8f705a176a8923c38e97877fb66ccec7` on `abbreviations-vtx-38` and
completes the previously approved `Vertex → Vtx` family. The original frozen
sources `6314f0d` and `0f18829` remain preserved. The user subsequently authorized
committing, publishing and submitting this batch to the designated integrator.
Integration acceptance remains pending.

用户在 #38 更新覆盖审查后安排继续下一步。本批从已集成 `9f7024a` 在新短分支
`abbreviations-vtx-38` 开始，补齐此前已批准的 Vtx 词族。两个旧冻结来源保全；
用户随后授权提交、推送并交给指定集成会话，集成验收待完成。

The 61 exact rows cover the graph vertex projection, graph shapes, presented
categories, labelled diagrams/chains, vertex nerves and their concrete models
and instance names. Already migrated `VtxFct` names remain unchanged. The
previously accepted compound `VertexNerveCartesianF → VtxNerveCartF` combines
the two approved stems. Three earlier map targets are now shortened further;
the earlier rows point directly to their current final names.

61 项精确映射覆盖图顶点投影、图形状、带对象呈现的范畴、标记图式／链、顶点
nerve 及具体模型、实例名。已有 VtxFct 词族保持原样；预先确认的复合名
VtxNerveCartF 同时采用 Vtx、Cart 词根。三项旧批次目标在本批继续缩短，旧表的
新名栏同步指向当前最终名称。

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `BoolVertexComparison` | `BoolVtxComparison` | [Instance/Bool/Nerve.v](../theories/Instance/Bool/Nerve.v) |
| `BoolVertexNerve` | `BoolVtxNerve` | [Instance/Bool/Nerve.v](../theories/Instance/Bool/Nerve.v) |
| `BoolVertexNerve_HasKanFillers` | `BoolVtxNerve_HasKanFillers` | [Instance/Bool/Nerve.v](../theories/Instance/Bool/Nerve.v) |
| `BoolVertexNerve_IsCoskeletal` | `BoolVtxNerve_IsCoskeletal` | [Instance/Bool/Nerve.v](../theories/Instance/Bool/Nerve.v) |
| `ConstantVertexF` | `ConstantVtxF` | [Instance/Bool/Nerve.v](../theories/Instance/Bool/Nerve.v) |
| `CospanVertex` | `CospanVtx` | [Graph/Shape.v](../theories/Graph/Shape.v) |
| `MonoidVertexF` | `MonoidVtxF` | [Instance/Set/Simplicial/Vertex/Monoid.v](../theories/Instance/Set/Simplicial/Vertex/Monoid.v) |
| `MonoidVertexN` | `MonoidVtxN` | [Instance/Set/Simplicial/Vertex/Monoid.v](../theories/Instance/Set/Simplicial/Vertex/Monoid.v) |
| `OrdinalVertexF` | `OrdinalVtxF` | [Instance/Set/Vertex/Ordinal.v](../theories/Instance/Set/Vertex/Ordinal.v) |
| `OrdinalVertexInvF` | `OrdinalVtxInvF` | [Instance/Set/Vertex/Ordinal.v](../theories/Instance/Set/Vertex/Ordinal.v) |
| `OrdinalVertexMapF` | `OrdinalVtxMapF` | [Instance/Set/Vertex/Ordinal.v](../theories/Instance/Set/Vertex/Ordinal.v) |
| `OrdinalVertexNerveN` | `OrdinalVtxNerveN` | [Instance/Set/Simplicial/Vertex/Ordinal.v](../theories/Instance/Set/Simplicial/Vertex/Ordinal.v) |
| `OrdinalVertexPointF` | `OrdinalVtxPointF` | [Instance/Set/Vertex/Ordinal.v](../theories/Instance/Set/Vertex/Ordinal.v) |
| `StandardVertexNerveN` | `StandardVtxNerveN` | [Instance/Set/Simplicial/Vertex/Ordinal.v](../theories/Instance/Set/Simplicial/Vertex/Ordinal.v) |
| `Vertex` | `Vtx` | [Graph/Core.v](../theories/Graph/Core.v) |
| `VertexCat` | `VtxCat` | [Instance/Set/Vertex/Core.v](../theories/Instance/Set/Vertex/Core.v) |
| `VertexCat_IsGroupoid` | `VtxCat_IsGroupoid` | [Instance/Set/Simplicial/Vertex/Horn2.v](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) |
| `VertexChainEq` | `VtxChainEq` | [Instance/Set/Vertex/Chain.v](../theories/Instance/Set/Vertex/Chain.v) |
| `VertexChainEq_Equivalence` | `VtxChainEq_Equivalence` | [Instance/Set/Vertex/Chain.v](../theories/Instance/Set/Vertex/Chain.v) |
| `VertexChainS` | `VtxChainS` | [Instance/Set/Vertex/Chain.v](../theories/Instance/Set/Vertex/Chain.v) |
| `VertexCompF` | `VtxCompF` | [Instance/Set/Vertex/Functor.v](../theories/Instance/Set/Vertex/Functor.v) |
| `VertexDiagramEq` | `VtxDiagramEq` | [Instance/Set/Vertex/Core.v](../theories/Instance/Set/Vertex/Core.v) |
| `VertexDiagramEq_Equivalence` | `VtxDiagramEq_Equivalence` | [Instance/Set/Vertex/Core.v](../theories/Instance/Set/Vertex/Core.v) |
| `VertexDiagramN` | `VtxDiagramN` | [Instance/Set/Simplicial/Vertex/Core.v](../theories/Instance/Set/Simplicial/Vertex/Core.v) |
| `VertexDiagramS` | `VtxDiagramS` | [Instance/Set/Vertex/Core.v](../theories/Instance/Set/Vertex/Core.v) |
| `VertexFstF` | `VtxFstF` | [Instance/Set/Vertex/Product.v](../theories/Instance/Set/Vertex/Product.v) |
| `VertexIdF` | `VtxIdF` | [Instance/Set/Vertex/Functor.v](../theories/Instance/Set/Vertex/Functor.v) |
| `VertexIntervalProductF` | `VtxIntervalProductF` | [Instance/Set/Simplicial/Vertex/HomotopyInv.v](../theories/Instance/Set/Simplicial/Vertex/HomotopyInv.v) |
| `VertexMonoidN` | `VtxMonoidN` | [Instance/Set/Simplicial/Vertex/Monoid.v](../theories/Instance/Set/Simplicial/Vertex/Monoid.v) |
| `VertexNerve` | `VtxNerve` | [Instance/Set/Simplicial/Vertex/Core.v](../theories/Instance/Set/Simplicial/Vertex/Core.v) |
| `VertexNerveCartesianF` | `VtxNerveCartF` | [Instance/Set/Simplicial/Vertex/Cartesian.v](../theories/Instance/Set/Simplicial/Vertex/Cartesian.v) |
| `VertexNerveCylinderN` | `VtxNerveCylinderN` | [Instance/Set/Simplicial/Vertex/HomotopyInv.v](../theories/Instance/Set/Simplicial/Vertex/HomotopyInv.v) |
| `VertexNerveF` | `VtxNerveF` | [Instance/Set/Simplicial/Vertex/Category.v](../theories/Instance/Set/Simplicial/Vertex/Category.v) |
| `VertexNerveF_IsCartF` | `VtxNerveF_IsCartF` | [Instance/Set/Simplicial/Vertex/Cartesian.v](../theories/Instance/Set/Simplicial/Vertex/Cartesian.v) |
| `VertexNerveHomotopy` | `VtxNerveHomotopy` | [Instance/Set/Simplicial/Vertex/Homotopy.v](../theories/Instance/Set/Simplicial/Vertex/Homotopy.v) |
| `VertexNerveHomotopyN` | `VtxNerveHomotopyN` | [Instance/Set/Simplicial/Vertex/Homotopy.v](../theories/Instance/Set/Simplicial/Vertex/Homotopy.v) |
| `VertexNerveInvF` | `VtxNerveInvF` | [Instance/Set/Simplicial/Vertex/Reconstruction.v](../theories/Instance/Set/Simplicial/Vertex/Reconstruction.v) |
| `VertexNerveInvHomotopyN` | `VtxNerveInvHomotopyN` | [Instance/Set/Simplicial/Vertex/HomotopyInv.v](../theories/Instance/Set/Simplicial/Vertex/HomotopyInv.v) |
| `VertexNerveN` | `VtxNerveN` | [Instance/Set/Simplicial/Vertex/Functor.v](../theories/Instance/Set/Simplicial/Vertex/Functor.v) |
| `VertexNerveProduct` | `VtxNerveProduct` | [Instance/Set/Simplicial/Vertex/Product.v](../theories/Instance/Set/Simplicial/Vertex/Product.v) |
| `VertexNerveProductInvN` | `VtxNerveProductInvN` | [Instance/Set/Simplicial/Vertex/Product.v](../theories/Instance/Set/Simplicial/Vertex/Product.v) |
| `VertexNerveProductN` | `VtxNerveProductN` | [Instance/Set/Simplicial/Vertex/Product.v](../theories/Instance/Set/Simplicial/Vertex/Product.v) |
| `VertexNerveTerminalInvN` | `VtxNerveTerminalInvN` | [Instance/Set/Simplicial/Vertex/Terminal.v](../theories/Instance/Set/Simplicial/Vertex/Terminal.v) |
| `VertexNerveTerminalN` | `VtxNerveTerminalN` | [Instance/Set/Simplicial/Vertex/Terminal.v](../theories/Instance/Set/Simplicial/Vertex/Terminal.v) |
| `VertexPairF` | `VtxPairF` | [Instance/Set/Vertex/Product.v](../theories/Instance/Set/Vertex/Product.v) |
| `VertexPresentation` | `VtxPresentation` | [Instance/Set/Vertex/Category.v](../theories/Instance/Set/Vertex/Category.v) |
| `VertexPresentationCat` | `VtxPresentationCat` | [Instance/Set/Vertex/Category.v](../theories/Instance/Set/Vertex/Category.v) |
| `VertexPresentationCat_HasProduct` | `VtxPresentationCat_HasProduct` | [Instance/Set/Vertex/FiniteProducts.v](../theories/Instance/Set/Vertex/FiniteProducts.v) |
| `VertexPresentationCat_HasTerminal` | `VtxPresentationCat_HasTerminal` | [Instance/Set/Vertex/FiniteProducts.v](../theories/Instance/Set/Vertex/FiniteProducts.v) |
| `VertexPresentationMap` | `VtxPresentationMap` | [Instance/Set/Vertex/Category.v](../theories/Instance/Set/Vertex/Category.v) |
| `VertexPresentationOf` | `VtxPresentationOf` | [Instance/Set/Vertex/Category.v](../theories/Instance/Set/Vertex/Category.v) |
| `VertexPresentationProduct` | `VtxPresentationProduct` | [Instance/Set/Vertex/FiniteProducts.v](../theories/Instance/Set/Vertex/FiniteProducts.v) |
| `VertexPresentationTerminal` | `VtxPresentationTerminal` | [Instance/Set/Vertex/FiniteProducts.v](../theories/Instance/Set/Vertex/FiniteProducts.v) |
| `VertexProductF` | `VtxProductF` | [Instance/Set/Vertex/Product.v](../theories/Instance/Set/Vertex/Product.v) |
| `VertexProductObjF` | `VtxProductObjF` | [Instance/Set/Vertex/Product.v](../theories/Instance/Set/Vertex/Product.v) |
| `VertexRelabelF` | `VtxRelabelF` | [Instance/Set/Vertex/Relabel.v](../theories/Instance/Set/Vertex/Relabel.v) |
| `VertexSieveF` | `VtxSieveF` | [Instance/Set/Simplicial/Vertex/Sieve.v](../theories/Instance/Set/Simplicial/Vertex/Sieve.v) |
| `VertexSimplex` | `VtxSimplex` | [Instance/Set/Simplicial/Vertex/Core.v](../theories/Instance/Set/Simplicial/Vertex/Core.v) |
| `VertexSndF` | `VtxSndF` | [Instance/Set/Vertex/Product.v](../theories/Instance/Set/Vertex/Product.v) |
| `VertexTerminalF` | `VtxTerminalF` | [Instance/Set/Vertex/Terminal.v](../theories/Instance/Set/Vertex/Terminal.v) |
| `VertexTerminalObjF` | `VtxTerminalObjF` | [Instance/Set/Vertex/Terminal.v](../theories/Instance/Set/Vertex/Terminal.v) |

Source module names and paths containing `Vertex` remain unchanged. Selective
imports adapt their public declaration names while keeping their namespace.
Coqdoc code references and qualified `\coqref` targets migrate in both languages;
ordinary mathematical prose keeps “vertex”. Descriptive lowercase helpers,
including `vertex_*`, are not mechanically renamed. The remaining `Clos`,
`*ClosOp`, `Exp` and `Cart` families, optional `Prof` proposals, notation and
structural experiments remain separate work.

含 Vertex 的模块名及路径保持原样；选择性导入只更新公开声明名，保留命名空间。
双语 coqdoc 代码引用及带限定名的交叉引用同步迁移，普通数学叙述保留原词。
描述性小写辅助名不机械缩写；其余词族、新候选、记号及结构实验仍为独立工作。

### Batch 3 validation / 第三批验证

On this local working tree, project-switch `dune build @all` passed with
Rocq/Stdlib 9.2, OCaml 5.3.0 and Dune 3.23.1. The temporary audit checked all
166 current public targets with printed universes and `Print Assumptions`;
all 166 reports were closed. All 174 retired/intermediate-name `Fail Check`
probes passed, as did graph-projection computation and the vertex-category
and identity-functor coercion probes.

当前本地工作树使用项目 switch 的全库构建通过，工具链为 Rocq/Stdlib 9.2、
OCaml 5.3.0、Dune 3.23.1。临时审计覆盖全部 166 个现名的带宇宙签名与假设，
166 项假设报告全部闭合；174 项退役／中间名检查、图顶点投影计算及顶点范畴、
恒等函子的强制转换探针均通过。

The source audit reversed all 63 changed Rocq files exactly to the baseline,
apart from five record-closing indentation adjustments. Module imports and
selective-import namespaces are unchanged; 20 qualified coqdoc cross-reference
targets migrated within their original namespaces. All 175 historical/current
mapping rows resolve to existing source files and current names, and
`git diff --check` passed. These are temporary checks, with no new permanent
tests or HTML/PDF export. The user authorized freezing this validated batch
for integration; its source branch must remain unchanged during acceptance.
This is L2 breaking public-name migration, requiring affected-session
preservation/pause confirmations before integration and synchronization with
validation afterward.

源码审计确认：63 个 Rocq 文件逆向替换后与基线逐行一致，仅有五处记录闭合缩进
调整；模块导入和选择性导入命名空间保持原样，20 处带限定名交叉引用在原命名空间
内迁移。175 行历史／当前映射的源码与现名均可定位，差异空白检查通过。审计均为
临时检查，未增加永久测试，未导出 HTML/PDF。用户已授权冻结本批交付集成，
验收期间保全来源分支。本批为 L2 breaking 公开改名，集成前须取得受影响会话
的保全／暂停确认，集成后须同步并验证。

## Batch 4: Clos, Exp, Cart and Prof / 第四批：合并词族

The user approved `Prof` and requested completing these remaining families
in one batch. This work starts from integrated
`7d6e9da929a71590021ceb7deeca9238a4d017aa` on
`abbreviations-clos-exp-cart-prof-38`. All earlier frozen sources remain
preserved. This batch has 195 exact entries: 194 declarations/fields and one
scope. The user subsequently approved committing, publishing and submitting
this validated batch to the designated integrator. Keep its source frozen
during acceptance; integration remains pending.

用户批准 Prof，并安排剩余 Clos/ClosOp、Exp、Cart 与 Prof 合并处理。本批从
已集成 `7d6e9da` 在新短分支 `abbreviations-clos-exp-cart-prof-38` 开始，前序
冻结来源保全。195 项精确映射包括 194 个声明／字段和一个 scope；用户随后
批准提交、推送并交付指定集成会话，验收期间冻结来源，集成待完成。

For the #16 path-breaking integration, preserve the original WIP in the named
stash `wip-38-clos-exp-cart-prof-before-etcs-path-16` at
`61c28df28a5f6b14e4fe32ca9fb3d03c2487dcc6`. Following the explicit synchronization
instruction, only this unintegrated WIP was restored, without conflicts, onto
`bc446abd3d7bc844d221d290830cfb2f312ba743` on
`abbreviations-clos-exp-cart-prof-synced-bc446ab`. The 195-entry map is unchanged;
current source links and temporary audit imports use `Topos.ETCS`, `Topos.Nat`
and `Topos.Sub`. The new baseline also includes the CI dependency repair.
Old branches, stashes and frozen submissions remain preserved.

因 #16 路径 breaking 集成，原 WIP 已保全至上述命名 stash。按明确同步指令，
仅将未集成 WIP 无冲突恢复到 `bc446ab` 的新短分支，195 项精确映射保持不变；
现行源码定位及临时审计导入采用新的 Topos 路径。新基线也包含 CI 依赖修复；
旧分支、stash 及冻结来源继续保留。

### Reviewed mathematical boundaries / 已核对的数学边界

Generic operators use `Clos`; raw generated relations use `*Clos`.
`FamilyEquivalenceClosure` returns a packaged closure on the inclusion preorder
of relation families, so its target is `FamilyEquivClosOp`. The packaged
compatible and congruence operators similarly become `CompatibleClosOp` and
`CongruenceClosOp`; their raw context/equational relations use `ContextClos`
and `EquationalClos`. The records, Type-valued witnesses, selected maps,
coercions and universe bounds remain the same.

一般闭包算子采用 Clos，底层生成关系采用 *Clos。逐纤维等价闭包实际返回关系族
包含预序上的打包算子，因此采用 FamilyEquivClosOp；相容及合同打包算子也采用
ClosOp，其底层上下文／方程关系则采用 Clos。记录、Type 值见证、选定映射、
强制转换及宇宙界保持原样。

The `Prof` family includes the reviewed public lowercase operations and laws,
the composition/strength fields, Hom constructions, instance and scope names.
`FunctorHomProfunctor` is the Hom profunctor reindexed along two supplied
functors, hence `FctHomProf`. `Prof` remains the existing mixed-variance `Fct`
alias; `ProfCat` remains its ordinary functor category. There is no new class
or bifunctor implementation. The existing notation and `%profunctor` delimiter
remain; only the scope's registered name becomes `prof_scope`.

Prof 词族包含经审阅的公开小写操作与定律、复合／强度字段、Hom 构造、实例和
scope 名。两个给定函子对 Hom profunctor 重索引的构造采用 FctHomProf。
Prof 仍是已有混合变元 Fct 别名，ProfCat 仍是通常函子范畴，不新增结构类或
双函子实现。现有记号及 scope 分隔符保留，只将 scope 注册名缩为 prof_scope。

Keep `HasExponential`, `hasExponential`, `CartesianCat`, `CartesianC`,
`hasCartesian` and the matching `Gluing_CartesianCat` instance. The complete
cartesian hierarchy is reserved for separate review. Cartesian lift names
have been inventoried with their arrow-category, CwF and set-family clients;
these names change without changing any lifting property or chosen data.
Other descriptive lowercase helpers and test-only `WitnessClosure` remain.
Module paths, section names and ordinary mathematical prose are unchanged.
Optional `NatPrism`, `CtxCatEquiv`, `NNO`, `Gpd`, reserved notation and structural
experiments remain separate.

保留 HasExponential 选定接口及完整 CartesianCat 层级、投影／选择字段与对应
Gluing 实例；完整层级另行审阅。笛卡尔提升已盘点箭头范畴、CwF 和广集族的
客户端，只迁移名称，保留提升性质与选择数据。其他描述性小写辅助名和仅供测试的
WitnessClosure 保留；模块路径、Section 名及普通数学叙述不改。可选缩写、
预留记号及结构实验另行安排。

### Clos / 闭包

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `Closure` | `Clos` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `ClosureEq` | `ClosEq` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `ClosureEq_Equivalence` | `ClosEq_Equivalence` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `ClosureF` | `ClosF` | [Instance/Preorder/Closure.v](../theories/Instance/Preorder/Closure.v) |
| `ClosureFromUniversal` | `ClosFromUniversal` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `ClosureLe` | `ClosLe` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `ClosureLe_PreOrder` | `ClosLe_PreOrder` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `ClosureMonad` | `ClosMonad` | [Instance/Preorder/Closure.v](../theories/Instance/Preorder/Closure.v) |
| `CompatibleClosure` | `CompatibleClosOp` | [Set/Relation/Compatible.v](../theories/Set/Relation/Compatible.v) |
| `CompositeClosure` | `CompositeClos` | [Set/Closure/Composition.v](../theories/Set/Closure/Composition.v) |
| `CongruenceClosure` | `CongruenceClosOp` | [Set/Relation/Congruence.v](../theories/Set/Relation/Congruence.v) |
| `CongruenceClosure_Equivalence` | `CongruenceClosOp_Equivalence` | [Set/Relation/Congruence.v](../theories/Set/Relation/Congruence.v) |
| `CongruenceClosure_proper` | `CongruenceClosOp_proper` | [Set/Relation/Congruence.v](../theories/Set/Relation/Congruence.v) |
| `ContextClosure` | `ContextClos` | [Set/Relation/Compatible.v](../theories/Set/Relation/Compatible.v) |
| `ContextClosure_proper` | `ContextClos_proper` | [Set/Relation/Compatible.v](../theories/Set/Relation/Compatible.v) |
| `EquationalClosure` | `EquationalClos` | [Set/Relation/Congruence.v](../theories/Set/Relation/Congruence.v) |
| `EquationalClosure_Equivalence` | `EquationalClos_Equivalence` | [Set/Relation/Congruence.v](../theories/Set/Relation/Congruence.v) |
| `EquationalClosure_proper` | `EquationalClos_proper` | [Set/Relation/Congruence.v](../theories/Set/Relation/Congruence.v) |
| `EquivClosure` | `EquivClos` | [Set/Generated.v](../theories/Set/Generated.v) |
| `EquivClosure_Equivalence` | `EquivClos_Equivalence` | [Set/Generated.v](../theories/Set/Generated.v) |
| `EquivalenceClosure` | `EquivClosOp` | [Set/Relation/Equivalence.v](../theories/Set/Relation/Equivalence.v) |
| `EquivalenceClosure_Equivalence` | `EquivClosOp_Equivalence` | [Set/Relation/Equivalence.v](../theories/Set/Relation/Equivalence.v) |
| `EquivalenceClosure_proper` | `EquivClosOp_proper` | [Set/Relation/Equivalence.v](../theories/Set/Relation/Equivalence.v) |
| `FamilyEquivalenceClosure` | `FamilyEquivClosOp` | [Set/Relation/Family.v](../theories/Set/Relation/Family.v) |
| `FamilyEquivalenceClosure_proper` | `FamilyEquivClosOp_proper` | [Set/Relation/Family.v](../theories/Set/Relation/Family.v) |
| `IdentityClosure` | `IdentityClos` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `PointwiseClosure` | `PointwiseClos` | [Set/Closure/Pointwise.v](../theories/Set/Closure/Pointwise.v) |
| `ReflTransClosure` | `ReflTransClos` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `ReflTransClosure_PreOrder` | `ReflTransClos_PreOrder` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `ReflTransClosure_Symmetric` | `ReflTransClos_Symmetric` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `ReflTransClosure_proper` | `ReflTransClos_proper` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `ReflexiveTransitiveClosure` | `ReflTransClosOp` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `SymClosure` | `SymClos` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `SymClosure_Symmetric` | `SymClos_Symmetric` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `SymClosure_proper` | `SymClos_proper` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `SymmetricClosure` | `SymClosOp` | [Set/Relation/Closure.v](../theories/Set/Relation/Closure.v) |
| `TmEquationalClosure` | `TmEquationalClos` | [STLC/Reduction.v](../theories/STLC/Reduction.v) |

### Exp / 指数构造

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `ExponentialBiF` | `ExpBiF` | [Cat/Exponential/Functor.v](../theories/Cat/Exponential/Functor.v) |
| `ExponentialContraF` | `ExpContraF` | [Cat/Exponential/Functor.v](../theories/Cat/Exponential/Functor.v) |
| `ExponentialF` | `ExpF` | [Cat/Exponential/Core.v](../theories/Cat/Exponential/Core.v) |
| `ExponentialF_IsCartF` | `ExpF_IsCartF` | [Cat/Limit/Exponential.v](../theories/Cat/Limit/Exponential.v) |
| `ExponentialFixedN` | `ExpFixedN` | [Cat/Exponential/Functor.v](../theories/Cat/Exponential/Functor.v) |
| `ExponentialIteratedN` | `ExpIteratedN` | [Cat/Exponential/Currying.v](../theories/Cat/Exponential/Currying.v) |
| `ExponentialProductN` | `ExpProdN` | [Cat/Exponential/Laws.v](../theories/Cat/Exponential/Laws.v) |
| `ExponentialUnitN` | `ExpUnitN` | [Cat/Exponential/Laws.v](../theories/Cat/Exponential/Laws.v) |

### Cart / 笛卡尔构造

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `ArrowCodF_HasCartesianLift` | `ArrowCodF_HasCartLift` | [Cat/Arrow/Fibration.v](../theories/Cat/Arrow/Fibration.v) |
| `CartesianAssociatorN` | `CartAssociatorN` | [Cat/Monoidal/Cartesian.v](../theories/Cat/Monoidal/Cartesian.v) |
| `CartesianLeftUnitorIso` | `CartLeftUnitorIso` | [Cat/Monoidal/Cartesian.v](../theories/Cat/Monoidal/Cartesian.v) |
| `CartesianLeftUnitorN` | `CartLeftUnitorN` | [Cat/Monoidal/Cartesian.v](../theories/Cat/Monoidal/Cartesian.v) |
| `CartesianLift` | `CartLift` | [Cat/Fibration.v](../theories/Cat/Fibration.v) |
| `CartesianMonoid` | `CartMonoid` | [Cat/Monoidal/Cartesian.v](../theories/Cat/Monoidal/Cartesian.v) |
| `CartesianMonoidal` | `CartMonoidal` | [Cat/Monoidal/Cartesian.v](../theories/Cat/Monoidal/Cartesian.v) |
| `CartesianRightUnitorIso` | `CartRightUnitorIso` | [Cat/Monoidal/Cartesian.v](../theories/Cat/Monoidal/Cartesian.v) |
| `CartesianRightUnitorN` | `CartRightUnitorN` | [Cat/Monoidal/Cartesian.v](../theories/Cat/Monoidal/Cartesian.v) |
| `CartesianSymmetricPremonoidal` | `CartSymmetricPremonoidal` | [Cat/Premonoidal/Cartesian.v](../theories/Cat/Premonoidal/Cartesian.v) |
| `CtxCat_Cartesian` | `CtxCat_Cart` | [STLC/CCC.v](../theories/STLC/CCC.v) |
| `CwFBaseF_HasCartesianLift` | `CwFBaseF_HasCartLift` | [DTT/Comprehension.v](../theories/DTT/Comprehension.v) |
| `FamBaseF_HasCartesianLift` | `FamBaseF_HasCartLift` | [Instance/Set/Fam/Fibration.v](../theories/Instance/Set/Fam/Fibration.v) |
| `HasCartesianLift` | `HasCartLift` | [Cat/Fibration.v](../theories/Cat/Fibration.v) |
| `SetCartesianMonoidal` | `SetCartMonoidal` | [Instance/Set/Monoid.v](../theories/Instance/Set/Monoid.v) |
| `SetCat_Cartesian` | `SetCat_Cart` | [Instance/Set/Cartesian.v](../theories/Instance/Set/Cartesian.v) |
| `TyCat_Cartesian` | `TyCat_Cart` | [STLC/TypeCategory.v](../theories/STLC/TypeCategory.v) |

### Prof family / Prof 词族

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `FunctorHomProfunctor` | `FctHomProf` | [Cat/Profunctor/Hom.v](../theories/Cat/Profunctor/Hom.v) |
| `HasProfunctorComp` | `HasProfComp` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `HasProfunctorStrength` | `HasProfStrength` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |
| `HomProfunctor` | `HomProf` | [Cat/Profunctor/Hom.v](../theories/Cat/Profunctor/Hom.v) |
| `HomProfunctorMapN` | `HomProfMapN` | [Cat/Profunctor/Hom.v](../theories/Cat/Profunctor/Hom.v) |
| `HomProfunctorStrength` | `HomProfStrength` | [Cat/Profunctor/HomStrength.v](../theories/Cat/Profunctor/HomStrength.v) |
| `HomProfunctorStrengthN` | `HomProfStrengthN` | [Cat/Profunctor/HomStrength.v](../theories/Cat/Profunctor/HomStrength.v) |
| `Profunctor` | `Prof` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `ProfunctorCat` | `ProfCat` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `ProfunctorComp` | `ProfComp` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `ProfunctorCompBoundaryN` | `ProfCompBoundaryN` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `ProfunctorCompCowedge` | `ProfCompCowedge` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `ProfunctorCompF` | `ProfCompF` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `ProfunctorCompInputN` | `ProfCompInputN` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `ProfunctorCompKernel` | `ProfCompKernel` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `ProfunctorCompMapN` | `ProfCompMapN` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `ProfunctorContext` | `ProfContext` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |
| `ProfunctorLeftUnitComp` | `ProfLeftUnitComp` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLeftUnitCowedge` | `ProfLeftUnitCowedge` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLeftUnitIso` | `ProfLeftUnitIso` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLeftUnitKernelInvN` | `ProfLeftUnitKernelInvN` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLeftUnitKernelN` | `ProfLeftUnitKernelN` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLeftUnitor` | `ProfLeftUnitor` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLeftUnitorInvN` | `ProfLeftUnitorInvN` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLeftUnitorN` | `ProfLeftUnitorN` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `ProfunctorLmapN` | `ProfLmapN` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `ProfunctorReindex` | `ProfReindex` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `ProfunctorReindexF` | `ProfReindexF` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `ProfunctorReindexN` | `ProfReindexN` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `ProfunctorRightUnitComp` | `ProfRightUnitComp` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRightUnitCowedge` | `ProfRightUnitCowedge` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRightUnitIso` | `ProfRightUnitIso` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRightUnitKernelInvN` | `ProfRightUnitKernelInvN` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRightUnitKernelN` | `ProfRightUnitKernelN` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRightUnitor` | `ProfRightUnitor` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRightUnitorInvN` | `ProfRightUnitorInvN` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRightUnitorN` | `ProfRightUnitorN` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `ProfunctorRmapN` | `ProfRmapN` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `SetCat_ProfunctorComp` | `SetCat_ProfComp` | [Instance/Set/ProfunctorComp.v](../theories/Instance/Set/ProfunctorComp.v) |
| `functor_hom_profunctor_dimap` | `fct_hom_prof_dimap` | [Cat/Profunctor/Hom.v](../theories/Cat/Profunctor/Hom.v) |
| `hasProfunctorCompCoend` | `hasProfCompCoend` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `hom_profunctor_dimap` | `hom_prof_dimap` | [Cat/Profunctor/Hom.v](../theories/Cat/Profunctor/Hom.v) |
| `hom_profunctor_lmap` | `hom_prof_lmap` | [Cat/Profunctor/Hom.v](../theories/Cat/Profunctor/Hom.v) |
| `hom_profunctor_rmap` | `hom_prof_rmap` | [Cat/Profunctor/Hom.v](../theories/Cat/Profunctor/Hom.v) |
| `hom_profunctor_strength` | `hom_prof_strength` | [Cat/Profunctor/HomStrength.v](../theories/Cat/Profunctor/HomStrength.v) |
| `profunctor_comp_boundary_comp` | `prof_comp_boundary_comp` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `profunctor_comp_boundary_id` | `prof_comp_boundary_id` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `profunctor_comp_boundary_inject` | `prof_comp_boundary_inject` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_boundary_proper` | `prof_comp_boundary_proper` | [Cat/Profunctor/Compose.v](../theories/Cat/Profunctor/Compose.v) |
| `profunctor_comp_cowedge_gluing` | `prof_comp_cowedge_gluing` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_cowedge_η` | `prof_comp_cowedge_η` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_desc` | `prof_comp_desc` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_desc_input` | `prof_comp_desc_input` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_desc_unique` | `prof_comp_desc_unique` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_desc_β` | `prof_comp_desc_β` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_desc_η` | `prof_comp_desc_η` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_dimap_inject` | `prof_comp_dimap_inject` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_gluing` | `prof_comp_gluing` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_hom_ext` | `prof_comp_hom_ext` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_inject` | `prof_comp_inject` | [Cat/Profunctor/ComposeUniversal.v](../theories/Cat/Profunctor/ComposeUniversal.v) |
| `profunctor_comp_input_boundary` | `prof_comp_input_boundary` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_input_comp` | `prof_comp_input_comp` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_input_id` | `prof_comp_input_id` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_input_inject` | `prof_comp_input_inject` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_input_proper` | `prof_comp_input_proper` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_left_parameter_desc` | `prof_comp_left_parameter_desc` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_left_parameter_hom_ext` | `prof_comp_left_parameter_hom_ext` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_left_parameter_map` | `prof_comp_left_parameter_map` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_left_parameter_unique` | `prof_comp_left_parameter_unique` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_left_parameter_β` | `prof_comp_left_parameter_β` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_map_comp` | `prof_comp_map_comp` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_map_id` | `prof_comp_map_id` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_map_inject` | `prof_comp_map_inject` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_map_iso` | `prof_comp_map_iso` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_map_proper` | `prof_comp_map_proper` | [Cat/Profunctor/ComposeMap.v](../theories/Cat/Profunctor/ComposeMap.v) |
| `profunctor_comp_parameter_boundary` | `prof_comp_parameter_boundary` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_parameter_change` | `prof_comp_parameter_change` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_parameter_desc` | `prof_comp_parameter_desc` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_parameter_hom_ext` | `prof_comp_parameter_hom_ext` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_parameter_map` | `prof_comp_parameter_map` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_parameter_proper` | `prof_comp_parameter_proper` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_parameter_unique` | `prof_comp_parameter_unique` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_comp_parameter_β` | `prof_comp_parameter_β` | [Cat/Profunctor/Parameter.v](../theories/Cat/Profunctor/Parameter.v) |
| `profunctor_dimap` | `prof_dimap` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_dimap_comp` | `prof_dimap_comp` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_dimap_id` | `prof_dimap_id` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_dimap_l_r` | `prof_dimap_l_r` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_dimap_proper` | `prof_dimap_proper` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_dimap_r_l` | `prof_dimap_r_l` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_interchange` | `prof_interchange` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_left_unit_eval_boundary` | `prof_left_unit_eval_boundary` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_factor` | `prof_left_unit_factor` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_in` | `prof_left_unit_in` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_in_out` | `prof_left_unit_in_out` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_kernel_iso` | `prof_left_unit_kernel_iso` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_out` | `prof_left_unit_out` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_out_in` | `prof_left_unit_out_in` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_out_input` | `prof_left_unit_out_input` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_universal` | `prof_left_unit_universal` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unit_β` | `prof_left_unit_β` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unitor_inv_natural` | `prof_left_unitor_inv_natural` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_left_unitor_natural` | `prof_left_unitor_natural` | [Cat/Profunctor/LeftUnit.v](../theories/Cat/Profunctor/LeftUnit.v) |
| `profunctor_lmap` | `prof_lmap` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_lmap_comp` | `prof_lmap_comp` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_lmap_id` | `prof_lmap_id` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_lmap_proper` | `prof_lmap_proper` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_natural` | `prof_natural` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_reindex_dimap` | `prof_reindex_dimap` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_reindex_iso` | `prof_reindex_iso` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_reindex_map` | `prof_reindex_map` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_right_unit_eval_boundary` | `prof_right_unit_eval_boundary` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_factor` | `prof_right_unit_factor` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_in` | `prof_right_unit_in` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_in_out` | `prof_right_unit_in_out` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_kernel_iso` | `prof_right_unit_kernel_iso` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_out` | `prof_right_unit_out` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_out_in` | `prof_right_unit_out_in` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_out_input` | `prof_right_unit_out_input` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_universal` | `prof_right_unit_universal` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unit_β` | `prof_right_unit_β` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unitor_inv_natural` | `prof_right_unitor_inv_natural` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_right_unitor_natural` | `prof_right_unitor_natural` | [Cat/Profunctor/RightUnit.v](../theories/Cat/Profunctor/RightUnit.v) |
| `profunctor_rmap` | `prof_rmap` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_rmap_comp` | `prof_rmap_comp` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_rmap_id` | `prof_rmap_id` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_rmap_proper` | `prof_rmap_proper` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_scope` | `prof_scope` | [Cat/Profunctor/Core.v](../theories/Cat/Profunctor/Core.v) |
| `profunctor_strength` | `prof_strength` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |
| `profunctor_strengthN` | `prof_strengthN` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |
| `profunctor_strength_assoc` | `prof_strength_assoc` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |
| `profunctor_strength_context` | `prof_strength_context` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |
| `profunctor_strength_natural` | `prof_strength_natural` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |
| `profunctor_strength_unit` | `prof_strength_unit` | [Cat/Profunctor/Strength.v](../theories/Cat/Profunctor/Strength.v) |

### Batch 4 validation / 第四批验证

Before synchronization, the `7d6e9da` working tree passed project-switch
`dune build -j2 @all` and the temporary 359-signature/assumption audit, with all
reports closed. Its 368 retired-name probes, old/new scope checks, definitional
and strict-universe probes passed. These results describe that earlier WIP,
not the later synchronized baseline.

同步前的 `7d6e9da` 工作树已通过项目 switch 全库构建及 359 项临时签名／假设
审计，报告全部闭合；368 项退役名、scope、定义计算及严格宇宙探针也通过。
这些结果只描述旧 WIP，不作为同步后基线的验证结论。

On the synchronized `bc446ab` working tree, project-switch
`dune build -j2 @all @install` passed with Rocq/Stdlib 9.2, OCaml 5.3.0 and
Dune 3.23.1. The regenerated temporary audit passed all 359 signatures with
printed universes and 359 closed assumption reports, 368 retired-name probes,
old/new scope checks, Prof alias/category definitional comparisons, both
strict carrier/equality universe orders, closure computations and the earlier
Graph/Vtx computation/coercion probes.

同步至 `bc446ab` 的工作树使用项目 switch 全库及安装目标构建通过，工具链为
Rocq/Stdlib 9.2、OCaml 5.3.0、Dune 3.23.1。重新生成的临时审计覆盖全部
359 项带宇宙签名与假设，报告全部闭合；368 项退役名、新旧 scope、Prof 别名／
范畴定义相等、载体与相等见证宇宙的两种严格次序、闭包计算及原 Graph/Vtx
计算／强制转换探针均通过。

The source audit confirms 104 Rocq files reverse exactly to this new baseline,
with no extra edits; module imports and namespaces are unchanged. All 370 map
rows, referring to 359 declarations/fields and one scope, resolve to current
names and source files. A loader mirror containing only the 539 current source
modules passed three retired-ETCS `Fail Require` probes and direct imports of
the new modules; the install manifest contains no old paths. Current sources
and docs contain no retired ETCS imports or local links. Whitespace checks
passed. These are temporary audits; no new permanent tests or HTML/PDF export.
The user approved freezing this validated batch for submission. This is an
L2 breaking public-name migration; before integration, the designated
integrator coordinates preserved pauses with affected consumers, then renewed
validation and synchronization. Further work awaits user instructions.

精确源码审计确认：104 个 Rocq 文件逆向替换后与新基线完全一致，零额外改动，
导入及命名空间不变；370 行对照涉及 359 个声明／字段和一个 scope，现名及
源码定位均有效。仅包含 539 个当前源码模块的加载镜像中，三个旧 ETCS 模块的
导入失败检查、新模块直接导入均通过；安装清单无旧路径，现行源码和文档无退役
ETCS 导入或本地链接，差异空白检查通过。均为临时审计，未增加永久测试或导出
HTML/PDF。用户已批准冻结交付本批；本批为 L2 breaking 公开名称迁移，由指定
集成者协调受影响消费者保全／暂停，复验后集成并同步。后续工作等待用户安排。

### Upstream client compatibility / 上游客户端兼容

The frozen source `315dbda` was rebased by the integrator onto `a92b026`,
yielding temporary result `98dec6e`. A separate compatibility branch starts
from that exact result and adapts the later
[iterated composition](../theories/Cat/Profunctor/Iterated.v) and
[associator](../theories/Cat/Profunctor/Associator.v) clients using only the
existing 195-entry map: 139 exact replacements, including their two scope
openings. Their new declarations keep their existing names; module paths,
ordinary prose, notation, proofs and mathematical choices are preserved.
The map remains 370 historical rows referring to 359 declarations/fields
and one scope. Across the original batch and this repair, all 106 changed
Rocq files reverse byte-for-byte to `a92b026`. The original source and
backups remain preserved. The integrator accepted and pushed the exact repair
as `76642d4`, which is also the final integration result.

集成者将冻结来源 `315dbda` 重基至 `a92b026`，得到临时结果 `98dec6e`。
独立兼容分支严格从该结果开始，仅按已有 195 项表适配后来新增的
[迭代复合](../theories/Cat/Profunctor/Iterated.v)与
[结合子](../theories/Cat/Profunctor/Associator.v)客户端，共 139 处精确替换，
其中包括两处 scope 开启。新增声明保留原名；模块路径、普通叙述、记号、证明
及数学选择均保持。对照表仍为 370 条历史行，对应 359 个声明／字段及一个
scope。原批次与本修订合计 106 个 Rocq 文件，逆向后与 `a92b026` 逐字一致。
原来源与备份保全；集成者已原样验收并推送修订 `76642d4`，最终来源与结果同 SHA。

The repaired tree passed project-switch compilation of both affected modules
and `dune build -j2 @all @install`. The original temporary audit was copied
unchanged and passed 359 universe signatures/closed assumption reports,
368 retired-name probes and its computation/coercion/strict-universe checks.
A supplementary audit passed 42 client signatures/closed reports (39 explicit
declarations and three record fields); importing the new clients also passed
the same 368 retired-name probes and old/new scope checks. The unchanged map,
source reverse comparison, guide links and whitespace checks passed. These
remain temporary checks; no new permanent tests or HTML/PDF export.

修订工作树使用项目 switch 通过两个模块定向编译及全库／安装目标构建。
原临时审计原样复制复跑，359 项带宇宙签名／假设全部闭合，368 项退役名及
原计算／强制转换／严格宇宙检查通过。补充检查覆盖 42 项客户端签名／闭合
报告（39 个显式声明及三个记录字段）；导入新增客户端后，同样的 368 项
退役名及新旧 scope 检查也通过。原表、源码逆向、指南链接及差异空白检查
通过。均为临时检查，未增加永久测试或导出 HTML/PDF。

## Algebra interface ergonomics / 代数接口易用性

This separate exact map implements the user-authorized ergonomic follow-up
to [architecture #42](https://github.com/Godalin/rocq-cats/issues/42), with
implementation in [#15](https://github.com/Godalin/rocq-cats/issues/15) and
[naming review in #38](https://github.com/Godalin/rocq-cats/issues/38#issuecomment-6908412626).
It starts at `hierarchy-packed-algebra-42@e30adfa`; the 54 entries below are
implemented and locally validated for the current user-review checkpoint.
This is not an extension of the historical 195-entry Batch 4 abbreviation
table or an integration
submission. Module paths, chosen data and multiplication notations stay
unchanged; no compatibility aliases are introduced.

本独立精确表落实用户授权的 [#42 架构易用性后续](https://github.com/Godalin/rocq-cats/issues/42)，
具体实现归 [#15](https://github.com/Godalin/rocq-cats/issues/15)，
[命名审阅归 #38](https://github.com/Godalin/rocq-cats/issues/38#issuecomment-6908412626)。
从 `hierarchy-packed-algebra-42@e30adfa` 开始，以下 54 项已完成本地实施及
验证，作为当前用户审阅检查点；不扩充历史第四批 195 项缩写表，也不表示提交
集成。模块路径、选定数据及乘法记号保持不变，不增加兼容别名。

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `MagmaS` | `MagmaToSetC` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `SemigroupM` | `SemigroupToMagma` | [Algebra/Semigroup/Core.v](../theories/Algebra/Semigroup/Core.v) |
| `MonoidSG` | `MonoidToSemigroup` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `GroupM` | `GroupToMonoid` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `magma_mul` | `mul` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `monoid_unit` | `mul_unit` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `magma_mul_proper` | `mul_proper` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `semigroup_assoc` | `mul_assoc` | [Algebra/Semigroup/Core.v](../theories/Algebra/Semigroup/Core.v) |
| `monoid_unit_l` | `mul_unit_l` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `monoid_unit_r` | `mul_unit_r` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `group_inv_l` | `mul_inv_l` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_inv_r` | `mul_inv_r` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `magma_mul_l_resp` | `mul_l_resp` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `magma_mul_r_resp` | `mul_r_resp` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `magma_mul_l_proper` | `mul_l_proper` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `magma_mul_r_proper` | `mul_r_proper` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `group_inv` | `inv` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_inv_unique` | `inv_unique` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_inv_proper` | `inv_proper` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_inv_unit` | `inv_unit` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_inv_inv` | `inv_inv` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_inv_mul` | `inv_mul` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_inv_resp` | `inv_resp` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `semigroup_mul_l_comp` | `mul_l_comp` | [Algebra/Semigroup/Core.v](../theories/Algebra/Semigroup/Core.v) |
| `semigroup_mul_r_comp` | `mul_r_comp` | [Algebra/Semigroup/Core.v](../theories/Algebra/Semigroup/Core.v) |
| `semigroup_mul_lr_comm` | `mul_lr_comm` | [Algebra/Semigroup/Core.v](../theories/Algebra/Semigroup/Core.v) |
| `monoid_units_equiv` | `units_equiv` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `monoid_extension_inverse_unique` | `mul_ext_inv_unique` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `monoid_inverse_unique` | `mul_inv_unique` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `group_inverse_candidates_equiv` | `inv_candidates_equiv` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `group_extension_inv_unique` | `inv_ext_unique` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `monoid_mul_comm` | `mul_comm` | [Algebra/Monoid/Commutative.v](../theories/Algebra/Monoid/Commutative.v) |
| `monoid_mul_interchange` | `mul_interchange` | [Algebra/Monoid/Commutative.v](../theories/Algebra/Monoid/Commutative.v) |
| `group_mul_cancel_l` | `mul_cancel_l` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_cancel_r` | `mul_cancel_r` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_l_solution` | `mul_l_solution` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_r_solution` | `mul_r_solution` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_l_solve_resp` | `mul_l_solve_resp` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_r_solve_resp` | `mul_r_solve_resp` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_l_solve_proper` | `mul_l_solve_proper` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_r_solve_proper` | `mul_r_solve_proper` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_l_solve_β` | `mul_l_solve_β` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_l_solve_η` | `mul_l_solve_η` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_r_solve_β` | `mul_r_solve_β` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `group_mul_r_solve_η` | `mul_r_solve_η` | [Algebra/Group/Equation.v](../theories/Algebra/Group/Equation.v) |
| `IsCommutativeMonoid` | `IsCommMonoid` | [Algebra/Monoid/Commutative.v](../theories/Algebra/Monoid/Commutative.v) |
| `BoolS_IsCommutativeMonoid` | `BoolS_IsCommMonoid` | [Instance/Bool/Commutative.v](../theories/Instance/Bool/Commutative.v) |
| `BoolCocycleSphereClassS_IsCommutativeMonoid` | `BoolCocycleSphereClassS_IsCommMonoid` | [Instance/Bool/CocycleSphereGroup.v](../theories/Instance/Bool/CocycleSphereGroup.v) |
| `cocycle_two_sphere_IsCommutativeMonoid` | `cocycle_two_sphere_IsCommMonoid` | [Instance/Set/Simplicial/Cocycle/SphereGroup.v](../theories/Instance/Set/Simplicial/Cocycle/SphereGroup.v) |
| `cocycle_kan_IsCommutativeMonoid` | `cocycle_kan_IsCommMonoid` | [Instance/Set/Simplicial/Cocycle/SphereKanGroup.v](../theories/Instance/Set/Simplicial/Cocycle/SphereKanGroup.v) |
| `MagmaFromExtension` | `MagmaOfSetC` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `MonoidFromExtension` | `MonoidOfSemigroup` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `GroupFromExtension` | `GroupOfMonoid` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `SemigroupFromProperty` | `SemigroupOfMagma` | [Algebra/Semigroup/Core.v](../theories/Algebra/Semigroup/Core.v) |

Each parent name denotes the same immediate `:>` projection; no direct
ancestor bypass is added. All stronger structures inherit one `mul` and
its laws from the weakest defining layer. `inv` is the one selected inverse;
`mul_unit` names the selected multiplicative unit; bare `unit` conflicts
with Rocq's one-element type. When another theory uses a short name, qualify the algebra
declaration rather than adding a structure-specific alias.

每个方向父名称仍为原来的直接 `:>` 投影，不增加绕过直接父结构的祖先转换。
更强结构从最弱定义层继承同一个 `mul` 及其定律；`inv` 为唯一的选定逆。
选定乘法单位元命名为 `mul_unit`，避免与 Rocq 单元素类型 `unit` 冲突。
短名与其他理论重叠时使用限定名称，不另设带结构前缀的别名。

Checkpoint `77a7cf0` validation with Rocq 9.3.0 / Stdlib 9.2.0:
`dune build -j2 @all @runtest
@install` passed; 218 temporary assumption reports are closed, including all
44 public names. All 44 retired-name probes and nine earlier transitional-name
probes passed. The 63 Rocq files contain only the mapped renames and three
formula line wraps; imports are unchanged. See the
[structure guide](./BundledInterfaces.md#complete-algebra-hierarchy-current-migration)
for the full validation scope. No export or shared environment changes.

检查点 `77a7cf0` 在 Rocq 9.3.0／Stdlib 9.2.0 下的全库、测试、安装检查
通过，218 项临时假设
报告全部闭合，含全部 44 个公开名；44 个退役名及九个更早过渡名负探针通过。
63 个 Rocq 文件只有表内改名及三处公式换行，导入不变。完整验证范围见
[结构指南](./BundledInterfaces.md#complete-algebra-hierarchy-current-migration)，
无导出或共享环境改动。

### Shared algebra scope / 共用代数作用域

The user-authorized follow-up to #42 combines the above field names with
one inherited notation scope. This is a separate scope migration, not an
extension of the historical 195-entry Batch 4 table. The identifier map
at that checkpoint had 45 entries, including the later user-requested `monoid_unit → mul_unit` change; scope changes are:

用户授权的 #42 后续将上述字段名称与唯一继承记号作用域合并实施。本节独立
记录作用域迁移，不扩充历史第四批 195 项表。该检查点有 45 项标识符改名，
含用户后续指定的 `monoid_unit → mul_unit`；
作用域的源码 breaking 变化如下：

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `magma_scope` | `algebra_scope` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `monoid_scope` | `algebra_scope` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `%magma` | `%alg` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `%monoid` | `%alg` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |

The multiplication and section glyphs are unchanged. Their interpretations
are declared once in the magma core and inherited by `Require Export`;
monoid and group add only unit and inverse notation in the same scope.
Local opening is explicit. No compatibility scopes or Notations modules
are retained; the chain-specific segment/substitution notations also move
to `algebra_scope`. The separate repository-wide reserved-notation work
is not replayed or taken over by this bounded algebra follow-up.

乘法与偏应用符号不变，解释只在原群核心声明一次，通过 `Require Export`
继承；幺半群与群分别只在同一作用域增加单位元与逆记号，作用域须显式局部
打开。不保留兼容作用域或增加 Notations 模块；连续乘积／替换记号也迁入
`algebra_scope`。本有界代数后续不重放或接管独立的全库预留记号工作。

The local follow-up passes full build/tests/install, the original 218 closed
reports and 12 new notation reports. Old scopes are rejected; no mathematical
definitions, laws, parent projections or identifiers change in this follow-up.
This notation checkpoint was local review work, not an integration submission.

本地后续通过全库／测试／安装、原 218 项闭合报告及新增 12 项记号报告，旧作用域
被拒绝；该记号检查点不改数学定义、定律、父投影或标识符，仅为本地待审成果，
不是集成候选。

### Selected multiplicative unit / 选定乘法单位元

At the unit-renaming checkpoint, the user-requested `monoid_unit → mul_unit`
entry above was implemented
on the same local WIP, without a compatibility alias. The earlier 44 names
are unchanged; that checkpoint map had 45 entries. All 21 affected Rocq files
contain only this exact token replacement relative to the notation WIP.
Final full build/tests/install passed; the expanded audit has 231 closed
reports, and the retired unit name fails as intended. This was a local
review checkpoint, with no integration handoff.

在单位字段改名检查点，用户指定的 `monoid_unit → mul_unit` 在同一本地 WIP
实施，不保留
兼容别名。此前 44 项名称不变，该检查点对照表共 45 项；21 个受影响 Rocq 文件
相对前一步记号 WIP 只有该精确词元替换。最终全库／测试／安装通过，扩展审计
共 231 项报告全部闭合，旧单位字段名按预期退役；该检查点仅为本地待审成果，
未交集成。

The earlier readability checkpoint used the same 45 identifiers and scope
map; mathematical notation, inferred law arguments and actual rewriting
are simplified without local forwarding bindings. See the [structure guide](./BundledInterfaces.md#complete-algebra-hierarchy-current-migration).

此前可读性检查点沿用这 45 项名称及作用域表，简化数学记号、定律隐式参数及
实际重写，不增加局部转发绑定，详见[结构指南](./BundledInterfaces.md#complete-algebra-hierarchy-current-migration)。

### Comm, Ext and Of / 交换、扩充及构造名称

The user-authorized algebra follow-up on local review commit `4814341`
uses `Comm` for commutativity, `Ext` / `ext` for extensions, and `Of`
for constructors previously named with `From`. The exact 11-name step is
below; two existing cumulative targets are shortened and nine new rows are
added, bringing the current algebra map to 54 entries. Earlier 45-name
checkpoint counts and the historical 195-entry table remain historical.
No compatibility aliases, module-path changes or mathematical changes are
introduced; Rocq's `From ... Require` command is unchanged.

用户授权在本地审阅提交 `4814341` 上继续将交换性缩为 `Comm`，扩充缩为
`Ext`／`ext`，构造名称中的 `From` 改为 `Of`。本步精确 11 项如下：
累计表中两项已有目标继续缩短，新增九行，当前代数表共 54 项。早前 45 项
检查点数量及历史 195 项表仍保留历史含义。不增加兼容别名、不改模块路径或
数学内容，也不改 Rocq 的 `From ... Require` 命令。

| Old / 旧名 | New / 新名 | Source / 源码 |
| --- | --- | --- |
| `IsCommutativeMonoid` | `IsCommMonoid` | [Algebra/Monoid/Commutative.v](../theories/Algebra/Monoid/Commutative.v) |
| `BoolS_IsCommutativeMonoid` | `BoolS_IsCommMonoid` | [Instance/Bool/Commutative.v](../theories/Instance/Bool/Commutative.v) |
| `BoolCocycleSphereClassS_IsCommutativeMonoid` | `BoolCocycleSphereClassS_IsCommMonoid` | [Instance/Bool/CocycleSphereGroup.v](../theories/Instance/Bool/CocycleSphereGroup.v) |
| `cocycle_two_sphere_IsCommutativeMonoid` | `cocycle_two_sphere_IsCommMonoid` | [Instance/Set/Simplicial/Cocycle/SphereGroup.v](../theories/Instance/Set/Simplicial/Cocycle/SphereGroup.v) |
| `cocycle_kan_IsCommutativeMonoid` | `cocycle_kan_IsCommMonoid` | [Instance/Set/Simplicial/Cocycle/SphereKanGroup.v](../theories/Instance/Set/Simplicial/Cocycle/SphereKanGroup.v) |
| `MagmaFromExtension` | `MagmaOfExt` | [Algebra/Magma/Core.v](../theories/Algebra/Magma/Core.v) |
| `MonoidFromExtension` | `MonoidOfExt` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `GroupFromExtension` | `GroupOfExt` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |
| `SemigroupFromProperty` | `SemigroupOfProperty` | [Algebra/Semigroup/Core.v](../theories/Algebra/Semigroup/Core.v) |
| `mul_extension_inv_unique` | `mul_ext_inv_unique` | [Algebra/Monoid/Core.v](../theories/Algebra/Monoid/Core.v) |
| `inv_extension_unique` | `inv_ext_unique` | [Algebra/Group/Core.v](../theories/Algebra/Group/Core.v) |

All 29 renamed Rocq source/client targets compile with the project switch
and `-j2`. Eleven full signature/assumption checks are closed; all eleven
retired names fail lookup. Exact reverse substitution restores every
pre-rename file, including the earlier uncommitted proof cleanup, and
imports are unchanged. This step remains uncommitted review work; it is
not pushed or submitted for integration.

项目 switch 下全部 29 个改名源码／客户端目标以 `-j2` 编译通过。11 项完整
签名／假设检查闭合，11 个旧名均退役。精确逆向替换可逐字恢复每个改名前文件，
包括此前未提交的证明整理；导入不变。本步仍为未提交待审修改，未推送或交集成。

Other extension families (category extension and DTT context extension)
and constructors outside the reviewed algebra hierarchy remain pending
bounded migrations. Ordinary English and descriptive local helper names
are retained.

其他扩充词族（范畴扩充及 DTT 上下文扩充）以及本次代数层级以外的构造名称
留待后续有界迁移；普通英文与描述性局部辅助名称保留。

The final local closeout passes 34 concrete changed-module and regression
targets; exact snapshot substitution, retired-name and map/link checks pass.
Existing closed assumption reports are reused for unchanged inputs. The
interrupted full build is not a pass. See the [dated review record](./BundledInterfaces.md#local-review-closeout-2026-11-16)
for coverage, evidence and the remaining full-library integration check.

最终本地收尾通过 34 个具体修改模块及回归目标；精确快照替换、旧名退役、
表格及链接检查通过。已有闭合假设报告按未变输入复用，中断的全量构建不计
成功。覆盖范围、证据及后续全库集成验证见[注明日期的审阅记录](./BundledInterfaces.md#local-review-closeout-2026-11-16)。

In the subsequent constructor cleanup, the four packing names become actual
record constructors. The user then selected the uniform `TargetOfParent`
naming scheme, paired with `TargetToParent` projections. This four-name
follow-up updates four existing targets in the cumulative map; it stays at
54 rows. The earlier 11-name step above records its intermediate spellings.

后续构造器整理将四个打包名称直接作为记录构造器，用户随后选择统一的
`TargetOfParent` 命名，与 `TargetToParent` 父投影配对。本步四项改名更新
累计表中的四个已有目标，总行数仍为 54；上方早前 11 项表保留当时的中间名称。

| Previous / 前名 | Current constructor / 当前构造器 | Parent projection / 父投影 |
| --- | --- | --- |
| `MagmaOfExt` | `MagmaOfSetC` | `MagmaToSetC` |
| `SemigroupOfProperty` | `SemigroupOfMagma` | `SemigroupToMagma` |
| `MonoidOfExt` | `MonoidOfSemigroup` | `MonoidToSemigroup` |
| `GroupOfExt` | `GroupOfMonoid` | `GroupToMonoid` |

Each constructor takes its parent and extension/property witness explicitly;
separate packing definitions and intermediary aliases are removed. See the
[constructor design](./BundledInterfaces.md#named-algebra-record-constructors).

各构造器显式接受父结构及扩充／性质见证，不保留独立打包定义或中间名别名，
详见[构造器设计](./BundledInterfaces.md#named-algebra-record-constructors)。

The parent-named constructor checkpoint passes 34 concrete targets and
19 closed temporary assumption/pattern/signature reports. The four retired
intermediary names fail lookup; no aliases remain. The semigroup proof
formatting supplied during review is preserved. Evidence:
`/tmp/hierarchy42-parent-constructors`; this is uncommitted local work,
with no full build, push or integration handoff.

按父结构命名的构造器检查点通过 34 个具体目标及 19 项闭合临时假设／模式
匹配／签名报告，四个中间名查找失败，不保留别名。审阅期间用户提供的半群
证明排版已保留；证据位于 `/tmp/hierarchy42-parent-constructors`。
本批仍未提交，未运行全库构建、推送或交集成。

## Groupoid parent and constructor / 群胚父结构与构造器

The user-authorized follow-up on `4788f85` migrates the complete `Gpd`
from `Class` to `Record` and applies these two names. This is a separate
bounded map, outside the 54-row algebra map and the historical abbreviation
batches. `GpdOfCat` directly constructs the record; no packing wrapper or
compatibility alias remains. `IsGroupoid C`, ordinary theory names and
module paths are unchanged. See the [structure follow-up](./BundledInterfaces.md#groupoid-record-follow-up).

用户授权在 `4788f85` 上将完整 `Gpd` 从 `Class` 改为 `Record`，并应用以下
两项命名。本表是独立的有界迁移，不扩充 54 行代数表及历史缩写批次。
`GpdOfCat` 直接构造记录，不保留打包包装或兼容别名；`IsGroupoid C`、通常
理论名称及模块路径不变，详见[结构后续](./BundledInterfaces.md#groupoid-record-follow-up)。

| Previous / 前名 | Current / 当前名 | Source / 源码 |
| --- | --- | --- |
| `GpdC` | `GpdToCat` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `GpdFromProperty` | `GpdOfCat` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |

Actual clients and the bundled-groupoid regression migrate together.
Sixteen concrete project-switch targets pass; nine temporary assumption
reports are closed. The two retired names fail lookup, and fixed-category
inverse theory remains byte-for-byte unchanged. The changes remain
uncommitted for user review, with no push or integration handoff.

实际客户端及群胚接口回归同步迁移。项目 switch 下 16 个具体目标通过，
九项临时假设报告闭合；两个退役名查找失败，固定范畴逆理论逐字不变。修改
保持未提交，等待用户审核，未推送或交集成。

## Groupoid interface names / 群胚接口命名

The user expanded the pending groupoid review batch to use `IsGpd`,
`isGpd` and `gpd_*` throughout the public family, including related instance
and Boolean model names. The exact 48-name map below is separate from the
two parent/constructor names above and the 54-row algebra map. Module paths
and ordinary English/Chinese prose retain their descriptive spelling.
Earlier statements that `IsGroupoid` was unchanged describe the pre-rename
checkpoints, not the current interface.

用户扩大待审群胚批次，统一公共词族中的 `IsGpd`、`isGpd` 及 `gpd_*`，
同步相关实例和布尔模型名称。下方精确 48 项表独立于此前父投影／构造器两项
及 54 行代数表；模块路径及普通中英文保留描述性拼写。更早关于
`IsGroupoid` 未改的陈述对应改名前检查点，不代表当前接口。

| Previous / 前名 | Current / 当前名 | Source / 源码 |
| --- | --- | --- |
| `BoolGroupoid` | `BoolGpd` | [Instance/Bool/Action.v](../theories/Instance/Bool/Action.v) |
| `BoolGroupoid_IsGroupoid` | `BoolGpd_IsGpd` | [Instance/Bool/Action.v](../theories/Instance/Bool/Action.v) |
| `CodiscreteCat_IsGroupoid` | `CodiscreteCat_IsGpd` | [Cat/Groupoid/Preorder.v](../theories/Cat/Groupoid/Preorder.v) |
| `EqGpd_IsGroupoid` | `EqGpd_IsGpd` | [Instance/Set/Groupoid.v](../theories/Instance/Set/Groupoid.v) |
| `FctCat_IsGroupoid` | `FctCat_IsGpd` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `IsGroupoid` | `IsGpd` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `IsoShape_IsGroupoid` | `IsoShape_IsGpd` | [Cat/Shape/Order.v](../theories/Cat/Shape/Order.v) |
| `MonoidCat_IsGroupoid` | `MonoidCat_IsGpd` | [Algebra/Group/Category.v](../theories/Algebra/Group/Category.v) |
| `PreorderCat_IsGroupoid` | `PreorderCat_IsGpd` | [Cat/Groupoid/Preorder.v](../theories/Cat/Groupoid/Preorder.v) |
| `ProdCat_IsGroupoid` | `ProdCat_IsGpd` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `VtxCat_IsGroupoid` | `VtxCat_IsGpd` | [Instance/Set/Simplicial/Vertex/Horn2.v](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) |
| `equivalence_IsGroupoid` | `equivalence_IsGpd` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `fully_faithful_IsGroupoid` | `fully_faithful_IsGpd` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `groupoid_HasLeftDivision` | `gpd_HasLeftDivision` | [Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v) |
| `groupoid_HasRightDivision` | `gpd_HasRightDivision` | [Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v) |
| `groupoid_arrow_iso` | `gpd_arrow_iso` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_fmap_inv` | `gpd_fmap_inv` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `groupoid_fmap_iso` | `gpd_fmap_iso` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `groupoid_initial_diagram_iso` | `gpd_initial_diagram_iso` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `groupoid_inv` | `gpd_inv` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_comp` | `gpd_inv_comp` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_id` | `gpd_inv_id` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_inv` | `gpd_inv_inv` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_l` | `gpd_inv_l` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_proper` | `gpd_inv_proper` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_r` | `gpd_inv_r` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_resp` | `gpd_inv_resp` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inv_unique` | `gpd_inv_unique` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `groupoid_inverse_square` | `gpd_inverse_square` | [Cat/Groupoid/Star.v](../theories/Cat/Groupoid/Star.v) |
| `groupoid_iso` | `gpd_iso` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `horn2_0_IsGroupoid` | `horn2_0_IsGpd` | [Instance/Set/Simplicial/Vertex/Horn2.v](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) |
| `horn2_2_IsGroupoid` | `horn2_2_IsGpd` | [Instance/Set/Simplicial/Vertex/Horn2.v](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) |
| `isGroupoid` | `isGpd` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `left_division_IsGroupoid` | `left_division_IsGpd` | [Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v) |
| `left_division_groupoid_iff` | `left_division_gpd_iff` | [Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v) |
| `nerve_groupoid_eq_iff` | `nerve_gpd_eq_iff` | [Instance/Set/Simplicial/Nerve.v](../theories/Instance/Set/Simplicial/Nerve.v) |
| `op_IsGroupoid` | `op_IsGpd` | [Cat/Groupoid/Core.v](../theories/Cat/Groupoid/Core.v) |
| `outer_horn2_groupoid_iff` | `outer_horn2_gpd_iff` | [Instance/Set/Simplicial/Vertex/Horn2.v](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) |
| `retract_IsGroupoid` | `retract_IsGpd` | [Cat/Groupoid/Functor.v](../theories/Cat/Groupoid/Functor.v) |
| `right_division_IsGroupoid` | `right_division_IsGpd` | [Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v) |
| `right_division_groupoid_iff` | `right_division_gpd_iff` | [Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v) |
| `vertex_groupoid_HasKanFillers` | `vertex_gpd_HasKanFillers` | [Instance/Set/Simplicial/Vertex/Kan.v](../theories/Instance/Set/Simplicial/Vertex/Kan.v) |
| `vertex_groupoid_higher_HasFillers` | `vertex_gpd_higher_HasFillers` | [Instance/Set/Simplicial/Vertex/Kan.v](../theories/Instance/Set/Simplicial/Vertex/Kan.v) |
| `vertex_groupoid_horn2_HasFillers` | `vertex_gpd_horn2_HasFillers` | [Instance/Set/Simplicial/Vertex/Filling.v](../theories/Instance/Set/Simplicial/Vertex/Filling.v) |
| `vertex_kan_IsGroupoid` | `vertex_kan_IsGpd` | [Instance/Set/Simplicial/Vertex/Outer.v](../theories/Instance/Set/Simplicial/Vertex/Outer.v) |
| `vertex_kan_groupoid_iff` | `vertex_kan_gpd_iff` | [Instance/Set/Simplicial/Vertex/Kan.v](../theories/Instance/Set/Simplicial/Vertex/Kan.v) |
| `vertex_outer_horn2_IsGroupoid` | `vertex_outer_horn2_IsGpd` | [Instance/Set/Simplicial/Vertex/Outer.v](../theories/Instance/Set/Simplicial/Vertex/Outer.v) |
| `vertex_outer_horn2_groupoid_iff` | `vertex_outer_horn2_gpd_iff` | [Instance/Set/Simplicial/Vertex/Outer.v](../theories/Instance/Set/Simplicial/Vertex/Outer.v) |

The former complete-bundle helper `gpd_inv` is removed; that name now
belongs to the general inverse operation on a supplied category with
`IsGpd` evidence. Choice-sensitive bundle clients explicitly pass their
stored `isGpd` witness. This retains one operation at the weakest layer,
with no forwarding alias. All changes remain uncommitted for review.

原完整结构包上的 `gpd_inv` 辅助包装已移除，该名称现用于给定范畴及
`IsGpd` 见证上的一般逆运算。需要固定选择的结构包客户端显式传入保存的
`isGpd` 见证，在最弱层保留唯一操作，不增加转发别名。全部修改仍未提交，
等待审核。

The final naming batch passes 28 concrete targets and 48 closed public
signature/assumption reports; all 48 retired-name checks pass. Twenty ordinary
clients are exact substitutions; the core and bundle regression additionally
consolidate inverse access. Evidence: `/tmp/hierarchy42-gpd-names`. No full
build, commit, push or integration handoff is included.

最终命名批次通过 28 个具体目标及 48 项闭合公开签名／假设报告，48 项退役名
负检查通过。20 个普通客户端为精确替换；核心及结构包回归另统一了逆的访问。
证据位于 `/tmp/hierarchy42-gpd-names`；未执行全库构建、提交、推送或交接。

## Division names / 除法名称

After the 48-name groupoid-family checkpoint above, the user approved
`Div` / `div` with right/left suffixes `R` / `L` and `_r` / `_l`. The nine
exact changes below include six intermediate targets from that earlier
checkpoint and three additional division-interface names. The earlier map
remains a historical step; this table specifies the current division names.
The `Division.v` path and descriptive prose are unchanged. No aliases remain.

上方 48 项群胚词族检查点之后，用户批准使用 `Div`／`div`，右／左方向使用
`R`／`L` 及 `_r`／`_l` 后缀。下方精确九项含早前检查点中的六个中间目标，
另有三个除法接口名称；早前表保留历史步骤，本表给出当前除法名称。
`Division.v` 路径及描述性文字不变，不保留别名。

| Previous / 前名 | Current / 当前名 |
| --- | --- |
| `HasRightDivision` | `HasDivR` |
| `HasLeftDivision` | `HasDivL` |
| `right_division` | `div_r` |
| `gpd_HasRightDivision` | `gpd_HasDivR` |
| `gpd_HasLeftDivision` | `gpd_HasDivL` |
| `right_division_IsGpd` | `div_r_IsGpd` |
| `left_division_IsGpd` | `div_l_IsGpd` |
| `right_division_gpd_iff` | `div_r_gpd_iff` |
| `left_division_gpd_iff` | `div_l_gpd_iff` |

`HasDivL C` remains `HasDivR (C^op)` by definition. The ordinary word
right/left specifies which factor is divided; `_resp` remains the suffix
for respectful maps. All declarations are in
[Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v); the horn client
[Vertex/Horn2.v](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) migrates
with the same equations and witnesses. This remains uncommitted review work.

`HasDivL C` 按定义仍为 `HasDivR (C^op)`。右／左表示被除的因子方向，
保相等映射仍使用 `_resp`。全部声明位于
[Cat/Groupoid/Division.v](../theories/Cat/Groupoid/Division.v)，horn 客户端
[Vertex/Horn2.v](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) 同步迁移，
方程及见证不变。本批仍为未提交待审成果。

This nine-name step passes six concrete targets, nine full public
signature/retired-name checks and ten closed temporary assumption reports
including the opposite-definition identity. Both Rocq files are exact
substitutions. Evidence: `/tmp/hierarchy42-div-names`; uncommitted for review.

本步九项改名通过六个具体目标、九项完整公开签名／退役名检查及十项闭合临时
假设报告，包含反范畴定义等式。两个 Rocq 文件为精确替换；证据位于
`/tmp/hierarchy42-div-names`，修改保持未提交供审核。

User review of the groupoid/division batch is complete and a local
checkpoint commit is authorized. Earlier uncommitted-status notes retain
their historical meaning. The recorded targeted checks are reused for
unchanged inputs; this does not claim full-library integration acceptance.

用户已完成群胚／除法批次审核并批准保存本地提交。早前未提交状态保留其历史
含义，未变输入复用已记录的定向检查，不表示完成全库集成验收。

## Adj and Of follow-up / Adj 及 Of 后续

The user authorized completing the remaining `Adj` / `adj` family together
with the reviewed `From → Of` constructors. The exact 34-name table below
includes mathematical declarations and their directly named regression
helpers. Earlier tables that retained descriptive `adjunction_*` names are
historical checkpoints superseded for these reviewed entries. `adjunct`
and `unadjunct` retain their distinct Hom-transposition meaning; their
`from_hom` helpers become `of_hom`. Module paths and ordinary prose do not
change. This step is implemented alongside the first `Cat` Record slice,
without compatibility aliases. The user approved saving the reviewed work
as a local checkpoint; no push or integration handoff is included.

用户授权补齐剩余 `Adj`／`adj` 词族，并实施已审阅构造名中的 `From → Of`。
下方精确 34 项包含数学声明及直接命名的回归辅助项。早前保留描述性
`adjunction_*` 名称的表格是历史检查点，本次审阅项按下表更新。
`adjunct` 与 `unadjunct` 保留 Hom 转置的独立数学含义，其中 `from_hom`
辅助名改为 `of_hom`。模块路径及普通文字不变。本步与首片 `Cat` Record
迁移一同实施，不留兼容别名。用户已批准将审核后的成果保存为本地检查点；
未推送或交集成。

| Previous / 前名 | Current / 当前名 | Source / 源码 |
| --- | --- | --- |
| `AdjFromHom` | `AdjOfHom` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `ClosFromUniversal` | `ClosOfUniversal` | [Set/Closure/Core.v](../theories/Set/Closure/Core.v) |
| `FreeObjFromUniversal` | `FreeObjOfUniversal` | [Cat/FreeObject/Core.v](../theories/Cat/FreeObject/Core.v) |
| `IdentityFromAdjunction` | `IdentityOfAdj` | [tests/Computations.v](../tests/Computations.v) |
| `adjunct_from_hom` | `adjunct_of_hom` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_free_roundtrip_iso` | `adj_free_roundtrip_iso` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `adjunction_hom_iso` | `adj_hom_iso` | [Instance/Set/Adjunction.v](../theories/Instance/Set/Adjunction.v) |
| `adjunction_hom_nat_iso` | `adj_hom_nat_iso` | [Instance/Set/Adjunction.v](../theories/Instance/Set/Adjunction.v) |
| `adjunction_kleisli_fully_faithful` | `adj_kleisli_fully_faithful` | [Cat/Monad/KleisliComparison.v](../theories/Cat/Monad/KleisliComparison.v) |
| `adjunction_kleisli_unadjunct_comp` | `adj_kleisli_unadjunct_comp` | [Cat/Monad/KleisliComparison.v](../theories/Cat/Monad/KleisliComparison.v) |
| `adjunction_monad_mul` | `adj_monad_mul` | [Cat/Monad/Adjunction.v](../theories/Cat/Monad/Adjunction.v) |
| `adjunction_β` | `adj_β` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `adjunction_η` | `adj_η` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |
| `free_adjunction_counit` | `free_adj_counit` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `free_adjunction_unit` | `free_adj_unit` | [Cat/FreeObject/Adjunction.v](../theories/Cat/FreeObject/Adjunction.v) |
| `generator_adjunction_counit_iso` | `generator_adj_counit_iso` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `generator_adjunction_unit_iso` | `generator_adj_unit_iso` | [Cat/Diagram/Generator.v](../theories/Cat/Diagram/Generator.v) |
| `high_eq_adjunction_hom` | `high_eq_adj_hom` | [tests/Universes.v](../tests/Universes.v) |
| `high_eq_colimit_adjunction` | `high_eq_colimit_adj` | [tests/Universes.v](../tests/Universes.v) |
| `high_eq_exponential_adjunction` | `high_eq_exponential_adj` | [tests/Universes.v](../tests/Universes.v) |
| `high_eq_limit_adjunction` | `high_eq_limit_adj` | [tests/Universes.v](../tests/Universes.v) |
| `kleisli_adjunction_counit` | `kleisli_adj_counit` | [Cat/Monad/KleisliAdjunction.v](../theories/Cat/Monad/KleisliAdjunction.v) |
| `kleisli_adjunction_triangle_l` | `kleisli_adj_triangle_l` | [Cat/Monad/KleisliAdjunction.v](../theories/Cat/Monad/KleisliAdjunction.v) |
| `kleisli_adjunction_triangle_r` | `kleisli_adj_triangle_r` | [Cat/Monad/KleisliAdjunction.v](../theories/Cat/Monad/KleisliAdjunction.v) |
| `kleisli_adjunction_unit` | `kleisli_adj_unit` | [Cat/Monad/KleisliAdjunction.v](../theories/Cat/Monad/KleisliAdjunction.v) |
| `low_eq_adjunction_hom` | `low_eq_adj_hom` | [tests/Universes.v](../tests/Universes.v) |
| `low_eq_colimit_adjunction` | `low_eq_colimit_adj` | [tests/Universes.v](../tests/Universes.v) |
| `low_eq_exponential_adjunction` | `low_eq_exponential_adj` | [tests/Universes.v](../tests/Universes.v) |
| `low_eq_limit_adjunction` | `low_eq_limit_adj` | [tests/Universes.v](../tests/Universes.v) |
| `mixed_adjunction_comp` | `mixed_adj_comp` | [tests/Universes.v](../tests/Universes.v) |
| `mixed_free_adjunction` | `mixed_free_adj` | [tests/Universes.v](../tests/Universes.v) |
| `preorder_adjunction_correspondence` | `preorder_adj_correspondence` | [Cat/Logic/Adjunction.v](../theories/Cat/Logic/Adjunction.v) |
| `separated_closure_adjunction` | `separated_closure_adj` | [tests/Closure.v](../tests/Closure.v) |
| `unadjunct_from_hom` | `unadjunct_of_hom` | [Cat/Adjunction.v](../theories/Cat/Adjunction.v) |

## LiftT constructor / LiftT 构造器

Single-field universe wrappers now have the explicit constructor `Lift`.
Use `Lift x` for a value or equality witness. The wrapper type,
projection `lower` and independent universe bounds are unchanged; no
compatibility alias for the autogenerated constructor is retained.
Native map recovery is exposed separately as `unlift_resp` / `f^↓S`.

单字段宇宙包装现有显式构造器 `Lift`，值或相等见证写作 `Lift x`。
包装类型、投影 `lower` 及独立宇宙上界不变，不保留旧自动生成构造器的兼容
别名。原生映射恢复单独通过 `unlift_resp`／`f^↓S` 暴露。

| Previous / 前名 | Current / 当前名 | Source / 源码 |
| --- | --- | --- |
| `Build_LiftT` | `Lift` | [Set/Core.v](../theories/Set/Core.v) |

## Pending batches / 后续批次

The approved Clos/ClosOp, Exp, Cart and Prof work is integrated in Batch 4 above.
The following optional candidates remain outside that naming batch; structural
work follows the separate user-authorized bundled-interface migration.

已批准的合并词族已作为第四批集成。以下可选候选不在该命名批次；结构工作按用户
另行授权的打包接口迁移推进。

| Family / 词族 | Pending examples / 待处理示例 | Boundary / 边界 |
| --- | --- | --- |
| Optional names / 可选名称 | `IsStrictTwoCat → IsStrict2Cat`, `NaturalPrismF → NatPrismF`, `ContextCategoryEquivalence → CtxCatEquiv`, NNO | Separate user approval / 用户另行批准 |
| Complete hierarchies / 完整层级 | `CartesianCat`, monoidal/CCC bundling / 幺半及 CCC 打包 | Gpd complete; Cat Record slice in review / Gpd 已完成，Cat Record 片段待审 |
| Other notation / 其他记号 | Repository-wide reserved syntax beyond the algebra slice above / 上述代数片段以外的全库预留语法 | Separate review; no replay of #31 / 单独审阅，不重放 #31 |

## Preserved interfaces and collisions / 保留接口与冲突

- Keep source paths such as `Cat/Functor/Core.v`, `Cat/Adjunction.v` and
  `Instance/Set/Vertex/Functor.v`. Import paths are not public declaration names.
- The current structures are parameterized `MonoidalCat C`, `CartesianCat C`
  and `CCC C`; the historical name `MonoidalCategory C` in #38 is stale.
  This batch does not change their parameters, parents, fields or choices.
- The fixed-category property interface is now `IsGpd C`; the complete
  groupoid and its naming follow-up have separate review records above.
  Repository-wide `Reserved Notation` work remains separate.
- Keep the natural-number setoid `NatS`; a natural-transformation setoid
  cannot be renamed to it. Keep `EndofunctorMonoidal` distinct from
  `EndoMonoidal`. The two existing `MonoidCat` declarations remain in their
  respective namespaces.
- Preserve Type-valued equality/witnesses, universes, transparent computations,
  mathematical statements, canonical/typeclass registrations and explicit
  enabling of model choices.

- 保留原文件及导入路径；路径不是声明名，不能按标识符对照表机械替换。
- 当前 `MonoidalCat C`、`CartesianCat C`、`CCC C` 均有具名范畴参数；#38 的
  旧 `MonoidalCategory C` 描述已过时。本批不改变参数、父结构、字段或选定数据。
- 固定范畴性质接口现为 `IsGpd C`；完整群胚及其命名后续在上方单独记录。
  全库预留记号工作仍为独立任务。
- 避开自然数广集 `NatS`，区分 `EndofunctorMonoidal` 与 `EndoMonoidal`；
  两个已有 `MonoidCat` 仍保留各自命名空间。
- 保持 Type 值相等／见证、宇宙、透明计算、数学陈述、规范结构／实例注册和
  模型选择的显式启用方式。

## Batch 1 validation and delivery / 第一批验证与交付

These checks describe the first-batch checkpoint before Batch 2; the
second batch has its own validation record above.

以下是第二批开始前的首批检查点记录；第二批验证另见上文。

- Tool resolution checked in the existing `rocq-cats` opam switch:
  Rocq/Stdlib 9.2, OCaml 5.3.0, Dune 3.23.1.
- `opam exec --switch=rocq-cats -- dune build @all` passed, compiling the
  library and existing regression modules. Only identifier substitutions
  changed 285 Rocq files; reversing the exact map recovers their baseline
  text apart from eight nested-record closing-indent adjustments. All import
  commands are unchanged; retired names are absent from executable source.
- A temporary, uncommitted compilation checked all 69 new public signatures
  with universes printed and all 69 `Print Assumptions` reports closed under
  the global context. Seven retired-name checks passed. Definitional probes
  identify `Ob (FctCat C D)` with `Fct C D` and its arrows with `Nat`; the
  cartesian functor coercion and its stored preservation instance also passed.
- The 69 exact document rows agree with the migration map; every source link
  resolves and its owner contains the new name. `git diff --check` passed.
  Temporary audits are not retained regression tests. No HTML/PDF export ran.
- The first-batch checkpoint was initially retained locally; the later user
  instruction authorizes releasing both completed batches together.

- 已核对现有项目 switch 的工具解析及版本：Rocq/Stdlib 9.2、OCaml 5.3.0、
  Dune 3.23.1。
- 项目 switch 下 `dune build @all` 通过，编译全库及已有回归模块。
  285 个 Rocq 文件只改标识符；按精确对照反向替换即可恢复基线，仅另有八处
  嵌套记录结束符的缩进随短名调整。导入命令全部保持原样，执行代码无退役旧名。
- 临时、未提交的编译检查覆盖 69 项新名称签名并打印宇宙；69 项假设报告全部
  闭合。七项旧名退役检查通过；函子范畴对象／箭头的定义相等、笛卡尔函子包的
  强制转换及保存的保持性实例检查通过。
- 文档 69 项精确映射与实际迁移一致，源码链接及所属模块内新名称均已核对，
  `git diff --check` 通过。临时审计不作为已提交回归；未运行 HTML/PDF 导出。
- 首批起初保留在本地；后续用户指令授权将两批完成内容一同交付。
