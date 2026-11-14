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
| Cartesian / 笛卡尔 | `Cart` | Review complete structures separately / 完整结构另行审阅 |
| Diagonal / 对角 | `Diag` | Keep the existing diagonal notation / 保留已有对角记号 |
| Generator and generators / 生成元 | `Gen` | Singular and plural use the same stem / 单复数使用同一词根 |
| Object and objects / 对象 | `Obj` | Singular and plural use the same stem; preserve kind suffixes / 单复数统一，保留种类后缀 |
| Limit and colimit / 极限与余极限 | `Lim`, `Colim` | Keep `HasLimit`, `HasColimit` / 保留选定构造接口 |
| Presheaf / 预层 | `Psh` | Existing category name stays / 保留已有范畴名 |
| Vertex / 顶点 | `Vtx` | First batch only migrates the functor bundle family / 本批只迁移函子包词族 |
| Closure / 闭包 | `Clos` | Do not conflate with Closed / 不与 Closed 混写 |
| Packaged relation-closure operator / 打包关系闭包算子 | `*ClosOp` | Raw generated relations use `*Clos` / 底层生成关系用 `*Clos` |
| Subobject / 子对象 | `SubObj` | A setoid of subobjects needs `S` / 子对象广集须体现 `S` |
| Named exponential construction / 指数构造名 | `Exp` | Keep `HasExponential` / 保留选定指数接口 |
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
| `VertexNerveF_IsCartesianF` | `VertexNerveF_IsCartF` | [Instance/Set/Simplicial/Vertex/Cartesian.v](../theories/Instance/Set/Simplicial/Vertex/Cartesian.v) |
| `ExponentialF_IsCartesianF` | `ExponentialF_IsCartF` | [Cat/Limit/Exponential.v](../theories/Cat/Limit/Exponential.v) |

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
| `HasNaturalNumbersObject` | `HasNaturalNumbersObj` | [ETCS/Nat.v](../theories/ETCS/Nat.v) |
| `HasSubObjectClassifier` | `HasSubObjClassifier` | [ETCS/Sub.v](../theories/ETCS/Sub.v) |
| `LaxMonoidObject` | `LaxMonoidObj` | [Cat/Monoidal/Transport.v](../theories/Cat/Monoidal/Transport.v) |
| `MonoidObject` | `MonoidObj` | [Cat/Monoidal/Monoid.v](../theories/Cat/Monoidal/Monoid.v) |
| `MonoidObjectsF` | `MonoidObjF` | [Instance/Set/Simplicial/Vertex/Monoid.v](../theories/Instance/Set/Simplicial/Vertex/Monoid.v) |
| `OrdinalObjectsF` | `OrdinalObjF` | [Instance/Set/Vertex/Ordinal.v](../theories/Instance/Set/Vertex/Ordinal.v) |
| `PointwiseFreeObjects` | `PointwiseFreeObj` | [Cat/FreeObject/Representable.v](../theories/Cat/FreeObject/Representable.v) |
| `SetCat_HasNaturalNumbersObject` | `SetCat_HasNaturalNumbersObj` | [Instance/Set/Nat.v](../theories/Instance/Set/Nat.v) |
| `SetMonoidObject` | `SetMonoidObj` | [Instance/Set/Monoid.v](../theories/Instance/Set/Monoid.v) |
| `SubObject` | `SubObjS` | [Instance/Set/Subobject.v](../theories/Instance/Set/Subobject.v) |
| `VertexProductObjectsF` | `VertexProductObjF` | [Instance/Set/Vertex/Product.v](../theories/Instance/Set/Vertex/Product.v) |
| `VertexTerminalObjectsF` | `VertexTerminalObjF` | [Instance/Set/Vertex/Terminal.v](../theories/Instance/Set/Vertex/Terminal.v) |
| `hasNaturalNumbersObject` | `hasNaturalNumbersObj` | [ETCS/Core.v](../theories/ETCS/Core.v) |
| `hasSubObjectClassifier` | `hasSubObjClassifier` | [ETCS/Core.v](../theories/ETCS/Core.v) |

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

## Pending batches / 后续批次

These are remaining families, not completed migrations. Audit each declaration
and its import scopes before adding exact implemented rows. The compound
`VtxFct`/`FctPsh`/`ClosAdj`/`ProdExpAdj` names already in Batch 1 do not imply
that their entire stem families have migrated.

以下词族尚未完成迁移；后续须核对每个声明及导入作用域，再补入已实现精确表。
第一批已有的复合名不代表对应词族全部完成。

| Family / 词族 | Pending examples / 待处理示例 | Boundary / 边界 |
| --- | --- | --- |
| Vertex / 顶点 | `VertexCat → VtxCat`, `VertexPresentation → VtxPresentation`, `VertexNerve → VtxNerve`, related diagrams/products/chains / 相关图式、积及链 | Keep object/functor/transformation suffixes distinct / 区分对象、函子与自然变换后缀 |
| Closure / 闭包 | `Closure → Clos`, `ClosureLe → ClosLe`, `ClosureEq → ClosEq`, `ClosureF → ClosF`, `ClosureMonad → ClosMonad` | Review related constructors / 审阅相关构造 |
| Raw generated relations / 底层生成关系 | `EquivClosure → EquivClos`, `SymClosure → SymClos`, `ReflTransClosure → ReflTransClos` | Preserve witnesses / 保留见证 |
| Packaged closure operators / 打包闭包算子 | `EquivalenceClosure → EquivClosOp`, `SymmetricClosure → SymClosOp`, `ReflexiveTransitiveClosure → ReflTransClosOp` | Check the actual type of `FamilyEquivalenceClosure` before choosing its name / 逐纤维接口先核对类型 |
| Exponentials / 指数 | `ExponentialF → ExpF`, `ExponentialBiF → ExpBiF`, `ExponentialContraF → ExpContraF`, `ExponentialFixedN → ExpFixedN`, `ExponentialProductN → ExpProdN`, `ExponentialUnitN → ExpUnitN`, `ExponentialIteratedN → ExpIteratedN` | Retain `HasExponential` / 保留选定接口 |
| Other Cartesian names / 其他笛卡尔名称 | `CartesianMonoidal → CartMonoidal`, `CartesianAssociatorN → CartAssociatorN`, corresponding unitors, model/instance names / 单位子、模型与实例名 | Review complete `CartesianCat` hierarchy separately / 完整结构层级另行审阅 |
| Fibration lifts / 纤维化提升 | `HasCartesianLift → HasCartLift`, `CartesianLift → CartLift` | Candidate requiring exact client inventory / 候选，须盘点客户端 |
| Optional names / 可选名称 | `BoolGroupoid → BoolGpd`, `IsStrictTwoCat → IsStrict2Cat`, `NaturalPrismF → NatPrismF`, `ContextCategoryEquivalence → CtxCatEquiv` | Reconfirm optional compounds individually / 可选复合名逐项确认 |

## Preserved interfaces and collisions / 保留接口与冲突

- Keep source paths such as `Cat/Functor/Core.v`, `Cat/Adjunction.v` and
  `Instance/Set/Vertex/Functor.v`. Import paths are not public declaration names.
- The current structures are parameterized `MonoidalCat C`, `CartesianCat C`
  and `CCC C`; the historical name `MonoidalCategory C` in #38 is stale.
  This batch does not change their parameters, parents, fields or choices.
- Keep `IsGroupoid C`; bundled groupoid/category coercion experiments and
  `Reserved Notation` work are separate tasks.
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
- 保留 `IsGroupoid C`；群胚打包、范畴强制转换实验及预留记号属于独立任务。
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
