# Bundled interfaces and underlying views

# 打包接口与底层视图

Public identifiers in this guide follow the current
[abbreviation map](./Abbreviations.md); dated baseline inventories below
remain historical evidence.

本文公共标识符按当前[缩写对照](./Abbreviations.md)更新；下方注明日期与基线的
清单仍是历史证据。

The [dated whole-library audit](#library-wide-structure-and-naming-audit)
started with all 87 class/record interfaces at baseline `5d87331`, growing to
100 interfaces at its later synchronized checkpoint. It records the structural
naming and inheritance findings after the CCC changes. The complete-category
slice below gives a fresh inventory for its own integration baseline.

[注明基线的全库审计](#library-wide-structure-and-naming-audit)起初基于
`5d87331` 分类全部 87 个类／记录接口，在后续同步检查点增至 100 个接口，
并记录 CCC 修改后的结构命名与继承问题。下方完整范畴首片按自己的集成基线
重新盘点接口。

The lax monoidal interface now bundles its underlying functor and structure
in one record, exposing a single coercion to `Fct`. The first follow-up
from the library-wide survey now adds bundled cartesian and cartesian closed
functors. Existing fixed-data preservation interfaces remain available for
general theorems alongside those bundles.

Lax monoidal 接口现已将底层函子及结构打包在同一个记录中，只提供一条到
`Fct` 的强制转换。全库调查后的首项后续工作现已添加打包的笛卡尔函子及
笛卡尔闭函子。已有固定数据保持性接口继续与打包接口共存，服务于一般定理。

The [structured-category universes](./StructureUniverses.md) now build a
cartesian category of cartesian categories and a groupoid of groupoids and
equivalences. Both support self-membership at distinct universe instances.

[结构范畴宇宙](./StructureUniverses.md)现已构造笛卡尔范畴组成的笛卡尔范畴，
以及群胚和等价组成的群胚；两者均支持不同宇宙实例间的自身成员关系。

The current local follow-up also makes `CartFct` and `CCCFct`
complete records. Their unique parent projections are `CartFctToFct` and
`CCCFctToCartFct`; `CartFctOfFct` and `CCCFctOfCartFct` are direct
constructors. `CCCFctOfFct` retains the useful fixed-functor preservation
presentation. `IsCartF` and `IsCCCF` remain classes. `functor_*` and
`exponential_*` identifier segments now use `fct` and `exp`, with the exact
map in [the naming guide](./Abbreviations.md). Historical class inventories
below describe their dated baselines.

当前本地后续还将 `CartFct`、`CCCFct` 改为完整记录。唯一父投影为
`CartFctToFct`、`CCCFctToCartFct`，直接构造器为 `CartFctOfFct`、
`CCCFctOfCartFct`；`CCCFctOfFct` 保留有实际用途的固定函子保持性呈现。
`IsCartF`、`IsCCCF` 仍为类。标识符中的 `functor_*`、`exponential_*`
词段现统一为 `fct`、`exp`，精确对照见[命名指南](./Abbreviations.md)。
下方历史类清单仍描述其注明日期的基线。

The uncommitted lax-monoidal follow-up starts at `728ab7c`.
`LaxMonoidalFct` is now a complete record with the unique
`LaxMonoidalFctToFct :> Fct` parent and direct `LaxMonoidalFctOfFct`
constructor. Unit comparison, natural tensorator and all three coherence
laws stay defined on that same parent. `IdLaxMonoidalF` and
`ConstLaxMonoidalF` are explicitly selected constructions. There is no
extra `Data`/`Is`/`Has` layer or additional instance for the record parent.
`Applicative`, the monoidal category hierarchy and their choices retain
this checkpoint's existing presentations; only direct clients are updated.

未提交的 lax 幺半后续从 `728ab7c` 开始。`LaxMonoidalFct` 现为完整记录，
具有唯一父视图 `LaxMonoidalFctToFct :> Fct` 及直接构造器
`LaxMonoidalFctOfFct`。单位比较、自然张量子及三条相干律仍定义在同一个
父函子上；`IdLaxMonoidalF`、`ConstLaxMonoidalF` 为须显式选择的构造。
不增加 `Data`／`Is`／`Has` 层，也不为记录值父结构增加实例。
`Applicative`、幺半范畴层级及其选择保留本检查点的已有呈现，仅更新直接客户端。

`MonoidalFct` now extends that same `LaxMonoidalFct` through the unique
`MonoidalFctToLaxMonoidalFct` projection and direct
`MonoidalFctOfLaxMonoidalFct` constructor. In this library, an unqualified
monoidal functor means a strong monoidal functor: its stored unit and tensor
comparisons are invertible. Only Type-valued inverse witnesses are added;
forward maps and coherence stay in the lax parent. `MonoidalUnitIso` and
`MonoidalTensorIso` expose transparent views, and `MonoidalTensorInvN`
derives inverse naturality through the general natural-isomorphism theory.
`IdMonoidalF` extends the exact lax identity and is explicitly selected.
Tensorial strength remains a separate notion.

`MonoidalFct` 现通过唯一投影 `MonoidalFctToLaxMonoidalFct` 和直接构造器
`MonoidalFctOfLaxMonoidalFct` 扩展同一个 `LaxMonoidalFct`。本库中不加限定的
幺半函子指 strong monoidal functor：保存的单位及张量比较均可逆。
新增的仅为 Type 值逆见证，正向映射及相干律保留在 lax 父结构中。
`MonoidalUnitIso`、`MonoidalTensorIso` 提供透明视图，`MonoidalTensorInvN`
通过一般自然同构理论导出逆自然性。`IdMonoidalF` 扩展原有 lax 恒等构造，
仍须显式选择。张量强度保持为不同概念。

`Applicative` is now a complete record with the direct constructor
`ApplicativeOfLaxMonoidalFct`. Its only parent projection is
`ApplicativeToLaxMonoidalFct :> LaxMonoidalFct`, using the supplied terminal
and product choices through `CartMonoidal`. The parent retains the functor,
unit, tensorator and lax coherence; the extension retains the natural pure
map and its unit/product compatibility. No strong-monoidal condition or
extra functor copy is introduced. Reader, Monad, Arrow, native lax and
operation-reconstruction clients use the same stored parents. Alternate
`ApplicativeOps` and `ApplicativeAp` presentations keep their existing
interfaces in this bounded migration.

`Applicative` 现为完整记录，直接构造器为 `ApplicativeOfLaxMonoidalFct`。
唯一父投影 `ApplicativeToLaxMonoidalFct :> LaxMonoidalFct` 通过
`CartMonoidal` 使用给定的终对象及积选择。父结构保留函子、单位、张量子及
lax 相干律；扩展层保留自然纯值映射及其单位／积相容律，不增加 strong
幺半要求或另一份函子。Reader、Monad、Arrow、原生 lax 及运算重建客户端
沿用相同的父结构。本次有界迁移保留 `ApplicativeOps`、`ApplicativeAp`
两种替代呈现的已有接口。

The binoidal migration starts the monoidal category hierarchy at its
weakest layer. [IsFct](../theories/Cat/Functor/Laws.v) groups respectfulness,
identity and composition laws on supplied maps. `HasBinoidal C` selects one
object tensor and two arrow actions; `isBinoidalL` and `isBinoidalR`
apply that same law interface separately. The `FctOfMaps` view derives the
fixed-context functors without selecting another object map. `BinoidalCat`
is now a complete record, with `BinoidalCatToCat :> Cat`, one `hasBinoidal`
choice and direct constructor `BinoidalCatOfCat`.

`BifunctorHasBinoidal` and `ArrowHasBinoidal` supply choices on fixed
categories. `BifunctorBinoidal` and `ArrowBinoidal` bundle those exact choices
and categories. `PremonoidalCat` now owns one `BinoidalCat` parent, with
`hasPremonoidal` indexed by that parent's exact tensor choice. Its
constructor and projections already provide inheritance conversions;
no forwarding conversion functions or extra category coercions are needed.
The remaining parameterized monoidal and symmetric interfaces explicitly
retain one `HasBinoidal` choice and its indexed premonoidal extension.

双侧张量迁移从幺半范畴层级的最弱一层开始。
[IsFct](../theories/Cat/Functor/Laws.v) 为给定映射分组保相等、恒等及复合定律。
`HasBinoidal C` 选择唯一对象张量及两种态射作用；`isBinoidalL`、
`isBinoidalR` 分别使用同一函子律接口。`FctOfMaps` 视图导出固定上下文
函子，不另选对象映射。`BinoidalCat` 现为完整记录，保存
`BinoidalCatToCat :> Cat`、唯一 `hasBinoidal` 选择，直接构造器为
`BinoidalCatOfCat`。

`BifunctorHasBinoidal`、`ArrowHasBinoidal` 给出固定范畴上的选择；
`BifunctorBinoidal`、`ArrowBinoidal` 打包恰好这些选择及范畴。
`PremonoidalCat` 现拥有唯一 `BinoidalCat` 父结构，`hasPremonoidal` 以父结构的
同一张量选择为索引。构造器及投影已提供继承转换，无需转发转换函数或额外范畴
强制转换。尚未迁移的参数化幺半及对称接口显式保留一份 `HasBinoidal` 选择及
以它为索引的预幺半扩展。

### Wedges and selected ends / 楔与选定 end

[Wedge](../theories/Cat/End/Wedge.v) is a record at a fixed bifunctor
and apex. `WedgeOfLegs` packages the diagonal legs and their commuting
equation, and the leg projection still gives the function view.
[Cowedge](../theories/Cat/Coend/Wedge.v) stores the corresponding opposite
wedge, with `CowedgeOfOpWedge` as its constructor. `CowedgeOf` assembles
that same record from legs and equations in the original category.

[Wedge](../theories/Cat/End/Wedge.v) 是固定双函子与顶点上的记录。
`WedgeOfLegs` 打包对角腿及其交换方程，腿投影继续提供函数视图。
[Cowedge](../theories/Cat/Coend/Wedge.v) 保存对应的反楔，构造器为
`CowedgeOfOpWedge`。`CowedgeOf` 从原范畴中的腿及方程装配同一记录。

`HasEnd` and `HasCoend` are classes for selected universal wedges of
a supplied bifunctor. `is_end` and `is_coend` describe the candidate
properties. `HasCoendOfOpEnd` uses the supplied opposite-end choice
directly, preserving its Type-valued mediator witnesses. Day convolution
and profunctor composition continue to use their particular coend choices.

`HasEnd`、`HasCoend` 是给定双函子上的选定泛楔接口，候选性质分别由
`is_end`、`is_coend` 刻画。`HasCoendOfOpEnd` 直接使用给定的反 end
选择，保留其 Type 值中介见证。Day 卷积和 Profunctor 复合继续使用各自
所需的 coend 选择。

## Pre-stable refactoring policy

## 稳定版前的重构政策

[Issue #42](https://github.com/Godalin/rocq-cats/issues/42) is the sole
repository-wide structure architecture issue. Before a stable release, prefer
clean mathematical interfaces over historical source compatibility. Migrate
actual clients, proofs, models, tests and bilingual documentation together.
Remove obsolete compatibility aliases, transitional classes and wrappers;
do not preserve constructor shapes, implicit argument forms or universe
argument positions solely because previous releases used them. Useful
mathematical views remain justified by their actual clients, rather than by
compatibility. The [README](../README.md) states the public policy and
[AGENTS.md](../AGENTS.md) gives the development rules.

[议题 #42](https://github.com/Godalin/rocq-cats/issues/42) 是全库结构架构的唯一
总议题。稳定版前优先选择清晰的数学接口，不以历史源码兼容为约束。同步迁移
实际客户端、证明、模型、测试与双语文档，移除过时的兼容别名、过渡类及包装；
不因旧版本用过某种构造器、隐式参数形式或宇宙参数位置就继续保留。有实际
客户端的数学视图仍有其价值，不能只因它最初来自包装就机械删除。
[README](../README.md) 说明公开政策，[AGENTS.md](../AGENTS.md) 给出开发规则。

This policy relaxes backward compatibility, not mathematical correctness.
Preserve specified setoid equality, Type-valued computational witnesses,
coherent inheritance, intended independent universe bounds, transparency and
absence of unintended axioms. Universe *positions* may change; needed size
independence must still be verified. Keep bounded changes and serial
integration instead of attempting an all-library rewrite in one batch.

该政策放宽向后兼容要求，不放宽数学正确性。继续验证指定广集相等、Type 值
计算见证、相干继承、所需的独立宇宙上界、透明性及没有意外公理。宇宙参数的
位置可以改变，数学所需的大小独立性仍须验证。继续采用有界修改与串行集成，
不把全库重写混为一个批次。

## Complete algebra hierarchy: current migration

## 完整代数层级：当前迁移

The concrete algebra work is recorded in
[issue #15](https://github.com/Godalin/rocq-cats/issues/15#issuecomment-6906208038).
The current local batch starts at `aa66f9a`, following accepted monoid
prerequisite `b9b357b`, on `hierarchy-packed-algebra-42`. The user expanded its
scope from fixed-parent group extensions to the whole existing vertical chain
`Magma → Semigroup → Monoid → Group`, with its actual clients. This local
batch has passed source, regression and installation validation;
it is not an accepted integration result. The user requested review before a
further integration submission.

具体代数工作记录在
[议题 #15](https://github.com/Godalin/rocq-cats/issues/15#issuecomment-6906208038)。
当前本地批次在已接收幺半群前置 `b9b357b` 之后，从 `aa66f9a` 开始，分支为
`hierarchy-packed-algebra-42`。用户将范围从固定父结构的群扩充扩大至已有完整
纵链 `Magma → Semigroup → Monoid → Group` 及实际客户端。本片已通过本地
源码、回归与安装验证，
不是已接收结果；用户要求进一步提交集成前先审阅。

The ergonomic follow-up starts at published review commit `e30adfa`, applying
the new directional-parent and operation-subject rules from #42. Its exact
54-name map is recorded separately in
[the naming guide](./Abbreviations.md#algebra-interface-ergonomics--代数接口易用性)
and [#38's naming review](https://github.com/Godalin/rocq-cats/issues/38#issuecomment-6908412626).
The earlier 195-entry abbreviation table and frozen sources are preserved.
This follow-up has passed local validation and is retained for user review;
it is not an integration result.

易用性后续从已发布审阅提交 `e30adfa` 开始，落实 #42 新增的方向父投影及
运算主题命名规则。54 项精确对照单独记录在
[命名指南](./Abbreviations.md#algebra-interface-ergonomics--代数接口易用性)及
[#38 命名审阅](https://github.com/Godalin/rocq-cats/issues/38#issuecomment-6908412626)，
保全此前 195 项缩写表及冻结来源。此后续已完成本地验证，作为当前用户
审阅检查点保留，不是集成结果。

The user has approved saving the completed local algebra work as a review
checkpoint. Earlier descriptions of uncommitted work below record the editing
history; this checkpoint includes the parent-named direct constructors,
Comm/Ext client migration, derived inverse respectfulness and simplified
unit typing. The last relevant edit passed six concrete targets and six
closed temporary reports; the preceding inverse-respectfulness step passed
14 affected targets and six closed reports. Earlier naming/constructor
checks are recorded at their respective checkpoints. Full-library integration
acceptance, push and further hierarchy migrations are separate actions.

用户已批准将完成的本地代数修改保存为审阅提交。下方早前“未提交”的描述
保留编辑过程的历史含义；本检查点包含按父结构命名的直接构造器、Comm/Ext
客户端迁移、导出的逆保相等性及简化的单位元类型标注。最后相关修改通过
六个具体目标及六项闭合临时报告；此前逆保相等性后续通过 14 个受影响目标
及六项闭合报告。更早的命名／构造器检查按各自检查点记录。全库集成验收、
推送及进一步层级迁移是独立动作。

The four complete interfaces are unparameterized `Record` objects. Each stores
its immediate parent once: `MagmaToSetC`, `SemigroupToMagma`,
`MonoidToSemigroup`, `GroupToMonoid`.
There is one coercion chain to `SetC` and its carrier, without a bypass to a
weaker ancestor. Fixed-parent classes store only the added operations and
laws: `HasMagma` selects respectful multiplication; `IsSemigroup` states
associativity of the selected magma; `HasMonoid` selects a unit with
`IsMonoid` laws; `HasGroup` selects an inverse with `IsGroup` laws. A separate
`HasSemigroup` would add no choice and is omitted.

For native carrier/equality levels `u` and `p` and law bound `l`, the complete
records live in `Type@{max(u+1,p+1,l)}`. Packing adds no strict inequalities
`u < l` or `p < l`; multiplication's `Proper` evidence still requires the
ordinary bounds `u <= l` and `p <= l`.

四个完整接口采用无参数 `Record`，每个直接父结构只保存一次，依次为
`MagmaToSetC`、`SemigroupToMagma`、`MonoidToSemigroup`、`GroupToMonoid`。
到 `SetC` 及其载体只有一条
继承转换链，不另加绕过直接父结构的祖先转换。固定父结构类只保存新增运算与
定律：`HasMagma` 选择保相等乘法，`IsSemigroup` 规定选定原群的结合律，
`HasMonoid` 选择单位元及其 `IsMonoid` 定律，`HasGroup` 选择逆及其
`IsGroup` 定律。额外的 `HasSemigroup` 不增添选择，因而省略。

原生载体／相等层级为 `u`、`p`，定律界为 `l` 时，完整记录位于
`Type@{max(u+1,p+1,l)}`。打包不额外要求 `u < l` 或 `p < l`；乘法的
`Proper` 见证仍需通常的 `u <= l`、`p <= l` 上界。

In [the monoid core](../theories/Algebra/Monoid/Core.v), `mul_unit` is the
actual `HasMonoid` field; `mul_unit_l/r` are the actual `IsMonoid` fields.
There are no additional exported definitions to emulate the old unit APIs.
The numeral notation explicitly uses the complete monoid's stored evidence.
Fixed-parent clients use these same fields with their supplied evidence.
Likewise `mul`, `mul_proper`, `mul_assoc`, `inv` and
`mul_inv_l/r` are the actual extension/property fields, without `chosen`
intermediate names or same-name forwarding definitions. Multiplication and
inverse notation pass the complete object's stored evidence explicitly.
Respectful maps and derived inverse laws remain genuine constructions; no
view independently redefines an operation or proves its laws again.

Multiplication sections `(x ⋅−)` and `(−⋅ y)` denote the existing respectful
left- and right-multiplication maps. The shared `algebra_scope` provides
these notations; their composites use ordinary `∘r`. For example,
associativity gives `((x ⋅ y) ⋅−) ≈f ((x ⋅−) ∘r (y ⋅−))`.

[幺半群核心](../theories/Algebra/Monoid/Core.v) 中，`mul_unit` 直接是
`HasMonoid` 字段，`mul_unit_l/r` 直接是 `IsMonoid` 字段，不另导出定义
模拟旧单位接口。数字记号显式读取完整幺半群保存的见证；固定父结构客户端
使用同一批字段并传入给定见证。同样，`mul`、`mul_proper`、`mul_assoc`、`inv` 及
`mul_inv_l/r` 直接作为扩充／性质字段，不保留带 `chosen` 的中间名称及同名
转发定义。乘法与逆记号显式传入完整对象保存的见证。保相等映射及导出的逆律
仍是实际数学构造，所有视图均不重新定义运算或重证定律。

乘法偏应用 `(x ⋅−)` 与 `(−⋅ y)` 分别表示既有的左乘及右乘保相等映射。
共用的 `algebra_scope` 提供这组记号，复合仍使用普通 `∘r`。
例如结合律给出 `((x ⋅ y) ⋅−) ≈f ((x ⋅−) ∘r (y ⋅−))`。

The fixed-parent inverse-uniqueness theorem `mul_ext_inv_unique` types
its elements in `MonoidOfSemigroup SG HM`, so both inverse hypotheses use
bare `1`. This view has definitionally the same carrier and specified
equality as `SG`, retaining exactly the supplied `HM`; moving the annotation
introduces no additional mathematical assumption or transport.

固定父结构的逆唯一性定理 `mul_ext_inv_unique` 将元素类型写为
`MonoidOfSemigroup SG HM`，两条逆假设因而直接使用 `1`。此视图的载体及
指定相等按定义就是 `SG` 的同一份，并保留给定的 `HM`；移动类型标注不增加
数学假设，也不引入运输。

All four cores share that one scope, delimited by `%alg`. The magma core
fixes multiplication's common grammar with `Reserved Infix` before the
operation is defined, then binds its interpretation once the complete
magma's stored evidence is available. It also defines both respectful
sections once. The semigroup core re-exports them; the monoid and group
cores add only `1` and `x⁻¹`, respectively. Their `Require Export` chain
exposes the whole family when importing only `Algebra.Group.Core`.
Each client uses `Local Open Scope algebra_scope`, or explicit `%alg`;
importing a core does not open the algebra scope for its clients.
No Notations module, automatic scope binding or repeated inherited
interpretation is needed. The old `magma_scope` / `monoid_scope` and
their `%magma` / `%monoid` delimiters are removed.

四个核心模块共用这一个作用域，以 `%alg` 显式限定。原群核心在定义运算前
用 `Reserved Infix` 固定共用乘法语法，待完整原群的保存见证可用后只绑定
一次解释，并只定义一次两种保相等偏应用。半群核心重新导出这些记号；
幺半群和群核心分别只新增 `1` 与 `x⁻¹`。`Require Export` 链使只导入
`Algebra.Group.Core` 即可获得整组声明。客户端自行使用
`Local Open Scope algebra_scope` 或显式 `%alg`；导入核心不会替客户端
打开代数作用域。不增加 Notations 模块、自动作用域绑定或重复的继承解释。
旧 `magma_scope`／`monoid_scope` 及 `%magma`／`%monoid` 分隔符均移除。

Reservations declare grammar only. They do not make an operation, scope
interpretation or instance available before its definition. Reserve only
the shared multiplication grammar here; ordinary declarations suffice for
the closed sections, unit and inverse. In particular, do not reserve the
preexisting numeral `1`. A compiled prototype also confirms that Rocq 9.3
rejects `where` clauses on `Record`/`Class`; reserve syntax and bind it
after the declaration instead of adding a staging interface or alias.
The [group-only import regression](../tests/AlgebraNotation.v) checks
all five forms, precedence, explicit delimiters and local scope lifetime.

预留只声明语法，不使运算、作用域解释或实例提前可用。本片只预留共用乘法
语法；封闭偏应用、单位元及逆使用普通记号声明即可。尤其不预留已有数字 `1`，
编译原型还确认 Rocq 9.3 拒绝 `Record`／`Class` 上的 `where` 子句；应预留
语法并在声明后绑定，不为此增加暂存接口或别名。
[只导入群核心的回归](../tests/AlgebraNotation.v) 检查五类记号、优先级、
显式分隔符与局部作用域的生效范围。

The selected inverse is the single `inv` field. The unit is named
`mul_unit`: the bare name `unit` already denotes Rocq's one-element type.
Neither stronger structures nor notation duplicate these choices. Where
short names conflict with other theories, use qualified access such as
`Cats.Algebra.Magma.Core.mul`, or supply the selected `HasMagma` explicitly.
Routine expressions use `⋅`, `1` and `⁻¹`, not repeated explicit projection
applications. For example, the transported operation is simply
`g (f x ⋅ f y)`. Ordinary law applications use inference directly, as in
`rewrite mul_assoc` in ordinary equational proofs; do not introduce local
forwarding bindings when the selected structure is already inferred. Supply factor
arguments only to identify a particular rewrite site. Unit and inverse laws
likewise infer their parent and operation; write `rewrite mul_unit_l` rather
than expanding projection parameters. `units_equiv` infers its semigroup,
elements and unit witnesses from the expected equality. Ordinary uses of `1`
need no type annotation when the expression determines its monoid. When inference cannot
identify the intended evidence, select it explicitly, without a forwarding
binding. Actual `rewrite` clients check multiplication and both section
instances through map composition. The general `func_apply_proper` instance
allows a varying bundled map to be rewritten after evaluation.
Transport laws apply the primitive preservation witnesses directly: setoid
rewriting can insert opaque standard-library helpers into Type-valued proof
data, blocking their previously transparent computations.
At a boundary between two structures on one carrier, annotate the intended
bundle, as in `f ((x : MagmaTransport) ⋅ y)`. Fixed-parent candidate theorems
still pass their independently supplied choices explicitly.

The next user-reviewed naming step uses `Comm`, `Ext` / `ext` and `Of`:
`IsCommMonoid`, `MagmaOfSetC`, `MonoidOfSemigroup`, `GroupOfMonoid`,
`SemigroupOfMagma`, `mul_ext_inv_unique` and `inv_ext_unique`.
Related commutativity instances and actual clients migrate together.
The exact 11-name step is recorded in the naming guide; module paths and
ordinary prose retain their spelling, with no compatibility aliases.

用户继续指定使用 `Comm`、`Ext`／`ext` 和 `Of`，对应
`IsCommMonoid`、`MagmaOfSetC`、`MonoidOfSemigroup`、`GroupOfMonoid`、
`SemigroupOfMagma`、`mul_ext_inv_unique` 和 `inv_ext_unique`。
相关交换性实例和实际客户端同步迁移；命名指南记录本步精确 11 项。
模块路径及普通文字保留原拼写，不增加兼容别名。

Historical source-pinned sections below retain their original names; use
the current map when reading them against this branch.

选定逆直接保存为唯一的 `inv` 字段；单位使用 `mul_unit`，因为无前缀的
`unit` 已指 Rocq 的单元素类型。更强结构及记号均不重复保存这些选择。
短名与其他理论冲突时，使用 `Cats.Algebra.Magma.Core.mul` 等限定名称，
或显式传入选定的 `HasMagma`。

普通表达式使用 `⋅`、`1` 和 `⁻¹`，不反复显式展开投影；例如运输乘法直接写成
`g (f x ⋅ f y)`。普通等式证明用公开定律直接重写，如 `rewrite mul_assoc`；
能推断选定结构时不增加本地转发绑定，仅为定位特定改写位置才传入因子参数。单位律及逆元定律同样推断父结构和运算，直接写
`rewrite mul_unit_l`，不展开投影参数。`units_equiv` 从目标相等推断半群、
元素和单位律见证。普通表达式已经确定幺半群时，`1` 无须
类型标注。推断无法确定目标见证时再显式选择，不增加转发绑定。
实际 `rewrite` 客户端检查乘法及两种偏应用在映射复合中的重写；通用
`func_apply_proper` 实例允许对变化的打包映射求值后继续重写。
运输定律直接应用基本保相等见证：广集重写可能向 Type 值证明数据引入
标准库的不透明辅助项，阻断原本透明的计算。
同一载体上的不同结构交界处注明目标包，如 `f ((x : MagmaTransport) ⋅ y)`；
固定父结构的候选定理仍显式传入各自独立给定的选择。

以下固定历史来源的章节保留原名，阅读时按
当前对照表迁移到本分支。

The [boolean](../theories/Instance/Bool/Group.v), endomorphism
([magma](../theories/Algebra/Magma/Category.v),
[semigroup](../theories/Algebra/Semigroup/Category.v),
[monoid](../theories/Algebra/Monoid/Category.v),
[group](../theories/Algebra/Group/Category.v)),
[transport](../theories/Algebra/Group/Transport.v), and sphere clients are
migrated together in this local batch. Transport takes its complete source
before the two maps; each stronger transport reuses the exact preceding parent. The batch
adds neither categories of complete algebraic objects nor an unrelated
multiple-parent diamond, and does not expand Batch 4's historical 195-entry
abbreviation map.
Sphere regressions fix both strict input carrier/equality orders and verify
by conversion that the complete object stores the specified class setoid.
The derived sphere carrier contains boundary data, and its generated equality
contains witnesses; their bounds need not equal those of the input simplicial
setoid. The commutativity comparison now uses the coefficient law directly,
through a reusable product lemma, rather than selecting a complete monoid
just to prove a law. Cylinder comparisons state the actual product, constant
unit and selected inverse directly, with only the choices needed by each
operation; the packed operations still reduce to these same data.

At published checkpoint `77a7cf0`, on Rocq 9.3.0 / Stdlib 9.2.0, the batch passed
`dune build -j2 @all @runtest @install`. Regressions cover distinct choices on
the same parent, inherited law tokens, strict native universe orders, the
transparent parent chain, actual transport and sphere computations, and
explicit model enabling. Temporary audits checked 104 algebra declarations,
58 model declarations, 44 current public names, four notation computations
and eight instance/composition probes: all 218 reports are closed. Negative
checks reject all 44 retired public names and nine older transitional names.
The 63 migrated Rocq files follow the exact identifier map, apart from three
formula line wraps; imports and mathematical content are unchanged. No
HTML/PDF export was performed.

[布尔](../theories/Instance/Bool/Group.v)、自态射
（[原群](../theories/Algebra/Magma/Category.v)、
[半群](../theories/Algebra/Semigroup/Category.v)、
[幺半群](../theories/Algebra/Monoid/Category.v)、
[群](../theories/Algebra/Group/Category.v)）、
[运输](../theories/Algebra/Group/Transport.v)及球面客户端在本批同步迁移。
运输先接受完整来源结构，再接受两个映射；更强层的运输复用恰好前一层的父
结构。本片不增加完整代数对象的范畴或无关多父菱形；历史第四批 195 项表
不变，当前 54 项代数接口名称单列记录。
球面回归固定输入载体／相等的两种严格次序，以定义转换确认完整对象保存指定
类广集。派生球面载体含边界数据，生成相等也含见证，其大小界不必等于输入
单纯广集的界。交换性比较现在通过可复用乘积引理直接使用系数定律，不再为
证明一条定律而选取完整幺半群。柱比较直接陈述实际乘法、常值单位及选定逆，
每条只需相应运算所用的选择；打包运算仍归约至同一批数据。

已发布检查点 `77a7cf0` 在 Rocq 9.3.0／Stdlib 9.2.0 下通过
`dune build -j2 @all @runtest @install`。回归覆盖同父结构上的竞争选择、继承
定律的计算标记、原生宇宙的严格次序、透明父链、实际运输与球面计算及模型的
显式启用。临时审计覆盖 104 项代数声明、58 项模型声明、44 个当前公开名、
四项记号计算及八项实例／复合检查，218 项全部闭合；负检查确认 44 个旧公开
名称及九个更早过渡名均已退役。63 个迁移后的 Rocq 文件符合精确标识符表，
除三处公式换行外无额外改动，导入及数学内容不变。未执行 HTML／PDF 导出。

Earlier notation and unit-renaming checkpoints passed full build/tests/install.
The notation checkpoint retained 218 closed temporary reports and added 12;
the later unit-name checkpoint had 231 closed reports. These are historical
results for those exact inputs, rather than reruns of the current source.
The historical 195-entry table is unchanged; the current algebra map has 54
identifiers and four scope/delimiter migrations.

此前记号及单位字段改名检查点分别通过全库／测试／安装。记号检查点保留
218 项闭合临时报告并新增 12 项；后续单位字段改名检查点共 231 项闭合报告。
这些是对应精确输入的历史结果，不表示已对当前源码重跑。历史 195 项表不变；
当前代数表包含 54 项标识符及四项作用域／分隔符迁移。

The current review checkpoint removes the 26 explicit multiplication
applications and all 30 proposed local law bindings. Algebra laws infer
ordinary parameters, including all arguments of `units_equiv`. The reusable
`func_apply_proper` instance supports actual rewriting through varying
bundled maps; four regression examples exercise products, both multiplication
sections under composition and inferred unit laws. Transport constructions
retain direct primitive applications to preserve selected witness reduction.

当前待审检查点去掉 26 处显式乘法应用及此前提出的全部 30 个局部定律绑定。
代数定律推断普通参数，`units_equiv` 的参数全部隐式。可复用的
`func_apply_proper` 实例支持对变化的打包映射作实际重写；四个回归检查乘积、
复合中的两种乘法偏应用及隐式单位律。运输构造保留直接基本定律应用，使
选定见证保持可归约。

Following the user-directed editing validation trial, the final affected
algebra targets, Set/Bool models and representative interface/transport
regressions pass with `-j2`. Sixteen temporary reports are closed: eight
rewriting/instance checks, five inferred-witness/strict-universe/assumption
checks, and three observable transport-witness computations. An interrupted
broad build is not counted as successful; full delivery validation remains
separate. This branch is saved for user review, with no integration handoff,
export or shared-environment change.

按用户指定的编辑期验证试行，最终受影响的代数目标、Set／Bool 模型及代表性
接口／运输回归以 `-j2` 通过。16 项临时报告闭合：八项重写／实例检查、
五项隐式见证／严格宇宙／假设检查及三项可观察运输见证计算。已中断的宽构建
不计成功；完整交付验证另行执行。本分支保存供用户审核，未交集成、导出或
修改共享环境。

### Local review closeout (2026-11-16)

### 本地审阅收尾（2026-11-16）

The current proof cleanup and 11-name Comm/Ext/Of migration pass a final
project-switch `dune build -j2` of 34 concrete targets: all 31 modified Rocq
modules plus the inherited-notation and transport computation/universe
regressions. The existing monoid/group extensions, Boolean and sphere
clients are included. Rocq 9.3.0, Stdlib 9.2.0 and Dune 3.23.1 are used.
The attempted full build was interrupted after the user requested a faster
validation strategy; it is not counted as successful. Its cache is retained.

当前证明整理及 11 项 Comm/Ext/Of 迁移已在项目 switch 下通过最终 34 个具体
目标的 `dune build -j2`：覆盖全部 31 个修改 Rocq 模块，以及继承记号与运输
计算／宇宙回归，包含已有幺半群／群扩充、布尔和球面客户端。工具链为
Rocq 9.3.0、Stdlib 9.2.0、Dune 3.23.1。用户要求更快的验证方案后，本轮
全量构建已中断，不计成功；已完成的缓存保留。

Fresh checks confirm that the 29 renamed files equal their pre-rename
snapshots after exactly the specified 11-name substitution, preserving the
earlier proof edits. Retired names are absent from theory/test sources;
the cumulative 54-row and separate 11-name tables agree, and both edited
guides' local links pass. The existing 11 closed signature/assumption
reports and retired-name checks are reused for unchanged inputs. This is
not a fresh rerun of all historical audits. Permanent regressions check
competing stored choices, strict universe orders, actual rewriting and
transparent transport witnesses.

本轮新检查确认，29 个改名文件恰好等于改名前快照加指定 11 项替换，保全此前
证明整理。理论／测试源码无遗留退役名，累计 54 行表与独立 11 项表一致，
两份修改指南的本地链接通过。此前 11 项闭合签名／假设报告及旧名负检查按
未变输入复用，不表示重跑全部历史审计。永久回归检查所存竞争选择、严格
宇宙次序、实际重写及透明运输见证。

The concrete target list, exit status, log and source hashes are retained
in `/tmp/hierarchy42-final-review-20261116`. Editing validation follows the
current mainline rule now synchronized into this worktree's AGENTS: select
checks by mathematical impact and reuse unchanged evidence. Targeted
validation establishes the listed coverage; final integration still requires
the full library build on its exact resulting SHA. This remains uncommitted
local review work based on `4814341`, with no push or integration handoff.
Broader #15, #38 and #42 work remains open. No additional theory, permanent
test, export or shared-environment change was introduced in this closeout.

具体目标清单、退出码、日志及源码摘要保留于
`/tmp/hierarchy42-final-review-20261116`。本 worktree 的 AGENTS 已同步当前
主线的编辑期验证规则：按数学影响选检查，复用未变证据。定向验证提供上述
覆盖范围的证据；最终集成仍须对精确结果 SHA 执行全库构建。本批仍是基于
`4814341` 的未提交本地待审成果，未推送或交集成；#15、#38、#42 的更广范围
工作继续开放。本轮收尾未新增理论、永久测试、导出或共享环境修改。

### Derivable respectfulness and interface requirements

### 可推导的保相等性与接口要求

Before adding `Proper` or analogous evidence that an operation is
well-defined on the specified equality, derive it from the existing
structural laws whenever possible. Keep the proof at the weakest sufficient
layer and expose it as an instance when appropriate. Callers should supply
independent defining data and laws, while the interface provides the
operational compatibility that follows from them. Preserve the required
Type-valued witnesses, transparency and independent universe bounds.

新增 `Proper` 或类似的操作适用条件前，先检查能否由已有结构定律推出操作
对指定相等的保相等性。可以推出时，在最弱充分层证明，并在合适时提供实例；
调用者只需给出独立的定义数据和定律，由接口提供可推导的操作相容性。保留
所需的 Type 值见证、透明性及独立宇宙上界。

For example, a raw magma's binary operation needs respectfulness as an
input: an arbitrary function on representatives need not preserve setoid
equality. In contrast, an operation satisfying `IsGroup M i` is respectful
by inverse uniqueness, using the monoid's respectful multiplication and
the two inverse laws. No additional inverse-respectfulness field is needed.
The general `inv_proper` instance now takes a supplied monoid, candidate
inverse and `IsGroup` witness directly. Complete groups obtain it through
their stored inverse laws, without a second instance. This rule concerns operational well-definedness, and does not
ask for an artificially minimal group axiom system or move ordinary group
theorems such as cancellation into required fields.

例如，原群的原始二元运算需要输入保相等性：任意代表上的函数未必保持广集
相等。相反，满足 `IsGroup M i` 的运算可由逆唯一性推出保相等性，只使用
幺半群已有的保相等乘法及双侧逆律，无须新增逆保相等字段。一般实例
`inv_proper` 现直接接受给定幺半群、候选逆及 `IsGroup` 见证；完整群通过
保存的逆律获得该实例，不另建第二份实例。这条规则针对操作的适用条件，不要求人为压缩群的定义公理体系，也不
将消去律等通常的群论定理改作必填字段。

The inverse-respectfulness follow-up passes 14 concrete group, transport,
Boolean and sphere targets with the project switch. A permanent regression
rewrites a raw inverse candidate under multiplication using only `IsGroup`.
Six temporary assumption reports are closed, including strict carrier/equality
orders and actual candidate/complete-group rewriting. At explicit transport
and cylinder boundaries, clients pass the stored `IsGroup` witness to pin
the intended parent and universe bounds. `inv_resp` likewise uses its stored
witness; no additional group-specific instance is added. Evidence:
`/tmp/hierarchy42-inv-proper`, with the initial failed inference check kept
separate from the final passing build. This remains uncommitted local work;
no full-library build is claimed.

逆保相等性后续在项目 switch 下通过 14 个具体群论、运输、布尔及球面目标。
永久回归仅给出 `IsGroup`，就在乘法内部实际重写候选逆。六项临时假设报告
闭合，覆盖严格载体／相等次序及候选逆／完整群的实际重写。在显式运输与柱
边界，客户端传入保存的 `IsGroup` 见证，以固定所用父结构及宇宙上界；
`inv_resp` 同样使用其保存的见证，不另增完整群专用实例。证据位于
`/tmp/hierarchy42-inv-proper`，初次推断失败与最终通过的构建分别保留。
修改仍未提交，不声称全库构建通过。

### Named algebra record constructors

### 具名代数记录构造器

The user-directed follow-up makes `MagmaOfSetC`, `SemigroupOfMagma`,
`MonoidOfSemigroup` and `GroupOfMonoid` the actual record constructors. The four
separate packing definitions are removed. Each constructor directly takes
its immediate parent and extension/property witness; `Arguments ... : clear
implicits` keeps both arguments explicit. Named-field literals, parent
coercions, instance projections and selected computational witnesses use
the same fields. No forwarding alias or new mathematical structure is added.

用户指定的后续将 `MagmaOfSetC`、`SemigroupOfMagma`、`MonoidOfSemigroup` 和
`GroupOfMonoid` 直接作为记录构造器，移除四个独立打包定义。每个构造器直接接受
父结构及扩充／性质见证，以 `Arguments ... : clear implicits` 保持两个参数
显式。具名字段字面量、父结构转换、实例投影及选定计算见证仍使用同一组字段，
不增加转发别名或数学结构。

Names follow `TargetOfParent`, paired with the stored `TargetToParent`
projection. The witness type expresses which additional choices or laws
are required; constructor names consistently describe the parent instead.

名称统一遵循 `TargetOfParent`，与保存的 `TargetToParent` 父投影配对。
见证类型说明需要增加哪些选择或定律，构造器名称统一说明父结构。

| Constructor / 构造器 | Parent projection / 父投影 |
| --- | --- |
| `MagmaOfSetC` | `MagmaToSetC` |
| `SemigroupOfMagma` | `SemigroupToMagma` |
| `MonoidOfSemigroup` | `MonoidToSemigroup` |
| `GroupOfMonoid` | `GroupToMonoid` |

The preceding 29-file snapshot-substitution result describes the earlier
rename-only checkpoint. These four core files now additionally change the
constructor declarations; the public rename map still has 54 rows, with four
constructor targets updated to the parent-based names. Validation of this
follow-up is recorded separately from that earlier result.

前述 29 文件快照替换结果对应更早的纯改名检查点。本次四个核心文件还修改了
构造器声明；公共改名表仍为 54 行，其中四个构造器目标已同步更新为基于父结构
的名称。本次验证与此前结果分别记录。

Final current-source validation with the project switch passes all 34
concrete algebra/client/regression targets. Temporary constructor-pattern
and public-signature checks give 19 closed assumption reports; the four
intermediate names and the default `Build_*` names are absent. Strict
universe orders, competing stored choices and transparent transport-witness
computations are covered by the compiled regressions. Eleven client/core
files are exact token renames; the semigroup core additionally preserves
the user's proof formatting, with a missing sentence terminator repaired.
The four constructors have explicit parent/witness arguments, and the
named-field literals remain valid. Evidence is retained separately in
`/tmp/hierarchy42-parent-constructors`. No full build was run for this step;
the changes remain uncommitted local review work.

最终当前源码在项目 switch 下通过全部 34 个具体代数／客户端／回归目标。
临时构造器模式匹配及公开签名检查得到 19 项闭合假设报告；四个中间名及默认
`Build_*` 名均不存在。编译的回归覆盖严格宇宙次序、所存竞争选择及透明运输
见证计算。11 个客户端／核心文件为精确词元替换；半群核心还保留用户的证明
排版，并补正缺失的句点。四个构造器均显式接受父结构及见证，具名字段字面量
继续可用。证据单独保留于 `/tmp/hierarchy42-parent-constructors`。
本步未运行全库构建，修改仍为未提交的本地待审成果。

### Historical first-slice evidence

### 首片历史证据

The earlier fixed-parent monoid slice was accepted as `b9b357b` from frozen
`4a2cf72`, after appended compatibility corrections to original `128774b`.
Its full library/tests/install, 35 closed probes, ten complete old/new API
comparisons and seven old calls passed. The
[independent acceptance record](https://github.com/Godalin/rocq-cats/issues/15#issuecomment-6906061569)
remains valid for that precise historical result. Those old signature and
universe-position comparisons do not impose compatibility obligations on the
current complete-object migration. Frozen sources and their refs remain
preserved.

此前固定父结构的幺半群首片由冻结来源 `4a2cf72` 接收为 `b9b357b`，来源中
保留对原 `128774b` 的追加兼容修正。其全库／测试／安装、35 项闭合探针、
十项完整新旧 API 比较及七个旧调用通过。
[独立验收记录](https://github.com/Godalin/rocq-cats/issues/15#issuecomment-6906061569)
仍是该精确历史结果的有效证据；当时的签名及宇宙位置比较不对当前完整对象
迁移施加兼容义务。冻结来源及其引用继续保全。

## Cat Record foundation and Adj naming follow-up

## Cat Record 基础及 Adj 命名后续

The user requested continuing from categories themselves while completing
the remaining adjunction abbreviations. On `9dd8b86`, the first bounded
foundation changes complete `Cat` from `Class` to `Record`. It owns the same
object type, hom-setoids, identities, composition and laws once. `Ob :> Type`
remains its sole sort view; `Hom` and `HomEq` are still computed from the
same `HomSet`. Composition respectfulness remains a defining field, not an
extra equivalence or unproved assumption. No staging data record or chosen
category class is introduced.

用户要求补齐伴随缩写，并从范畴本身继续底层重构。在 `9dd8b86` 上，首个有界
基础批次将完整 `Cat` 从 `Class` 改为 `Record`；对象类型、Hom 广集、恒等、
复合及定律仍只保存一份。`Ob :> Type` 仍为唯一类型视图，`Hom` 与 `HomEq`
仍由同一 `HomSet` 计算。复合保相等性保留为定义字段，不增加额外等价结构或
未证假设，也不引入分阶段数据记录或选定范畴类。

Generic objects use their named category (`X : C`, or explicit `@Ob C`)
where the former ambient-class default supplied it. Arrow projections keep
implicit category parameters inferred from those object types. Fixed-data
`Has*` and `Is*` extensions retain their category parameters and classes;
their operations and choices are not repacked. `SetCat`, `FctCat`, `CatCat`
and `FamCat`, the former `Cat` instances, become canonical record values.
Canonical inference uses their `Ob` projections; `HomSet` is marked
`canonical=no` so common hom-set constructors do not select a category.
This removes global ambient-category choice while retaining the object view.
The interface regression rejects selecting an ambient category merely by
class search after importing the set model. The named ambient argument of
`HomSet` is now `C`; former explicit `Cat := ...` callers are updated.

先前由环境类默认补出的对象类型改为使用具名范畴（`X : C`，或显式
`@Ob C`）；态射投影仍从对象类型推断隐式范畴参数。固定数据的 `Has*`／`Is*`
扩充保留其范畴参数及类，运算与选择不重新打包。此前作为 `Cat` 实例的
`SetCat`、`FctCat`、`CatCat` 和 `FamCat` 改为规范记录值。规范推断使用其
`Ob` 投影；`HomSet` 标为 `canonical=no`，不让共用的 Hom 广集构造器
选取范畴。这在保留对象视图的同时移除全局环境范畴选择。接口回归检查导入
集合模型后，类搜索不能默认选取环境范畴。`HomSet` 的具名环境参数现在为
`C`，先前显式写作 `Cat := ...` 的调用同步更新。

The independent 34-name `Adj` / `Of` map is recorded in the naming guide.
It shortens the remaining `adjunction` components and updates the selected
constructors `AdjOfHom`, `FreeObjOfUniversal` and `ClosOfUniversal`, while
retaining the mathematical transposition names `adjunct` and `unadjunct`.
Actual clients and bilingual code references migrate together. `Cat`, its
models and affected consumers are validated before any wider
cartesian, monoidal, Topos or CwF hierarchy migration. The user approved
saving this reviewed batch, the lift follow-up and development-check rules
as a local checkpoint. No push or integration handoff is included.

独立的 34 项 `Adj`／`Of` 表记录于命名指南，缩写剩余 `adjunction` 片段，
更新指定构造器 `AdjOfHom`、`FreeObjOfUniversal`、`ClosOfUniversal`，并保留
`adjunct`／`unadjunct` 的数学转置名称。实际客户端及双语代码引用同步迁移。
本批先验证 `Cat`、模型及受影响消费者，再考虑更广的笛卡尔、幺半、Topos
或 CwF 层级迁移。用户已批准将本批、提升映射后续及开发检查规则一同保存为
本地检查点；未推送或交接。

Validation uses Rocq 9.3.0, Stdlib 9.2.0 and Dune 3.23.1 in the existing
`rocq-cats` switch. At the Cat Record/Adj naming checkpoint, before the
lift follow-up, the incremental build passed all 776 `.vo`
targets (605 theory modules and 171 tests), with unchanged source/build
inputs during that pass. Temporary audits check the 34 renamed signatures
and retired names; all 34 assumption reports close under the global context.
A separate Cat audit passes strict hom/equality universe orderings, the four
canonical object/Hom views, transparent set-model computations and 13 closed
assumption reports. The ambient-category rejection now lives in
`tests/CoreInterfaces.v`; temporary audit files stay outside the repository.
`git diff --check` passes. No HTML/PDF export or CI claim is included.

验证使用现有 `rocq-cats` switch 中的 Rocq 9.3.0、Stdlib 9.2.0 和
Dune 3.23.1。在提升映射后续之前，Cat Record／Adj 命名检查点的增量构建
通过全部 776 个 `.vo` 目标（605 个理论模块及
171 个测试），该轮源码及构建输入未变化。临时审计检查 34 项新名签名及旧名
退役，34 项假设报告均闭合。独立 Cat 审计通过 Hom／相等见证宇宙的严格
双向排列、四个规范对象／Hom 视图、集合模型计算透明性及 13 项闭合假设报告。
环境范畴拒绝回归现位于 `tests/CoreInterfaces.v`；临时审计文件位于仓库外。
`git diff --check` 通过；未导出 HTML／PDF，也不声称 CI 通过。

## Native maps across universe lifts / 跨宇宙提升的原生映射

`LiftT` exposes the constructor `Lift`, so single-field values and
equality tokens use `Lift x` instead of a record literal.
`Set.Morphism.unlift_resp`, written `f^↓S`, recovers a native respectful
map from a map between lifted sets. Its source and target lift bounds are
independent, and its native Proper bound stays independent of both.
`unlift_resp_apply` handles arbitrary wrapped inputs;
`unlift_lift_resp` recovers a lifted native map pointwise. Their statements
use specified set equality, without comparing preservation records.

`LiftT` 暴露构造器 `Lift`，单字段值及相等标记写作 `Lift x`。
`Set.Morphism.unlift_resp`（记作 `f^↓S`）从提升后集合间的映射恢复原生
保相等映射。源、目标提升的上界独立，原生 Proper 上界也独立于两者。
`unlift_resp_apply` 处理任意包装输入，`unlift_lift_resp` 逐点恢复提升前的
原生映射。定律使用指定集合相等，不比较保相等记录。

Both adjunction hom maps now use this common recovery operation.
Their inverse equations reuse `unlift_resp_apply`, and naturality uses
the short `Lift` constructor at the remaining universe boundary.
The forward and inverse maps, including their preservation witnesses,
remain transparent.

伴随的正反 Hom 映射共用此恢复操作，互逆方程复用 `unlift_resp_apply`，
自然性在剩余宇宙边界使用简短的 `Lift` 构造器。正反映射及其保相等见证
保持透明。

This later local slice uses targeted validation: `@check-core`, the set
adjunction model, adjunction-induced monads, free-object adjunctions,
exponential Hom and closure regressions. Temporary audits check strictly
separated native/lift/Proper levels, both hom/equality level orderings,
rewriting, identity-adjunction reduction, observable equality-token reduction
and eight closed assumption reports. The earlier full-build record above
belongs to its preceding checkpoint; no new full-library or full-test run
is claimed for this slice.

此后续本地片段使用定向验证：`@check-core`、集合伴随模型、伴随诱导 Monad、
自由对象伴随、指数 Hom 及闭包回归。临时审计检查原生／提升／Proper 层级严格
分离、Hom／相等层级的两种排列、重写、恒等伴随归约、可观察相等标记归约及
八项闭合假设报告。上方全量构建记录属于此前检查点；此片段不声称重新跑过
完整库或全部测试。

## Natural transformations as records / 自然变换作为记录

The `828db11` follow-up changes `Nat F G` from a class into a record.
Its endpoints remain supplied functors; the component family `nt` is
the unique function view, and `nat_naturality` stores the same Type-valued
hom equations. No category, component family or law is duplicated.
Naturality is not rebuilt by clients, and pointwise equality continues to
ignore native equality of component functions and law fields.

`828db11` 后续将 `Nat F G` 从类改为记录。两端仍由给定函子索引，
分量族 `nt` 是唯一函数视图，`nat_naturality` 保存同样的 Type 值
Hom 方程，不重复保存范畴、分量族或定律。客户端无须重建自然性，
逐点相等仍不要求分量函数或定律字段原生相等。

`IdN` and `CompN` are transparent definitions, with no notation wrapper
or global instance choosing a transformation. Inverse, whiskering,
horizontal composition and opposite transformations use direct N-suffixed
construction names. The `NatPrism*` clients and all affected consumers
follow the exact map in [the naming guide](./Abbreviations.md).
The foundational regression checks that fixing endpoints does not make
instance search select even the identity transformation.

`IdN`、`CompN` 是透明定义，不通过记号包装，也不通过全局实例默认选择
自然变换。取逆、须化、水平复合及取反同样使用直接的 N 后缀构造名。
`NatPrism*` 客户端及受影响消费者按[命名指南](./Abbreviations.md)的精确
映射迁移。基础回归检查：指定两端函子后，实例搜索也不得默认选出恒等自然变换。

`CartesianCat` is renamed `CartCat`; its current category parameter,
choices and class status remain. Its computed category view is
`CartCatToCat`; the CCC parent becomes `CCCToCartCat`, and that same
projection remains registered for inherited instance search.
CCC exponentials still use its parent's selected products. Complete
`CartCat` / `CCC` bundling remains the next structural slice.

`CartesianCat` 改为 `CartCat`，当前范畴参数、选择及类的地位不变。
计算得到的范畴视图名为 `CartCatToCat`，CCC 父视图改为
`CCCToCartCat`，仍注册同一投影供继承实例搜索使用。
CCC 指数继续使用父结构选定的积，完整 `CartCat`／`CCC` 打包留待下一结构片段。

Local validation used the project switch (Rocq 9.3.0, Stdlib 9.2.0 and
Dune 3.23.1). `@check-library @check-tests` passed with `-j 2`, selecting
605 theory and 172 test modules, in 19 minutes 6 seconds. Subsequent
whitespace-only edits in `Cartesian/Core.v` and `End/{Core,Wedge}.v`
and formatting in `Bicategory/Cat.v` were preserved and checked with
the affected modules, `@check-core`,
Set/CCC, Topos/ETCS, STLC/CCC, Coend, Day and the computation regression.
Temporary audits also passed: strict independent universes, actual
coercions, component reduction and distinct selected inverse witnesses;
all eight semantic assumption reports and forty rename reports were
closed. These audits are temporary checks, not additional committed
tests. No HTML/PDF export or CI result is claimed.

本地验证使用项目 switch（Rocq 9.3.0、Stdlib 9.2.0、Dune 3.23.1）。
`@check-library @check-tests` 以 `-j 2` 通过，选择 605 个理论模块及
172 个测试模块，耗时 19 分 6 秒。保留随后对 `Cartesian/Core.v` 及
`End/{Core,Wedge}.v`、`Bicategory/Cat.v` 的纯空白调整，
并补验相关模块、`@check-core`、
Set/CCC、Topos/ETCS、STLC/CCC、Coend、Day 及计算回归。临时审计也已通过：
严格分离的宇宙、实际强制转换、分量归约及不同的选定逆见证；八项语义检查
与四十项改名检查的假设报告全部闭合。这些属于临时检查，不是新增已提交测试。
不声称 HTML/PDF 导出或 CI 结果。

## CCC theory organization and CCCCat

## CCC 理论组织及 CCCCat

The user-reviewed CCC organization places the bundle in
[CCC/Core.v](../theories/Cat/CCC/Core.v), preservation and bundled functors
in [CCC/Functor.v](../theories/Cat/CCC/Functor.v), and the category of
complete CCCs in [CCC/Category.v](../theories/Cat/CCC/Category.v).
The former `Cat.CCC` and `Cat.Functor.Closed` module paths are removed
without compatibility stubs. General exponential comparison wrappers now
live in `Cat.Functor.ExponentialComparison`, as transparent views of its
existing construction. They do not import the CCC theory.

按用户审阅的组织方式，完整包位于 [CCC/Core.v](../theories/Cat/CCC/Core.v)，
保持性及打包函子位于 [CCC/Functor.v](../theories/Cat/CCC/Functor.v)，
完整 CCC 的范畴位于 [CCC/Category.v](../theories/Cat/CCC/Category.v)。
移除原 `Cat.CCC`、`Cat.Functor.Closed` 路径，不添加兼容导入。一般指数比较
包装移至 `Cat.Functor.ExponentialComparison`，作为其已有构造的透明视图，
不导入 CCC 理论。

`CCCCat` uses complete bundles as objects and CCC-preserving functors as
arrows. Its hom-setoid retains natural-isomorphism witnesses and ignores
native equality of preservation fields. `CCCForgetF` maps into `CatCat`
and is faithful; `CCCCatHom` reuses `CatCatHom` for independent larger
auxiliary proof bounds without changing maps or computational preservation
witnesses. This is an actual client of the packed architecture; the general
architecture remains here and the mathematical construction is described in
[the CCC guide](./CCCStructure.md#ccc-modules-and-the-category-of-cccs).

`CCCCat` 的对象为完整结构包，态射为保持 CCC 结构的函子。Hom 广集保留
自然同构见证，不要求保持性字段原生相等。`CCCForgetF` 忘却到 `CatCat`
且忠实；`CCCCatHom` 复用 `CatCatHom`，容纳独立的较大辅助证明界，
不改变映射或保持性的计算见证。这是打包架构的实际客户端；通用架构仍在本指南，
数学构造则在 [CCC 指南](./CCCStructure.md#ccc-modules-and-the-category-of-cccs)。

## Groupoid Record follow-up

## 群胚 Record 后续

The user has completed the local review and approved saving this groupoid
and division batch as a local checkpoint. Earlier uncommitted-status notes
below describe its editing stages. Validation remains the documented
28-target groupoid naming checkpoint and six-target division follow-up,
with their signature, assumption and retired-name checks; later formatting
preserves the same tokens. Full-library integration acceptance and pushing
are separate actions.

用户已完成本地审核，并批准将群胚及除法批次保存为本地检查点。下方更早的
未提交状态描述保留其编辑阶段含义。验证采用已记录的 28 目标群胚命名检查点
及六目标除法后续，包含对应签名、假设和退役名检查；后续排版保持词元不变。
全库集成验收及推送是独立动作。

On local algebra checkpoint `4788f85`, the user requested a bounded groupoid
migration for review. `Gpd` is now a `Record`; `GpdOfCat` is its actual
constructor and `GpdToCat :> Cat` its sole category projection. The constructor
takes the category and `IsGroupoid` witness explicitly. The fixed-category
`IsGroupoid C` remains a class, and the same `isGroupoid` field supplies
inherited instance search. The former `GpdFromProperty` packing definition
and `GpdC` name are removed, without aliases.

在本地代数检查点 `4788f85` 上，用户要求实施一个有界群胚迁移供审核。
`Gpd` 现为 `Record`，`GpdOfCat` 是其实际构造器，`GpdToCat :> Cat` 是唯一
范畴投影。构造器显式接受范畴及 `IsGroupoid` 见证；固定范畴上的
`IsGroupoid C` 仍为类，同一个 `isGroupoid` 字段继续支持继承实例搜索。
原 `GpdFromProperty` 打包定义和 `GpdC` 名称已移除，不留别名。

The unique view chain remains `Gpd → Cat → Type`. No category, inverse,
property witness or selected equality is copied. The opposite and product
constructions, preorder groupoids and one-object groupoids use the direct
constructor. Existing inverse theory and its derived respectfulness keep
their fixed-category assumptions. The interface regression additionally
checks the supplied parent and property by conversion. No change to `Cat`,
other hierarchy families or concrete-model enabling is included.

唯一视图链仍为 `Gpd → Cat → Type`，不复制范畴、逆、性质见证或选定相等。
反／乘积构造、预序群胚及单对象群胚使用直接构造器；既有逆理论及导出的
保相等性保持固定范畴假设。接口回归新增了给定父结构及性质按定义保留的
检查。本批不改 `Cat`、其他层级族或具体模型的启用方式。

Project-switch validation passes 16 concrete core/model/interface/nerve
and strict-universe targets. Nine temporary assumption reports are closed;
constructor-pattern checks accept `GpdOfCat` and reject the two retired
names and default `Build_Gpd`. The fixed-category inverse theory is
byte-for-byte unchanged, including derived respectfulness. Source clients
outside the core/regression are exact identifier substitutions. The two
edited guides' local links and `git diff --check` pass. Evidence and exact
targets are retained in `/tmp/hierarchy42-gpd-record`. No full-library build,
commit, push or integration handoff is included; the user requested review.

项目 switch 下 16 个具体核心／模型／接口／nerve 及严格宇宙目标通过，九项
临时假设报告闭合；模式匹配确认 `GpdOfCat` 是实际构造器，两个退役名及
默认 `Build_Gpd` 名查找失败。固定范畴上的逆理论逐字不变，包含导出的
保相等性；核心／回归之外的源码客户端均为精确标识符替换。两份修改指南的
本地链接及 `git diff --check` 通过。证据和精确目标保留于
`/tmp/hierarchy42-gpd-record`。本批未执行全库构建、提交、推送或交接，
按用户要求保留供审核。

The dated first-slice report below retains its historical class and naming
choices. This follow-up is a separate, uncommitted review batch; validation
is recorded for its own source inputs, without a full-library acceptance claim.

下方注明基线的首片报告保留当时的类及命名选择。本后续是独立的未提交待审
批次，按自身源码输入记录验证，不声称完成全库验收。

### IsGpd and gpd operations

### IsGpd 及 gpd 运算

The user's naming review then expands this pending batch to `IsGpd`,
`isGpd`, `gpd_iso` and the `gpd_*` operation/law family. Related `_IsGpd`
instances and `BoolGpd` migrate with actual clients. The exact 48-name map
is in the naming guide. The earlier 16-target result above is evidence for
the preceding constructor-only checkpoint; the current renamed interface
has its own validation inputs. Dated historical reports retain their old names.

用户随后将待审批次的命名统一为 `IsGpd`、`isGpd`、`gpd_iso` 及 `gpd_*`
运算／定律族，相关 `_IsGpd` 实例与 `BoolGpd` 同实际客户端一起迁移。
精确 48 项表见命名指南；上方早前 16 目标结果对应仅修改构造器的检查点，
当前改名接口按自己的输入验证。注明日期的历史报告保留原名称。

The old bundle-only `gpd_inv` wrapper is removed so that the general
fixed-category inverse can use this name directly. Its hypotheses are
`C : Cat` and `IsGpd C`; inverse respectfulness remains derived. Explicit
selection uses the bundle's stored `isGpd` witness, without a second inverse
operation, a forwarding alias or equality of property records. The two
competing-choice regressions exercise exactly that stored-witness use.
Module paths, chosen data, ordinary mathematical statements and universe
conventions are preserved. No commit, push or integration handoff is included.

移除原仅用于完整结构包的 `gpd_inv` 包装，使固定范畴上的一般逆运算直接
使用此名；其假设为 `C : Cat` 和 `IsGpd C`，逆保相等性仍由定律导出。
显式选择时使用结构包保存的 `isGpd` 见证，不另建逆运算或转发别名，也不
要求性质记录相等；两个竞争选择回归检查恰好使用所存见证的行为。
模块路径、选定数据、通常数学陈述及宇宙约定保持不变，未提交、推送或交接。

The final naming checkpoint passes 28 concrete affected/representative
targets with the project switch. All 48 public signatures have closed
assumption reports, and all 48 retired-name checks pass. The fixed-category
inverse theory is unchanged after the exact identifier substitution;
20 ordinary clients match that substitution byte for byte. Core and bundle
regressions additionally remove the conflicting wrapper and select the
stored property explicitly. Strict universes, selected inverse computations,
models and nerve/horn clients are covered by the compiled targets. Exact
maps, source snapshots, logs and review patch are retained in
`/tmp/hierarchy42-gpd-names`. This is uncommitted review work; no full build,
push or integration handoff is claimed.

最终命名检查点在项目 switch 下通过 28 个具体受影响／代表性目标；48 个
公开签名的假设报告全部闭合，48 项退役名负检查通过。固定范畴上的逆理论
在精确替换标识符后保持不变，20 个普通客户端逐字符合该替换；核心及结构包
回归另移除冲突包装，并显式选取所存性质。编译目标覆盖严格宇宙、选定逆的
计算、模型及 nerve／horn 客户端。精确表、源码快照、日志及审阅补丁保留于
`/tmp/hierarchy42-gpd-names`。本批仍为未提交待审修改，不声称完成全库构建、
推送或交接。

### Division abbreviations

### 除法缩写

The next user-approved naming step uses `HasDivR`, `HasDivL`, `div_r`,
`gpd_HasDivR`, `gpd_HasDivL`, `div_r_IsGpd`, `div_l_IsGpd`,
`div_r_gpd_iff` and `div_l_gpd_iff`; the naming guide records all nine names. `HasDivL C` is definitionally
`HasDivR (C^op)`, preserving the existing opposite construction and its
computational witnesses. Only identifiers in the division core and horn
client change. The module remains `Cat.Groupoid.Division`, and no new
operation, assumption or compatibility alias is added. This step remains
uncommitted for review, separately from the preceding naming checkpoints.

下一步用户批准的命名使用 `HasDivR`、`HasDivL`、`div_r`、`gpd_HasDivR`、
`gpd_HasDivL`、`div_r_IsGpd`、`div_l_IsGpd`、`div_r_gpd_iff` 和
`div_l_gpd_iff`；命名指南记录全部九个精确名称。
`HasDivL C` 按定义仍为 `HasDivR (C^op)`，保留原反范畴构造及计算见证。
本步仅修改除法核心及 horn 客户端中的标识符；模块仍为
`Cat.Groupoid.Division`，不新增运算、假设或兼容别名。修改仍未提交供审核，
与此前命名检查点分别记录。

The division rename passes six concrete division/horn/interface/universe
targets. All nine public signatures and retired-name checks pass; ten
temporary assumption reports are closed, including the definitional
opposite identity. Both modified Rocq files exactly match the specified
token substitution, so proofs and selected witnesses are preserved.
Evidence: `/tmp/hierarchy42-div-names`. No full build, commit, push or
integration handoff is included.

除法改名通过六个具体除法／horn／接口／宇宙目标；九项公开签名及退役名检查
通过，包含反范畴定义等式的十项临时假设报告闭合。两个修改后的 Rocq 文件
均为指定词元的精确替换，保留原证明及选定见证。证据位于
`/tmp/hierarchy42-div-names`，未执行全库构建、提交、推送或交接。

## Complete category bundles: first slice

## 完整范畴打包：首个批次

The user-directed structural migration starts from integrated naming result
`76642d4`. This first bounded slice changes [Cat](../theories/Cat/Core.v) to
expose `Ob :> Type`, so an object can be written `X : C`. It adds the complete
[Gpd](../theories/Cat/Groupoid/Core.v) class with `GpdC :> Cat` and inherited
`isGroupoid :: IsGroupoid GpdC`. The sole view chain is `Gpd → Cat → Type`;
the category and computational inverse witnesses are stored once. Fixed-data
`IsGroupoid C` and the general inverse theory remain independently reusable.

用户安排的结构迁移从已集成命名结果 `76642d4` 开始。首个有界批次让
[Cat](../theories/Cat/Core.v) 通过 `Ob :> Type` 暴露对象类型，可直接写
`X : C`；新增完整 [Gpd](../theories/Cat/Groupoid/Core.v) 类，保存
`GpdC :> Cat`，并继承 `isGroupoid :: IsGroupoid GpdC`。唯一视图链为
`Gpd → Cat → Type`，范畴及可计算逆见证只保存一次。固定数据上的
`IsGroupoid C` 与一般取逆理论继续独立复用。

`GpdFromProperty` packages an explicitly supplied category and property.
`OpGpd` and `ProdGpd` reuse the existing opposite/product constructions and
their inverse laws. [PreorderGpd and CodiscreteGpd](../theories/Cat/Groupoid/Preorder.v)
and [GroupGpd](../theories/Algebra/Group/Category.v) similarly reuse the thin and
one-object theories. The existing
[EqGpd](../theories/Instance/Set/Groupoid.v) and
[BoolGroupoid](../theories/Instance/Bool/Action.v) now return complete `Gpd`
values; their category projections reduce to the original categories.
Their explicit property views read the same stored witnesses. Model modules
export the groupoid interface so clients can use its coercion chain. Clients
that selectively import only `EqGpd` explicitly import `Cat.Groupoid.Core`
as well; selecting a constructor alone does not activate its coercion.

`GpdFromProperty` 打包显式提供的范畴及性质；`OpGpd` 与 `ProdGpd` 复用
已有反范畴／乘积构造及互逆定律。
[PreorderGpd、CodiscreteGpd](../theories/Cat/Groupoid/Preorder.v) 与
[GroupGpd](../theories/Algebra/Group/Category.v) 同样复用薄群胚及单对象理论。
已有 [EqGpd](../theories/Instance/Set/Groupoid.v) 和
[BoolGroupoid](../theories/Instance/Bool/Action.v) 现在返回完整 `Gpd` 值，
范畴投影归约为原范畴，显式性质视图读取同一份保存的见证。模型模块导出
群胚接口，使客户端可用其强制转换链。只选择性导入 `EqGpd` 的客户端另行显式
导入 `Cat.Groupoid.Core`；仅选择构造器不会启用其强制转换。

For an abstract `G : Gpd`, the existing `groupoid_inv f` infers its inherited
property. When two properties live on the same definitionally equal category,
ordinary instance search can choose either in-scope property; use
`gpd_inv G f` to select precisely the bundle's witnesses, or pass the desired
property explicitly to the fixed-data theory. Creating a concrete bundle is
an explicit selection; importing models alone supplies no arbitrary `Gpd`
or groupoid structure on an unrelated category.

对抽象 `G : Gpd`，已有 `groupoid_inv f` 可推断继承的性质。同一定义相等的
范畴上若有两份性质，普通实例搜索可能选择任一在域性质；使用 `gpd_inv G f`
即可固定为该包的见证，也可向固定数据理论显式传入所需性质。构造具体包本身
就是显式选择；仅导入模型不会选取任意 `Gpd` 或无关范畴上的群胚结构。

The [bundled-groupoid regression](../tests/BundledGroupoid.v) covers dependent
objects, inherited properties, two choices on one category, transparent
boolean/opposite/product inverses, existing CCC/monoidal sort chains and both
strict hom/equality universe orders. The remaining algebra, cartesian/CCC,
topos and monoidal hierarchy migrations are later bounded slices. The dated
inventories below describe their respective baselines. At its `76642d4`
baseline this slice adds one class to 116 interfaces, making 117. Including
the subsequently integrated `ElementMap` record, the rebased tree has 118.

[群胚打包回归](../tests/BundledGroupoid.v) 覆盖依赖对象、继承性质、同一范畴
的两份选择、透明的布尔／反群胚／乘积逆、已有 CCC／幺半类型链，以及 Hom 与
相等见证宇宙的两种严格次序。剩余代数、笛卡尔／CCC、拓扑斯及幺半层级留在
后续有界批次。下方注明日期的清单对应各自基线；本片在 `76642d4` 的 116 个
接口基线上增加一个类，得到 117。计入此后已集成的 `ElementMap` 记录，
重基后的源码树现有 118 个类／记录接口。

Local validation on the `76642d4`-based working tree passed project-switch
`dune build -j2 @all @runtest @install`, the new interface regression and the
existing nerve strict-universe target. Temporary checks passed 31 public
signatures/closed assumption reports, the unique coercion graph and two
model-only imports. The first full build exposed two selective-import
failures; all five such clients were given the explicit interface import and
passed targeted validation before the successful full build. The original
fixed-category inverse theory and opposite/product proofs are byte-for-byte
preserved. The 370 exact naming rows and all touched-document paths resolve;
whitespace checks pass. No HTML/PDF export or shared-toolchain change. This
slice has user approval for committing and submission to the designated
integrator; integration acceptance is pending.

基于 `76642d4` 的本地工作树使用项目 switch 通过全库／测试／安装目标、
新增接口回归及已有 nerve 严格宇宙目标。临时检查的 31 项公共签名／假设全部
闭合，唯一转换图及两份仅导入模型的探针通过。首轮全库发现两处选择性导入
失败后，已补齐全部五个此类客户端的显式接口导入；定向验证及最终全库通过。
原固定范畴取逆理论及反／乘积证明逐字保留，370 行原命名表与全部改动文档
路径有效，差异空白检查通过。无 HTML/PDF 或共享环境变更。用户已批准本片
提交并交付指定集成者；集成验收待完成。

## Scope and decision rule

## 范围及判断标准

The survey was performed on 2026-11-09 in the issue #35 task worktree,
based on integrated commit `8ae7cbd9f09c1738e9e30f4c637004552338036d`
plus the uncommitted issue #35 work. It inventories all 246 theory source
modules: 50 `Class` declarations, 25 `Record` declarations, field coercions,
and the two explicit `Coercion` declarations. Candidate interfaces and
their principal clients were then read directly. This is an interface
survey, not a review of every proof body.

本次调查于 2026-11-09 在 #35 任务 worktree 中进行，基于集成提交
`8ae7cbd9f09c1738e9e30f4c637004552338036d` 及尚未提交的 #35 工作。
扫描覆盖全部 246 个理论源模块：50 个 `Class`、25 个 `Record`、字段强制转换
及两个显式 `Coercion` 声明；随后直接阅读候选接口及其主要客户端。
这是接口调查，不是对每个证明体的审查。

Use a bundle when an object has a distinguished underlying map, functor or
carrier together with chosen structure. Keep the data and laws in one
record/class, with one underlying view exposed through `:>`. Use `::` for
inherited instances. Derived representations are separate constructions,
and comparisons use designated equality or natural isomorphism.

当对象具有明确的底层映射、函子或载体及选定结构时，适合打包。数据和定律
保存在同一记录／类中，通过 `:>` 暴露一个底层视图；`::` 用于继承实例。
派生表示保留为独立构造，比较使用指定相等或自然同构。

A property or chosen operation on already fixed data has a different role.
Such interfaces may also contain computational witnesses in `Type`: for
example, product preservation contains universal mediators, and invertibility
contains an inverse. Calling them fixed-data interfaces does not discard
those witnesses or assert proof irrelevance.

已有固定数据上的性质或选定运算具有另一种职责。这些接口也可能携带 `Type`
中的计算见证，例如积保持性包含泛中介，可逆性包含逆。称其为固定数据接口，
不意味着丢弃这些见证或假定证明无关性。

## Implemented bundles

## 已实现的打包接口

[LaxMonoidalFct MC MD](../theories/Cat/Monoidal/Functor.v) now stores
`LaxMonoidalFctToFct :> Fct C D`, the unit comparison, natural tensorator and
three coherence laws. Clients use `L X` and `fmap L f`. The
[identity](../theories/Cat/Monoidal/Functor.v) and
[constant](../theories/Cat/Monoidal/Constant.v) constructors explicitly
choose their underlying functors. The
[monoid transport](../theories/Cat/Monoidal/Transport.v) remains derived
from `L`, including its action on homomorphisms.

[LaxMonoidalFct MC MD](../theories/Cat/Monoidal/Functor.v) 现在保存
`LaxMonoidalFctToFct :> Fct C D`、单位比较、自然 tensorator 及三条相干律。
客户端使用 `L X`、`fmap L f`。
[恒等构造](../theories/Cat/Monoidal/Functor.v)与
[常值构造](../theories/Cat/Monoidal/Constant.v)显式选择底层函子。
[幺半群传输](../theories/Cat/Monoidal/Transport.v)及其同态作用仍由 `L` 派生。

Only the base functor is a coercion target. Storing an independent functor
on monoid objects would require additional compatibility data with the base
functor; the current construction determines its operations and arrow action
directly, so no such independent choice is needed.

只有基底函子作为强制转换目标。如果另外存储一个独立的幺半群对象函子，就
需要补充其与基底函子的相容数据；当前构造直接确定运算和箭头作用，不需要
这项独立选择。

The 2026-11-10 follow-up, based on integrated commit
`b7455f5869a76862c0388967f31719058789fc47`, implements the first two survey
candidates. [CartFct](../theories/Cat/Functor/Cartesian.v) stores one
`Fct` with inherited `IsCartF` evidence. It requires only the named
source terminal/products. [CCCFct](../theories/Cat/CCC/Functor.v) adds
exponential comparison invertibility, with the single coercion chain
`CCCFct → CartFct → Fct`. Its derived `IsCCCF` instance
shares the stored cartesian evidence. Preservation adapters, identity and
composition constructors reuse the existing proofs and computational witnesses.

2026-11-10 的后续工作基于集成提交
`b7455f5869a76862c0388967f31719058789fc47`，实现了调查中的前两个候选。
[CartFct](../theories/Cat/Functor/Cartesian.v) 保存一个 `Fct`
及继承的 `IsCartF` 证据，仅要求具名来源终对象／积。
[CCCFct](../theories/Cat/CCC/Functor.v) 增加指数比较可逆性，唯一强制
转换链为 `CCCFct → CartFct → Fct`；派生的 `IsCCCF` 实例
共享保存的笛卡尔证据。保持性适配器、恒等和复合构造复用已有证明及计算见证。

General theorems keep accepting fixed `F` and preservation evidence. STLC
interpretations can therefore be packaged without changing their universal
properties; their broad migration remains a separate task. No second direct
CCC-to-functor coercion or globally chosen concrete functor is introduced.

一般定理继续接受固定 `F` 及保持性证据，因此 STLC 解释可直接打包，无须改变
通用性质；其全面迁移仍是独立任务。不引入第二条 CCC 到函子的直接强制转换，
也不全局选定具体函子。

## Existing bundles that already fit

## 已符合原则的打包接口

| Interface / 接口 | Underlying view / 底层视图 | Finding / 结论 |
| --- | --- | --- |
| [SetC and FunS_resp](../theories/Set/Morphism.v), [SetC carrier](../theories/Set/Core.v) | Carrier or respectful function / 载体或保相等函数 | Already bundled; preserve pointwise setoid equality / 已打包，保留逐点广集相等 |
| [Fct](../theories/Cat/Functor/Core.v), [Nat](../theories/Cat/Natural.v) | Object map or component family / 对象映射或分量族 | Already expose the unique computational view / 已暴露唯一计算视图 |
| [Monad](../theories/Cat/Monad/Core.v), [MonoidObj](../theories/Cat/Monoidal/Monoid.v) | Endofunctor or ambient carrier / 自函子或所在范畴的载体 | Model for the new lax bundle; fixed-data law predicates also remain / 可作为 lax 打包范式，同时保留固定数据定律谓词 |
| [CwF](../theories/DTT/CwF.v) | `TyTmF :> Fct (C^op) FamCat` | Already bundles the functor and context extension; inherited terminal/context structures use `::` / 已打包函子和上下文扩张，用 `::` 继承结构 |
| [GraphMap](../theories/Graph/Morphism.v), [GenNat](../theories/Cat/Diagram/Generator.v), [Chain](../theories/Cat/Chain.v) | Vertex map or component family / 顶点映射或分量族 | Existing coercions support direct application / 已支持直接作用 |
| [FamS](../theories/Instance/Set/Fam/Core.v), [FamMap](../theories/Instance/Set/Fam/Fixed.v), [FamC and FamF](../theories/Instance/Set/Fam/Cat.v) | Fiber family, fiberwise maps or base map / 纤维族、逐纤维映射或基底映射 | Keep the selected view; other family components stay explicit / 保持选定视图，其他族分量显式访问 |
| [SectionS_resp](../theories/Instance/Set/Fam/Section.v), [SieveMatching](../theories/Instance/Set/Sieve/Matching.v) | Section or generator values / 截面或生成元处的值 | Already apply directly and compare values without proof-field equality / 已可直接作用，按值比较而不比较证明字段 |
| [Mono and Sub](../theories/Cat/Morphism.v), [SliceHom](../theories/Cat/Slice/Core.v) | Underlying arrow / 底层箭头 | Already bundled; `Mono` also has an explicit domain-object view, which should be considered during any future coercion changes / 已打包；`Mono` 还有显式定义域对象视图，未来修改强制转换时须一并考虑 |
| [Cone](../theories/Cat/Diagram/Core.v), [Cocone](../theories/Cat/Diagram/Dual.v) | Natural transformation / 自然变换 | Cone is a specialization of `Nat`; cocone exposes the ordinary view through `CoconeN` and reuses opposite-cone data / 锥特化 `Nat`，余锥通过 `CoconeN` 暴露通常视图并复用反锥数据 |

## Named parameter views and hierarchy audit

## 具名参数视图及层级调查

The `monoidal-cat-view` follow-up starts from integrated commit
`a7c849423f6f03193c82d5f6bb20230acf63d0a0`. Its fresh inventory covers all
256 theory modules, 52 `Class` declarations, 27 `Record` declarations,
24 existing field coercions and two explicit `Coercion` commands. The
monoidal change adds one field coercion. This inventory excludes the
unintegrated `ccc-equivalence-23` task and supplements the historical
survey above. All declared interfaces were classified; inheritance fields
and the source of each coercion were inspected. Proof bodies were not
audited individually.

`monoidal-cat-view` 后续任务从集成提交
`a7c849423f6f03193c82d5f6bb20230acf63d0a0` 开始，重新扫描全部 256 个
理论模块、52 个 `Class`、27 个 `Record`、已有的 24 个字段强制转换及两个
显式 `Coercion` 命令；此次幺半修改新增一个字段强制转换。调查不包含尚未集成的
`ccc-equivalence-23` 任务，并补充上文的历史调查。所有声明的接口均已分类，
继承字段和每个强制转换的来源均已核查；没有逐一审计证明体。

[MonoidalCat C](../theories/Cat/Monoidal/Core.v) initially gained the computed
field `MonoidalC :> Cat := C`. It exposes the supplied category without
storing another one or changing any constructor argument. Clients can write
`Fct MC MD`, `@Ob MC` and `Fct (MC ×C MC) MC`. Tensor, associators,
unitors and their laws still use the named category and selected structure.
Two monoidal structures on the same category remain distinct choices;
recovering their category does not identify their tensor data. The conversion
does not enable any concrete monoidal instance.

[MonoidalCat C](../theories/Cat/Monoidal/Core.v) 起初通过计算字段
`MonoidalC :> Cat := C` 暴露给定范畴，不另存一个范畴，也不改变构造器参数。
客户端可写 `Fct MC MD`、`@Ob MC`、`Fct (MC ×C MC) MC`。张量、
结合子、单位子及其定律仍使用具名范畴和选定结构。同一范畴上的两个幺半结构
仍是不同选择，恢复底层范畴不等于识别其张量数据，也不会启用任何具体幺半实例。

A computed view of an existing parameter is compatible with a fixed-data
interface. It is different from replacing that interface by an unindexed
bundle. However, its usefulness and the whole coercion graph still need
checking: `::` supplies instance search, whereas `:>` inserts a conversion
in a term. Neither mechanism should choose a model's structure by import.

为已有参数提供计算视图，与保留固定数据接口相容，不需要将其替换为无索引的
结构包。不过，仍须检查实际用途和整张强制转换图：`::` 服务于实例搜索，
`:>` 才会在项中插入转换。两种机制都不应因导入模块而替模型选定结构。

| Family / 接口族 | Current chain or boundary / 当前链或边界 | Decision / 结论 |
| --- | --- | --- |
| [CCCFct](../theories/Cat/CCC/Functor.v) | `CCCFct → CartFct → Fct → object function` / 经笛卡尔函子和普通函子到对象函数 | Already complete; no direct bypass / 已完整，不增加直接旁路 |
| [LaxMonoidalFct](../theories/Cat/Monoidal/Functor.v), [Monad](../theories/Cat/Monad/Core.v), [VtxFct](../theories/Instance/Set/Vertex/Functor.v) | Each goes through its unique `Fct` to the object function / 各自经唯一底层函子到对象函数 | Keep `fmap` for arrows; the respectful vertex-map adapter stays explicit / 态射保留 `fmap`，保相等顶点映射的适配器保持显式 |
| [CwF](../theories/DTT/CwF.v) | `CwF → Fct → object function`; an image is a [FamC](../theories/Instance/Set/Fam/Cat.v) / 函子像为相干族 | Its selected primary view is the type-and-term functor; adding a category view needs a separate interface decision / 主要视图已选为类型与项函子，增加范畴视图须另行决定 |
| [FamC and FamF](../theories/Instance/Set/Fam/Cat.v), [FamS](../theories/Instance/Set/Fam/Core.v) | `FamC → FamS → fiber function`; `FamF → FunS_resp → base function`; fibers go through `SetC → Type` / 相干族到纤维函数，相干族态射到基底函数，纤维经广集到类型 | Already chainable; the fiber action of a family morphism remains explicit / 已可连续使用，族态射的纤维作用保持显式 |
| [Cocone](../theories/Cat/Diagram/Dual.v), [Nat](../theories/Cat/Natural.v) | `Cocone → Nat → component function` / 余锥经自然变换到分量函数 | Already complete; keep the opposite-cone construction underneath / 已完整，底层保留反范畴上的锥构造 |
| [Sub and Mono](../theories/Cat/Morphism.v), [SliceHom](../theories/Cat/Slice/Core.v) | Subobjects reach a monomorphism, then its ambient arrow; `Mono` also exposes its domain object / 子对象经单态射到所在范畴的箭头，单态射还暴露定义域对象 | Preserve existing targets; check both paths before extending / 保留现有目标，扩展前核对两条路径 |
| [MonoidObj](../theories/Cat/Monoidal/Monoid.v) | The carrier target is `@Ob C`, not a fixed record such as `SetC` / 载体目标是所在范畴的对象类型，而非固定广集记录 | Dependent targets can stop chaining; use `MonoidCarrier A` when a concrete further view is needed / 依赖目标可能中断连续转换，具体底层视图需要时显式使用载体投影 |
| [CCC](../theories/Cat/CCC/Core.v) | `CCC → CartCat → Cat`; the parent shares terminal and product choices / 经笛卡尔父结构到普通范畴，共享终对象与积选择 | Implemented in the cumulative hierarchy below; no direct bypass / 已在下述累次层级中实现，不增加直接旁路 |
| [Topos](../theories/Topos/Core.v), [ETCS](../theories/Topos/ETCS.v) | `ETCS → Topos → CCC → CartCat → Cat` | `ETCSToTopos` and `ToposToCCC` each store one immediate parent; terminal-dependent fields use that same inherited terminal / `ETCSToTopos` 与 `ToposToCCC` 各保存唯一直接父结构，依赖终对象的字段使用同一继承终对象 |
| [Group](../theories/Algebra/Group/Core.v), [Monoid](../theories/Algebra/Monoid/Core.v), [Semigroup](../theories/Algebra/Semigroup/Core.v), [Magma](../theories/Algebra/Magma/Core.v) | `Group → Monoid → Semigroup → Magma → SetC → Type`; each parent is an inherited instance / 群经幺半群、半群、原群、广集到载体类型，各父结构均为继承实例 | Implemented in the algebra hierarchy slice below, sharing one multiplication and named setoid / 已在下述代数层级批次中实现，共享唯一乘法及具名广集 |
| [IsGroupoid](../theories/Cat/Groupoid/Core.v), [IsStrictTwoCat](../theories/Cat/Bicategory/Strict.v) | Witnesses on a fixed category/bicategory, including designated equality and comparison data / 固定范畴或双范畴上的见证，含指定相等及比较数据 | A parameter view is possible, but needs a client; do not collapse higher structure or change coherence / 参数视图技术上可行，待具体客户端；不折叠高阶结构、不改变相干性 |
| [Dual chosen structures](../theories/Cat/Colimit/Core.v), [HasInitial](../theories/Cat/Terminal.v), [HasCoproduct](../theories/Cat/Coproduct/Core.v), [HasCoequalizer](../theories/Cat/Coequalizer.v), [HasPushout](../theories/Cat/Pushout.v) | `::` inherits the original theory on opposite categories / 用实例继承反范畴上的原理论 | Keep the dual presentation and ordinary wrappers; these are choices on named data, not missing carrier bundles / 保留对偶呈现及通常包装，这是具名数据上的选择，不是缺少载体的结构包 |
| [HasLimitsOfShape](../theories/Cat/Limit/Core.v), [HasFiniteHomCover](../theories/Cat/Shape/Finite.v), [HasKanFillers](../theories/Instance/Set/Simplicial/Horn.v) | Inherited structures depend on diagrams, endpoints or horn indices / 继承结构依赖图式、端点或 horn 索引 | Use instance inheritance; no single uniform carrier conversion is needed / 使用实例继承，无须统一载体转换 |
| [Clos](../theories/Set/Closure/Core.v), respectful maps, [GraphMap](../theories/Graph/Morphism.v), [GenNat](../theories/Cat/Diagram/Generator.v), [Chain](../theories/Cat/Chain.v), sections and matching families | Already expose their operation or component function / 已暴露运算或分量函数 | Keep their existing unique functional view / 保留已有唯一函数视图 |
| Remaining `Has*`/preservation interfaces, [Adj](../theories/Cat/Adjunction.v), [Comprehension](../theories/Cat/Comprehension.v), [Sieve](../theories/Cat/Sieve.v) | Operations, relations or multiple views on fixed data / 固定数据上的运算、关系或多个视图 | Retain explicit parameters as detailed below; no blanket category/functor coercions / 按下文保留显式参数，不统一增加范畴或函子转换 |
| [ArrowOb](../theories/Cat/Arrow/Core.v), [CommaOb](../theories/Cat/Comma/Core.v), [SliceOb](../theories/Cat/Slice/Core.v), commuting-square records, [Horn2Presentation](../theories/Instance/Set/Simplicial/Vertex/Filling.v), [is_unique](../theories/Meta.v), [LiftT](../theories/Set/Core.v) | Multiple endpoints or witness/presentation records / 多个端点或见证、呈现记录 | No new hierarchy edge justified / 不据此新增层级边 |
| [Cat](../theories/Cat/Core.v), [Graph](../theories/Graph/Core.v), [Bicat](../theories/Cat/Bicategory/Core.v) | Foundational structures, not an existing inheritance chain / 基础结构，尚非继承链 | Keep object/vertex types and derived underlying categories explicit / 对象、顶点类型及派生底层范畴保持显式 |

Temporary elaboration checks confirmed `Fct MC MD`, coexistence of two
structures on one category, unchanged lax object/arrow use, both strict
hom/equality universe orders, and transparent identities in setoid and
endofunctor models. They also checked existing family/CwF chains: with the
relevant interface modules imported, `U x : Type`, `f x : famC_base V` and
`(T X) a : Type` elaborate directly. For
`A : MonoidObj SetCartMonoidal`, `A : @Ob SetCat` works, but
`A : SetC` and `A : Type` do not; `MonoidCarrier A : Type` does.
The coercion graph matches declared targets, so reduction of a dependent
target to a concrete record does not automatically add another graph edge.

临时 elaboration 检查确认了 `Fct MC MD`、同一范畴上两个结构共存、
lax 对象／态射用法不变、Hom 与相等宇宙的两种严格次序，以及广集和自函子
模型的恒等运算保持透明。相干族和 CwF 的已有链也已检查：导入相关接口模块后，
`U x : Type`、`f x : famC_base V` 和 `(T X) a : Type` 均可直接使用。
对 `A : MonoidObj SetCartMonoidal`，`A : @Ob SetCat` 可用，
但 `A : SetC`、`A : Type` 不可用，显式 `MonoidCarrier A : Type` 可用。
强制转换图按声明的目标匹配；依赖目标能归约为某个具体记录，不会自动增加
一条新的图边。

The first change implements the monoidal category view; the continuation
below adds group/monoid views and the cumulative cartesian/CCC hierarchy.
The ETCS slice below extends this chain through its shared CCC parent.
At that checkpoint `Cat` had no coercion to its object type; the first
complete-bundle slice above adds it. `Fct` still uses its object function
as its sole function coercion; arrow mapping stays `fmap`.

首项修改实现幺半结构的底层范畴视图；下述后续工作增加群／幺半群视图及
笛卡尔／CCC 累次层级。下述 ETCS 批次通过共享 CCC 父结构进一步延伸此链。
该检查点的 `Cat` 尚无到对象类型的强制转换；上方完整打包首片已添加此转换。
`Fct` 仍以对象函数为唯一函数强制转换，态射映射保留 `fmap`。

This follow-up passed `dune build @all @runtest @install` using
`opam exec --switch=rocq-cats`, Rocq/Stdlib 9.2.0, OCaml 5.3.0 and
Dune 3.23.1. Eight temporary `Print Assumptions` checks, covering the view,
ordinary and tensor functors, composition preservation, both equality
levels and concrete identity computation, reported `Closed under the
global context`. Strict bilingual HTML export generated 256 modules per
language and checked links and anchors in 517 pages; the new field's
adjacent explanations were checked in both editions. No permanent test
or shared toolchain change was needed. PDF export belongs to the next
integration batch. These are local results, not a CI-status claim.

此次后续工作使用 `opam exec --switch=rocq-cats`，在 Rocq／Stdlib 9.2.0、
OCaml 5.3.0、Dune 3.23.1 下通过 `dune build @all @runtest @install`。
八项临时 `Print Assumptions` 检查覆盖底层视图、普通及张量函子、复合保持、
两种相等层级及具体恒等计算，均报告 `Closed under the global context`。
严格双语 HTML 导出每种语言 256 个模块，检查了 517 页的链接及锚点；新增
字段旁的说明已在两种语言中核查。无需增加永久测试或修改共享工具链。
PDF 留待下一集成批次统一导出。以上为本地验证结果，不代表 CI 状态。

## Packed cartesian and topos hierarchy

## 打包的笛卡尔及拓扑斯层级

The user-approved follow-up from `ca985e0` replaces parameterized complete
classes by records. `CartCat` owns `CartCatToCat :> Cat` and its selected
terminal object and products. `CCC` owns only `CCCToCartCat :> CartCat`
and exponentials for that parent's products. `Topos` adds pullbacks and a
classifier relative to the inherited terminal; `ETCS` adds its existing
initial object, well-pointedness, split epimorphisms and NNO relative to
that same terminal. The single chain is
`ETCS → Topos → CCC → CartCat → Cat → Type`.
There is no carrier-equality field, duplicate selection or ancestor bypass.

用户批准的 `ca985e0` 后续将参数化完整类改为记录。`CartCat` 保存
`CartCatToCat :> Cat` 及其选定终对象和积；`CCC` 只保存
`CCCToCartCat :> CartCat` 及相对于父结构积的指数。`Topos` 增加拉回及
相对于继承终对象的分类子；`ETCS` 沿用同一终对象，增加已有始对象、良点性、
满态射分裂及自然数对象。唯一链为
`ETCS → Topos → CCC → CartCat → Cat → Type`，
不增加载体相等字段、重复选择或祖先旁路。

Record-valued parents are not instances. Their `:>` projections provide
coercions; the stored fixed-data `Has*` and `Is*` fields remain instances.
A bundle variable supplies its own choices through these projections.
Concrete models stay explicit definitions, without global model-selection
instances or canonical registrations that would enable their choices by import.
When several bundles compute to one category, pass the stored evidence
explicitly wherever a construction must distinguish their choices.

记录值父结构不是实例。其 `:>` 投影提供强制转换，保存的固定数据 `Has*`、
`Is*` 字段仍是实例；结构包变量通过这些投影提供自身选择。具体模型保持显式
定义，不注册会在导入时启用选择的全局模型实例或规范结构。
若多个结构包计算到同一范畴，需要区分选择的构造显式传入保存的证据。

```coq
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.CCC.Core.

Section CumulativeViews.
Context (C : CCC).

Definition cartesian_view
  : CartCat
  := C.
Definition category_view
  : Cat
  := C.
Definition identity_view
  : Fct C C
  := IdF.
Definition inherited_terminal
  : HasTerminal C
  := ltac:(typeclasses eauto).
Definition inherited_product
  : HasProduct C
  := ltac:(typeclasses eauto).
End CumulativeViews.
```

General product, exponential, Topos logic and computational Arrow theorems
keep their weaker fixed-data hypotheses. Freyd is still an extension on
named categories: it stores `hasValueTerminal` and `hasValueProduct`, replacing
its former cartesian bundle field without adding a second value category.
CCC preservation instead takes complete endpoints: `IsCCCF F` is indexed
by the selected CCCs, and `CCCFct C D` stores the same underlying cartesian
functor and preservation witnesses. No extra functor is introduced.

一般积、指数、Topos 逻辑及计算 Arrow 定理保留较弱的固定数据假设。
Freyd 仍是具名范畴上的扩充，改存 `hasValueTerminal` 和 `hasValueProduct`，
取代原笛卡尔结构包字段，不增加第二份值范畴。CCC 保持性则由完整两端索引：
`IsCCCF F` 绑定选定 CCC，`CCCFct C D` 保存同一底层笛卡尔函子及保持见证，
不增加另一份函子。

STLC semantics now takes `C : CCC`; its all-model families quantify
`CCC@{b b e l l}` directly. Explicit result bounds on `CtxCat_CCC` and
`TyCat_CCC` retain strict `b < e < l`, while interpretation and preservation
also retain both strict hom/equality size orderings. The older class-based
checkpoints elsewhere in this document are historical.

STLC 语义现接收 `C : CCC`，全模型族直接量化 `CCC@{b b e l l}`。
`CtxCat_CCC`、`TyCat_CCC` 的显式结果界保留严格的 `b < e < l`，解释及
保持性也保留 Hom／相等大小的两种严格次序。本文其余旧类式检查点属于历史记录。

Local validation passed with Rocq 9.3.0, Stdlib 9.2.0 and Dune 3.23.1:
`@check-library @check-tests` selected 605 theory and 173 test modules
(2 minutes 54 seconds at `-j 2`, reusing the worktree cache). After adding
native-category conversion assertions for the presheaf and normalization
gluing models, the same aliases passed again with unchanged library inputs.
`BundledCartesian` checks explicit model selection, actual ETCS coercions,
ordinary inherited notation, and two distinct terminal-map computations over
one category. Existing universe regressions and STLC completeness also pass.
Twenty temporary assumption reports are closed, including both strict size
orders, dependent classifier/NNO choices and concrete witnesses. The updated
README and hierarchy code examples compile. No HTML/PDF or CI result is claimed.

本地验证在 Rocq 9.3.0、Stdlib 9.2.0、Dune 3.23.1 下通过：
`@check-library @check-tests` 选择 605 个理论模块及 173 个测试模块，
以 `-j 2` 复用 worktree 缓存耗时 2 分 54 秒。随后补强预层及正规化粘合
模型的原生范畴转换断言，库输入不变，同一组入口再次通过。
`BundledCartesian` 检查显式模型选择、实际 ETCS 强制转换、普通继承记号，
以及同一范畴上两份不同终箭头的实际计算。已有宇宙回归和 STLC 完备性均通过；
二十项临时假设报告全部闭合，覆盖两种严格大小次序、依赖的分类子／自然数
选择及具体见证。更新的 README 及层级代码示例也已编译，不声称 HTML/PDF
导出或 CI 结果。

The [setoid](../theories/Instance/Set/Cartesian.v),
[context syntax](../theories/STLC/CCC.v) and
[type syntax](../theories/STLC/TypeCategory.v) models expose explicit
cartesian bundles, reused by their existing CCC bundles. Importing them
does not choose a concrete instance. The
[cartesian monoidal construction](../theories/Cat/Monoidal/Cartesian.v)
still derives from the selected terminal and products when requested;
it is not another stored parent or coercion path. General product and
exponential theorems retain their weaker original hypotheses.

[广集](../theories/Instance/Set/Cartesian.v)、
[上下文语法](../theories/STLC/CCC.v)及
[类型语法](../theories/STLC/TypeCategory.v)模型暴露显式笛卡尔包，由原有
CCC 包复用。导入时不自动选取具体实例。
[笛卡尔幺半构造](../theories/Cat/Monoidal/Cartesian.v)仍在需要时由选定
终对象与积派生，不是另一份保存的父结构或强制转换路径。一般积与指数定理
保留原有的较弱前提。

This hierarchy change passed the full build, test and install targets with
the existing `rocq-cats` switch (Rocq/Stdlib 9.2.0, Dune 3.23.1). Forty-four
temporary `Print Assumptions` checks reported `Closed under the global
context`. They cover the coercion chain and inherited choices, both strict
hom/equality universe orders, the three model assemblies, and six concrete
setoid reductions. Negative checks confirm that import alone selects no
model and that the cartesian bundle supplies no exponential instance.
The existing universe test only updates two fully qualified projection
names to their new parent module. No permanent test or shared alias was
added. Strict bilingual HTML generated 278 modules per language and checked
561 pages; all six new or updated source pages were checked in both
languages. PDF export remains with the integration batch.

此次层级修改在已有 `rocq-cats` switch 下，以 Rocq／Stdlib 9.2.0、Dune 3.23.1
通过全库构建、测试及安装。四十四项临时 `Print Assumptions` 检查均报告
`Closed under the global context`，覆盖转换链与继承选择、Hom／相等宇宙的
两种严格次序、三个模型装配及六项具体广集归约。反向检查确认导入本身不选取
模型，笛卡尔包也不提供指数实例。原有宇宙测试仅将两个全限定投影名更新到
新父模块，没有新增永久测试或共享别名。严格双语 HTML 每种语言生成 278 个
模块，检查 561 页；六个新增或更新的源码页面均已检查英中文正文。
PDF 仍由集成批次统一导出。

## Computational-model continuation

## 计算模型接口后续工作

**Historical checkpoint:** the parameterized algebra interfaces and parent
instance registrations described in this section belong to the named earlier
baseline. For the current complete-record migration, use the
[current algebra section](#complete-algebra-hierarchy-current-migration).

**历史检查点：** 本节具参代数接口及父实例注册属于下方注明的旧基线。
当前完整记录迁移见[当前代数章节](#complete-algebra-hierarchy-current-migration)。

The continuation on `monoidal-cat-view`, following `3a47f38`, applies the
same design to the algebraic foundations of the computational models.
[Monoid M](../theories/Algebra/Monoid/Core.v) originally had the computed
field `MonoidS :> SetC := M`. The algebra slice below moves that view to
[Magma](../theories/Algebra/Magma/Core.v) as `MagmaS :> SetC := M`, and
stores the intermediate parents as `MonoidSG :> Semigroup M` and
`SemigroupM :> Magma M`. The first hierarchy-normalization slice makes
[Group G](../theories/Algebra/Group/Core.v) expose its parent directly as
`GroupM :> Monoid G`, with `Existing Instance GroupM` for inherited search.
The unique chain is now `Group → Monoid → Semigroup → Magma → SetC → Type`;
the chosen
algebraic operations and carrier are shared. The original continuation had
26 field coercions and three explicit coercion commands; the current
hierarchy uses the direct parent field instead of the separate group
coercion command.

`monoidal-cat-view` 在 `3a47f38` 之后的后续工作，将同样的设计应用到计算
模型的代数基础。[Monoid M](../theories/Algebra/Monoid/Core.v) 最初具有计算字段
`MonoidS :> SetC := M`。下述代数批次将此视图移至
[Magma](../theories/Algebra/Magma/Core.v)，名为 `MagmaS :> SetC := M`，
并以 `MonoidSG :> Semigroup M`、`SemigroupM :> Magma M` 保存中间父结构。
首批层级规范化使
[Group G](../theories/Algebra/Group/Core.v) 直接以 `GroupM :> Monoid G`
暴露父结构，并通过 `Existing Instance GroupM` 支持继承搜索。唯一链仍为
`Group → Monoid → Semigroup → Magma → SetC → Type`，共享选定代数运算及
载体。最初的后续工作有
26 个字段强制转换、三个显式转换命令；当前层级以直接父字段替换群的单独
转换命令。

Given `HG : Group G`, clients can pass `HG` where `Monoid G` or `SetC`
is expected and bind `x : HG` as an element of the original setoid. For
example, `SetMonoidObj HG` builds the internal monoid object using the
same selected operations. The [lax transport](../theories/Cat/Monoidal/Transport.v)
now uses `L A` and `Hom A B` through the existing monoid-carrier view.
Its tensorator notation keeps explicit carrier projections: constructing
a pair before checking its dependent endpoint does not distribute
coercions into both pair components.

给定 `HG : Group G`，客户端可在要求 `Monoid G` 或 `SetC` 的位置传入
`HG`，也可用 `x : HG` 绑定原广集的元素。例如 `SetMonoidObj HG` 使用
同一组选定运算构造内部幺半群对象。[Lax 运输](../theories/Cat/Monoidal/Transport.v)
现通过已有载体视图直接使用 `L A` 和 `Hom A B`。Tensorator 记号保留显式载体
投影：先构造成对输入、再检查其依赖端点，不会把强制转换分配到两个分量中。

Monad and lax monoidal functors already have their unique underlying
functor chains. Their arrow maps still use `fmap`. Recovering a Monad from
an endofunctor-monoid presentation keeps the explicit `MonoidCarrier`
projection, as required by the dependent-target boundary above. Single-object
category interpretations and Monad/monoid correspondence maps remain derived
constructions. This continuation does not select concrete instances globally
or add Applicative, computational Arrow or tensorial-strength interfaces.

Monad 和 lax 幺半函子已有唯一的底层函子转换链，态射映射继续使用 `fmap`。
从自函子幺半群呈现恢复 Monad 的适配器仍须按上文的依赖目标边界，显式使用
`MonoidCarrier`。单对象范畴解释及 Monad／幺半群对应映射保留为派生构造。
此后续工作不会全局选定具体实例，也不新增 Applicative、计算 Arrow 或张量强度接口。

The existing `rocq-cats` switch passed `dune build @all @runtest @install`
after these changes. Temporary checks cover both strict carrier/equality
universe orders, inherited instance search, two structures on the same
setoid, direct group-to-monoid model adapters and transparent Boolean-xor
operations through lax transport. Eleven temporary `Print Assumptions`
checks reported `Closed under the global context`. The checks add no
permanent test sources or shared test aliases. Strict bilingual HTML
export again generated 256 modules per language and checked 517 pages;
the added field and carrier-use explanations were checked in both languages.
PDF export remains with the integration batch.

修改后在已有 `rocq-cats` switch 下通过 `dune build @all @runtest @install`。
临时检查覆盖载体／相等宇宙的两种严格次序、继承实例搜索、同一广集上的两个
结构、群到幺半群模型的直接适配，以及经 lax 运输后布尔异或运算的透明计算。
十一项临时 `Print Assumptions` 检查均报告 `Closed under the global context`。
检查没有新增永久测试源码或共享测试别名。严格双语 HTML 导出再次为每种语言
生成 256 个模块并检查 517 页；新增字段及载体使用说明已在两种语言中核查。
PDF 仍由集成批次统一导出。

The next serial slice implements
[Applicative](../theories/Cat/Applicative/Core.v) with the single chain
`Applicative → LaxMonoidalFct → Fct → object function`, preserving
the selected parent functor and `fmap`. Its pure operation is a natural
transformation with unit/product compatibility, rather than a competing
function coercion. See the [computation audit](./ComputationAudit.md#lawful-applicative-slice)
for the proved laws, Reader model, size checks and remaining boundaries.

下一串行切片实现了 [Applicative](../theories/Cat/Applicative/Core.v)，唯一转换链
为 `Applicative → LaxMonoidalFct → Fct → object function`，保留
选定父函子和 `fmap`。纯值运算是满足单位／积相容律的自然变换，不增加竞争的
函数强制转换。已证定律、Reader 模型、大小检查及剩余边界见
[计算模型审计](./ComputationAudit.md#lawful-applicative-slice)。

The operation-comparison slice adds
[ApplicativeOps](../theories/Cat/Applicative/Operations.v) and
[ApplicativeAp](../theories/Cat/Applicative/Application.v). Each has a single
`Fct → object function` view, preserving `fmap`; pure and application
stay explicit operations. Their conversions retain that same functor and
compare the supplied operations by designated equality. No competing
coercion to the structural Applicative is registered.

运算比较切片增加 [ApplicativeOps](../theories/Cat/Applicative/Operations.v)
及 [ApplicativeAp](../theories/Cat/Applicative/Application.v)，两者均只有
`Fct → object function` 视图，保留 `fmap`；纯值及应用仍为显式运算。
转换保留同一底层函子，使用指定相等比较所给运算，不注册到结构式 Applicative
的竞争强制转换。

The strength phase adds [StrongMonad](../theories/Cat/Monad/Strength.v)
with the unique chain `StrongMonad → Monad → Fct → object function`.
Its `hasStrength` field inherits a chosen structure on that same functor;
no second functor view is introduced. The
[MonadA conversion](../theories/Cat/Monad/Applicative.v) is an explicit
construction, preserving the parent functor and `fmap`, rather than another
coercion path. The [State model](../theories/Instance/Set/State.v) likewise
provides explicitly selected values.

强度阶段增加 [StrongMonad](../theories/Cat/Monad/Strength.v)，唯一转换链为
`StrongMonad → Monad → Fct → object function`。`hasStrength` 字段继承同一
函子上的选定结构，不增加第二个函子视图。
[MonadA 转换](../theories/Cat/Monad/Applicative.v) 为显式构造，保留父函子及
`fmap`，不增加竞争的强制转换路径；[状态模型](../theories/Instance/Set/State.v)
同样只提供须显式选定的值。

The computational [Arrow](../theories/Cat/Computational/Arrow/Core.v)
adds the unique `Arrow → Fct → object function` view, with the source
monoidal structure and target category named separately. `ComputationCat`
is an explicit reindexing of that target, not another coercion. Cartesian
first/second/split/fanout are derived operations. The concrete
[StateArrow](../theories/Instance/Set/State.v) is explicitly selected and
retains independent ambient carrier/equality levels.

计算 [Arrow](../theories/Cat/Computational/Arrow/Core.v) 增加唯一的
`Arrow → Fct → object function` 视图，分别具名指定来源幺半结构及目标
范畴。`ComputationCat` 是目标的显式重索引，不增加强制转换；笛卡尔
first／second／分开组合／扇出均为导出运算。具体
[StateArrow](../theories/Instance/Set/State.v) 须显式选择，保留独立的所在载体／
相等层级。

## Follow-up candidates

## 后续候选

| Candidate / 候选 | Current boundary / 当前边界 | Proposed treatment / 建议处理 | Main clients and risk / 主要客户端及风险 |
| --- | --- | --- | --- |
| [iso](../theories/Cat/Core.v), [NatIso](../theories/Cat/Natural.v) | Sigma bundles with `.1`/`.2` projections; unique forward arrow/transformation / 通过 `.1`、`.2` 访问的依赖和，具有明确正向箭头／自然变换 | Consider named records with a forward-map coercion while retaining `is_iso` and `is_nat_iso` / 可考虑具名前向映射的记录，同时保留固定映射上的可逆性接口 | Foundation-wide migration, including [CatCat equivalence](../theories/Cat/CatCat.v) and [representations](../theories/Instance/Set/Representable.v); separate prerequisite task, not a local rename / 牵涉范畴等价及表示，须作为独立前置任务 |
| [SectionOfS](../theories/Cat/Section.v) | Setoid carrier is a map plus its right-inverse witness / 广集载体为映射及其右逆见证 | Optional named bundled section with an arrow coercion; reuse current equality / 可增加具名截面记录及箭头强制转换，复用当前相等 | [family sections](../theories/Instance/Set/Fam/Section.v); lower priority until repeated projection access motivates it / 待重复投影使用显现需求后处理 |
| [Comprehension](../theories/Cat/Comprehension.v) | Fixed projection `P`, additional `ExtF`, natural projection and cartesian/pullback preservation / 固定投影 `P`，另含 `ExtF`、自然投影及保持性 | Decide which mathematical view is primary before adding a coercion / 添加强制转换前先确定主要数学视图 | `P`, `ExtF` and derived `ComprehensionF : E → Arr B` have different roles; no automatic choice between them / 三个函子职责不同，不能自动替选 |

The cartesian and CCC candidates are implemented above. The remaining
candidates require separate interface decisions and clients.

笛卡尔及 CCC 候选已在上文实现。剩余候选需要独立的接口决策及客户端。

## Fixed-data and relational interfaces to retain

## 应保留的固定数据及关系接口

| Interface family / 接口族 | Reason / 原因 |
| --- | --- |
| [is_faithful, is_full, is_fully_faithful](../theories/Cat/Functor/Core.v), [is_monad](../theories/Cat/Monad/Core.v), [is_monoid_object and is_monoid_hom](../theories/Cat/Monoidal/Monoid.v) | State laws about supplied data; fullness and universal properties retain computational witnesses / 陈述给定数据的定律，满性和泛性质仍保留计算见证 |
| [Adj F G](../theories/Cat/Adjunction.v) | Relates two specified functors; keep left/right views explicit / 关联两个指定函子，左右视图应显式访问 |
| [HasCartLift P](../theories/Cat/Fibration.v), [HasFreeObj U](../theories/Cat/FreeObject/Core.v) | Choose lifts or universal arrows for the existing functor; a future bundled fibration/right-adjoint view can reuse these interfaces / 为已有函子选择提升或泛箭头，未来打包视图可复用这些接口 |
| [HasDisplay](../theories/DTT/Display/Core.v), [HasContextExtension and CwF](../theories/DTT/CwF.v), [HasContextRepresentation](../theories/DTT/Context/Representation.v) | Describe interchangeable presentations over a fixed presheaf/family functor; CwF already supplies the complete bundled object / 描述固定预层／族函子上的可互换呈现，完整打包对象已有 CwF |
| [Monoid](../theories/Algebra/Monoid/Core.v), [Group](../theories/Algebra/Group/Core.v) | Historically fixed-setoid classes; the current local migration replaces them with complete records sharing one immediate parent / 历史版本为固定广集类，当前本地迁移改为共享一个直接父结构的完整记录 |
| [MonoidalCat](../theories/Cat/Monoidal/Core.v), [CCC](../theories/Cat/CCC/Core.v), [ETCS](../theories/Topos/ETCS.v), [IsGroupoid](../theories/Cat/Groupoid/Core.v), [IsStrictTwoCat](../theories/Cat/Bicategory/Strict.v) | Named-category/bicategory extensions; retain explicit chosen structures, equality relations and comparison maps / 具名范畴／双范畴上的扩展，保留显式结构、相等关系及比较映射 |
| `HasTerminal`, products, coproducts, exponentials, (co)equalizers, pullbacks/pushouts, [HasLimit and HasLimitsOfShape](../theories/Cat/Limit/Core.v), [colimit interfaces](../theories/Cat/Colimit/Core.v) | Choose constructions for fixed categories/diagrams; their derived functors remain derived / 为固定范畴／图式选择构造，其诱导函子仍是派生构造 |
| [HasFiniteCover](../theories/Set/Finite.v), [finite generators/covers](../theories/Cat/Shape/Finite.v), [horn fillers](../theories/Instance/Set/Simplicial/Horn.v), [two-horn fillers](../theories/Instance/Set/Simplicial/Vertex/Horn2.v), [IsCoskeletal](../theories/Instance/Set/Simplicial/Coskeletal.v) | Additional evidence or choices for fixed sets/categories/simplicial objects / 固定集合、范畴或单纯对象上的额外证据或选择 |
| [ArrowHom](../theories/Cat/Arrow/Core.v), [CommaHom](../theories/Cat/Comma/Core.v), [ContextMap](../theories/DTT/Comprehension.v) | A commuting square retains two distinct side maps; choosing one as its universal arrow view would hide part of its structure / 交换方形保留两条不同侧边，任取一条作为通用底层箭头会遮蔽其结构 |
| [Graph](../theories/Graph/Core.v), [Cat](../theories/Cat/Core.v), [Bicat](../theories/Cat/Bicategory/Core.v), [Sieve](../theories/Cat/Sieve.v) | Existing foundational or indexed structures have no competing stored underlying functor to remove; a new coercion requires a separate inference/use-case justification / 不存在需要消除的重复底层函子，新强制转换须另有推断及使用需求依据 |

## Migration order and verification

## 迁移次序及验证

1. The bundled lax monoidal change is implemented in the current task.
2. Cartesian and CCC bundles now reuse fixed-data preservation theorems and
   share inherited data. Migrate STLC clients in their owning task after
   integrating this interface prerequisite.
3. Treat named isomorphism records as a separate foundation task. Update
   natural isomorphisms, category equivalences, representations and dependent
   clients together; compare underlying maps without equality of proof fields.
4. Revisit optional section/comprehension bundles only with a concrete client
   and a clearly selected primary view.

1. 打包 lax monoidal 的修改已在当前任务实现。
2. 笛卡尔和 CCC 函子包现已复用固定数据保持定理并共享继承数据；集成此接口
   前置任务后，再由 STLC 所属任务迁移其客户端。
3. 具名同构记录单独作为基础任务，联动更新自然同构、范畴等价、表示及依赖
   客户端；比较底层映射，不要求证明字段相等。
4. 截面／理解结构的可选打包待具体客户端及主要视图明确后再处理。

Retained checks cover direct `fmap` use through the bundled coercion,
noninvertible constant comparisons, transparent transported operations, and
both strict hom/equality universe orders. The migration also needs the
full library/tests/install targets, strict bilingual documentation export
and temporary `Print Assumptions` checks of the foundational constructions.
Future bundles should likewise preserve independent law bounds and avoid
globally selecting concrete model structures.

保留检查覆盖经打包强制转换直接使用 `fmap`、不可逆常值比较、透明传输运算及
两种严格 Hom／相等宇宙次序。迁移还需全库／测试／安装目标、严格双语文档导出
及基础构造的临时 `Print Assumptions` 检查。未来打包也须保留独立的定律上界，
并避免全局选取具体模型结构。

The current bundled-lax migration passed `dune build @all @runtest @install`
with Rocq 9.0.1 and Dune 3.23.1 in the existing `rocq-env`/Nix environment.
Strict HTML export generated 248 modules in each language and checked links
and anchors in 501 pages. Temporary assumption checks for the identity and
constant lax structures, tensorator naturality, monoid transport, homomorphism
transport and the induced functor all reported `Closed under the global context`.
These were local checks of the lax task, subsequently integrated as
`b7455f5869a76862c0388967f31719058789fc47`.

当前打包 lax 迁移已在现有 `rocq-env`／Nix 环境下，用 Rocq 9.0.1、Dune 3.23.1
通过 `dune build @all @runtest @install`。严格 HTML 导出为每种语言生成 248 个
模块，并检查 501 页的链接和锚点。恒等及常值 lax 结构、tensorator 自然性、
幺半群传输、同态传输及诱导函子的临时公理检查均报告
`Closed under the global context`。这些是 lax 任务的本地检查，之后已作为
`b7455f5869a76862c0388967f31719058789fc47` 集成。

The cartesian/CCC follow-up passed the same full build, test and install
targets with that toolchain. Retained regressions check inherited inference,
explicit model selection, transparent composite product/exponential inverses,
mixed-level composition and STLC interpretation adapters. Strict bilingual HTML
export generated 251 modules per language and checked 507 pages. Temporary
`Print Assumptions` checks of all seven adapters, identity/composition
constructors and the inherited instance reported `Closed under the global
context`. These are local results on the task branch.

笛卡尔／CCC 后续工作在同一工具链下通过相同的全库、测试及安装目标。保留的
回归检查覆盖继承推断、显式模型选择、复合后透明的积／指数逆、不同层级复合及
STLC 解释适配。严格双语 HTML 导出为每种语言生成 251 个模块，并检查 507 页。
全部七项适配器、恒等／复合构造及继承实例的临时 `Print Assumptions` 检查
均报告 `Closed under the global context`。这些是任务分支的本地结果。

## Library-wide structure and naming audit

## 全库结构与命名审计

The original audit reads baseline `5d87331` on `monoidal-cat-view`: 278
theory modules, 60 classes and 27 records. The inventory below follows the
hierarchy, binoidal, premonoidal, Freyd and static-Arrow slices and now
covers 370 modules,
70 classes and 30 records.
It inventories every declaration, checks their parameter/field
roles and coercion declarations, and inspects
principal inheritance clients. It also considers definition-based interfaces
such as `Cone`, `iso`, `NatIso`, `is_monad`, `is_monoid_object` and
`HasLeftDivision`. It does not audit every proof body. The algebra hierarchy
example from the discussion was temporary; the final algebra slice below
implements Magma and Semigroup in the library with actual clients.

原始审计读取 `monoidal-cat-view` 上的基线 `5d87331`：278 个理论模块、60 个
类及 27 个记录。下表跟随层级、双侧张量、预幺半、Freyd 及静态 Arrow 批次
更新，现覆盖 370 个模块、70 个类及 30 个记录。清单覆盖
每个声明，核对参数／字段职责、强制转换声明及主要继承客户端；也检查通过
定义表达的接口，例如 `Cone`、`iso`、`NatIso`、
`is_monad`、`is_monoid_object` 与 `HasLeftDivision`。没有逐个审计证明体。
讨论中的代数层级起初属于临时示例；下述最后一个代数批次将原群与半群及其
实际客户端加入库中。

### Naming by interface role

### 按接口职责命名

A public mathematical structure uses its mathematical name: `Monoid`,
`Group`, `CartCat`, `CCC`, `Monad`, `Applicative`, `Arrow` or `CwF`.
A named ambient parameter fixes its carrier or category; a computed view
can expose that same parameter. A stored primary parent uses a kind-based
projection and `:>`, with a separate inherited-instance registration when
needed. `CCCToCartCat :> CartCat C` is the implemented category example.

公共数学结构直接使用数学结构名，例如 `Monoid`、`Group`、`CartCat`、
`CCC`、`Monad`、`Applicative`、`Arrow` 或 `CwF`。具名环境参数固定载体或
范畴，计算视图可以暴露同一参数。保存的主要父结构使用按数学种类命名的投影
及 `:>`，需要时另外注册继承实例。`CCCToCartCat :> CartCat C` 是已实现的
范畴例子。

The existing `Has*` interfaces choose objects, operations or families of
witnesses over supplied data. All 29 such classes retain computational
data; `HasProduct C`, for example, chooses products for all pairs, not just
one product object. `Is*` and `is_*` interfaces can also retain Type-valued
witnesses. Prefixes do not distinguish data from propositions or justify
proof irrelevance. A public bundle and an interface on fixed data can
present related mathematics with different API roles.

已有 `Has*` 接口在给定数据上选择对象、运算或见证族。全部 29 个这类接口都
保留计算数据；例如 `HasProduct C` 为每对对象选择积，并非只表示一个积对象。
`Is*` 和 `is_*` 接口也可能保留 Type 值见证。前缀不能用来区分数据与命题，
也不能据此假定证明无关性。公共结构包与固定数据上的接口可以表达相关数学，
同时承担不同的 API 职责。

The approved convention retains `Has*` for construction availability and
its selected witnesses. `HasProduct C` is the appropriate name for products
provided for every object pair. Complete structures and their primary
parent views use direct structural names. The first application below
changes the group parent and the monoidal category name; all 29 `Has*`
class names remain unchanged, together with their computational content
and opposite-based dual constructions.

已确认的规范保留 `Has*` 表达相应构造的可用性及选定见证。`HasProduct C`
为每对对象提供积，名称合理。完整结构及其主要父视图直接使用结构名。
下述首批实施修改群父结构及幺半范畴名称；全部 29 个 `Has*` 类名、计算内容
以及基于反范畴的对偶构造均保持原样。

### Existing layers and primary views

### 已有层次与主要视图

| Layer / 层次 | Modules / 模块数 | Observed boundary / 已核对边界 |
| --- | ---: | --- |
| `Meta` | 1 | Constructive, Type-valued logical vocabulary / 构造性、Type 值逻辑词汇 |
| `Set/` | 22 | Setoids, respectful maps, finite covers and closure; no category imports / 广集、保相等映射、有限覆盖与闭包，不导入范畴层 |
| `Graph/` | 6 | Graphs over the set foundation / 基于集合基础的图 |
| `Cat/` | 183 | Categories, functors, universal properties, monoidal and computational theory / 范畴、函子、泛性质、幺半及计算理论 |
| `Algebra/` | 14 | Magma/semigroup/monoid/group cores depend on sets; categories/actions add category dependencies / 原群／半群／幺半群／群核心依赖集合，其范畴及作用扩展再依赖范畴层 |
| `Instance/` | 109 | Models and model-specific bridges / 模型及模型特有的桥接 |
| `STLC/` | 22 | Syntax, interpretation and free-CCC clients / 语法、解释与自由 CCC 客户端 |
| `DTT/` | 10 | Families, display, context extension and comprehension clients / 族、显示、上下文扩张与理解客户端 |
| `Topos/` | 7 | Elementary topos structure and classifiers, plus optional representation, conjunction, predicate order, NNO and ETCS extensions / 初等拓扑斯结构与分类子，以及可选的表示、合取、谓词序、自然数及 ETCS 扩展 |

Direct import inspection confirms that `Instance.Set.Core` depends only
on `Cat.Core`; the three STLC, DTT and ETCS directions do not import one
another. Some category theories use the setoid category to express natural
hom correspondences and presheaves, and chains/shapes use the natural-number
order model. These imports serve named mathematical constructions; the
selected setoid terminal/product/CCC models remain separate.

直接导入检查确认 `Instance.Set.Core` 只依赖 `Cat.Core`，STLC、DTT 与 ETCS
三个方向之间没有相互导入。部分范畴理论使用广集范畴表达自然 Hom 对应与
预层，链与形状则使用自然数序模型。这些导入服务于具名数学构造；广集的选定
终对象、积及 CCC 模型仍分别提供。

```mermaid
flowchart LR
  Group -->|GroupM| Monoid
  Monoid -->|MonoidSG| Semigroup
  Semigroup -->|SemigroupM| Magma
  Magma -->|MagmaS, computed| SetC
  SetC -->|carrier| Type
  ETCS -->|ETCSToTopos| Topos
  Topos -->|ToposToCCC| CCC
  CCC -->|CCCToCartCat| CartCat
  CartCat -->|CartCatToCat, computed| Cat
  Gpd -->|GpdC| Cat
  Cat -->|Ob| Type
  MonoidalCat -->|monoidal_hasBinoidal| HasBinoidal
  MonoidalCat -->|MonoidalToHasPremonoidal| HasPremonoidal
  PremonoidalCat -->|PremonoidalCatToBinoidalCat| BinoidalCat
  PremonoidalCat -->|hasPremonoidal| HasPremonoidal
  HasPremonoidal -->|hasAssociator| HasAssociator
  HasPremonoidal -->|hasUnitors| HasUnitors
  BinoidalCat -->|BinoidalCatToCat| Cat
  BinoidalCat -->|hasBinoidal| HasBinoidal
  StrongMonad -->|StrongMonadM| Monad
  Monad -->|MonadF| Fct
  CCCFct -->|CCCFctToCartFct| CartFct
  CartFct -->|CartFctToFct| Fct
  Applicative -->|ApplicativeToLaxMonoidalFct| LaxMonoidalFct
  LaxMonoidalFct -->|LaxMonoidalFctToFct| Fct
  ApplicativeOps -->|OpsF| Fct
  ApplicativeAp -->|ApF| Fct
  ArrowApply -->|ArrowApplyA| Arrow
  Arrow -->|ArrowF| Fct
  CwF -->|TyTmF| Fct
  Fct -->|F0| ObjectMap
```

Arrows in this diagram are current views, including computed views; they
are not claims that every node is an inherited typeclass instance. In
particular, a `:>` field does not by itself register its parent for instance
search. `Cat` reaches its object type through `Ob`. A monoid object's carrier
has a dependent target `Ob C`, which does not automatically create a
further coercion to `SetC` when `C` specializes to the setoid category.

图中的箭头都是当前视图，包含计算视图，并不声称每个节点都已注册为继承
类型类实例；特别是 `:>` 本身不会注册父类实例。`Cat` 通过 `Ob` 到达对象类型。
幺半群对象载体的目标是依赖类型 `Ob C`，当 `C` 特化为广集范畴时，也
不会自动产生到 `SetC` 的后续转换。

### Concrete design findings

### 具体设计问题

| Priority / 次序 | Evidence / 证据 | Proposed treatment / 建议处理 |
| --- | --- | --- |
| 1 | [Group](../theories/Algebra/Group/Core.v) now exposes `GroupM :> Monoid G` / 群现直接暴露幺半群父视图 | Implemented in the first slice, with explicit parent-instance registration and updated model constructors / 首批已实施，显式注册父实例并同步模型构造 |
| 2 | [MonoidalCat](../theories/Cat/Monoidal/Core.v) and [CartCat](../theories/Cat/Cartesian/Core.v) now share the category suffix / 两者现统一范畴名称后缀 | The first slice unified names; the current fixed-parent extension is `MonoidalToHasPremonoidal` over `monoidal_hasBinoidal` / 当前固定父扩展为 `monoidal_hasBinoidal` 上的 `MonoidalToHasPremonoidal` |
| 3 | [ETCS](../theories/Topos/ETCS.v) stores `ETCSC :> Topos C`, whose `ToposC :> CCC C` shares the cartesian closed choices / ETCS 经唯一 Topos 父结构共享 CCC 选择 | Topos owns pullbacks and the classifier; ETCS adds its set-theory axioms, with dependent fields on the same terminal / Topos 持有拉回与分类子，ETCS 增加集合论公理，各依赖字段使用同一终对象 |
| 4 | [Monoid](../theories/Algebra/Monoid/Core.v) inherits [Semigroup](../theories/Algebra/Semigroup/Core.v), which inherits [Magma](../theories/Algebra/Magma/Core.v) / 幺半群继承半群，半群继承原群 | Implemented in the algebra slice with weaker multiplication maps, composition laws, Boolean and endomorphism models / 代数批次已实施，包含较弱前提的乘法映射、复合律、布尔及自态射模型 |
| 5 | [HasStrength](../theories/Cat/Monoidal/Strength.v) and [HasAxiomChoice](../theories/Topos/ETCS.v) provide compatible strength and epi-splitting witnesses on fixed data / 在固定数据上提供相容强度及满态射分裂见证 | Keep these construction interfaces under the approved `Has*` convention; preserve their choices and explicit hypotheses / 按已确认的 `Has*` 构造接口规范保留名称、选择与显式前提 |
| 6 | [IsGroupoid](../theories/Cat/Groupoid/Core.v) is an inverse-witness interface on a fixed category / 是固定范畴上的逆见证接口 | Keep its current fixed-data role unless choosing a public `GroupoidCat` entry; any such migration must preserve inverses and setoid laws / 若要改为公共 `GroupoidCat` 入口，须联动保留逆及广集定律；当前固定数据职责有其用途 |
| 7 | [CwF](../theories/DTT/CwF.v), [Comprehension](../theories/Cat/Comprehension.v), and [IsStrictTwoCat](../theories/Cat/Bicategory/Strict.v) have different primary views/coherence data / 各自有不同主要视图或相干数据 | Keep CwF's type-and-term functor view; choose a comprehension view only with a client; strictness stays relative to specified 1-cell equality and comparison / 保留 CwF 的类型与项函子视图，理解结构的视图结合客户端决定，严格性保留指定一胞相等及比较 |

The already implemented cartesian/CCC, structured-functor and computational
chains fit the direct structural-name rule. The outstanding issues concern
parent selection and naming consistency, not missing coercions for every
parameter. Alternate presentations of Applicative and the monoid/Monad
correspondence remain explicit conversions rather than extra coercion paths.

已实现的笛卡尔／CCC、带结构函子及计算接口链符合结构直接命名的原则。
待处理问题主要是父结构选择与命名一致性，不是为每个参数都补转换。
Applicative 的不同呈现以及幺半群／Monad 对应继续使用显式转换。

### The 29 chosen-construction classes

### 29 个选定构造类

| Family / 接口族 | Actual choice / 实际选择 |
| --- | --- |
| `HasTerminal`, `HasInitial` | One selected object with its universal property / 一个选定对象及泛性质 |
| `HasProduct`, `HasCoproduct`, `HasExponential` | Constructions indexed by object pairs; exponentials depend on the same selected products / 按对象对索引的构造，指数依赖同一组选定积 |
| `HasEqualizer`, `HasCoequalizer`, `HasPullback`, `HasPushout` | Constructions for each supplied parallel pair or cospan/span / 对每个给定平行箭头对或余跨度／跨度给出构造 |
| `HasLimit`, `HasColimit` | One specified diagram's universal cone/cocone / 指定图式的泛锥／余锥 |
| `HasLimitsOfShape`, `HasColimitsOfShape` | A family of choices indexed by diagrams of a fixed shape / 按固定形状的图式索引的选择族 |
| `HasCartLift`, `HasFreeObj` | Chosen lifts over a fixed functor, or universal arrows in structured-arrow categories / 固定函子上的选定提升，或结构箭头范畴中的泛箭头 |
| `HasStrength` | A compatible tensorial natural map on a specified endofunctor / 指定自函子上的相容张量自然映射 |
| `HasRightDivision` | Solutions of composition equations; `HasLeftDivision` is a definition on the opposite / 复合方程的解，`HasLeftDivision` 是反范畴上的定义 |
| `HasContextExtension`, `HasContextRepresentation`, `HasDisplay` | Chosen extensions, representations or coherent displays over a fixed family/presheaf / 固定族／预层上的选定扩张、表示或相干显示 |
| `HasNaturalNumbersObj`, `HasSubObjClassifier` | Selected universal objects relative to the selected terminal / 相对于选定终对象的泛对象 |
| `HasAxiomChoice` | Right inverses for all epimorphisms, supplied as Type-valued data / 为全部满态射提供 Type 值右逆数据 |
| `HasFiniteCover`, `HasFiniteGen`, `HasFiniteHomCover` | Finite representatives/generators with covering witnesses / 有限代表或生成元及覆盖见证 |
| `HasHornFillers`, `HasKanFillers`, `HasHorn2Fillers` | Chosen fillers indexed by horns; uniqueness and functoriality are separate requirements / 按 horn 索引的选定填充，唯一性及函子性另行要求 |

These names cannot all be shortened to a singular noun without specifying
what the noun packages. For example, a binary-product cone for one pair,
a family of chosen products, and a cartesian category are different
interfaces. Naming changes should retain those boundaries and the single
opposite-based implementation of dual constructions.

这些名称若缩写为单数名词，需要说明名词究竟打包什么。例如，一个对象对的
积锥、一族选定积、笛卡尔范畴是不同接口。改名应保留这些边界，以及通过反
范畴共用的对偶实现。

### Complete declaration inventory

### 完整声明清单

Every class and record is listed below exactly once. Group assignments
identify API roles; they do not assert that law witnesses live in Prop.
The original audit commit `1d29636` changed documentation only and checked
declaration/count coverage, source links and direct imports. The first
hierarchy application has its own validation below; earlier build and
assumption results above belong to their stated stages.

下表将每个类和记录恰好列出一次。分组表达 API 职责，不断言定律见证位于
Prop。原始审计提交 `1d29636` 只修改文档，检查声明／数量覆盖、源码链接及
直接导入。首批层级实施的验证见下文；上文较早的构建与公理检查结果属于
各自注明的阶段。

| Interface / 接口 | Declaration / 声明 | Role / 职责 |
| --- | --- | --- |
| [Interval](../theories/Cat/Homotopy/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [Homotopy](../theories/Cat/Homotopy/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [VtxPresentation](../theories/Instance/Set/Vertex/Category.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [ContextSystem](../theories/Set/Relation/Compatible.v) | `Class` | Foundations and basic maps / 基础与基本映射 |
| [Group](../theories/Algebra/Group/Core.v) | `Class` | Set algebra / 集合上的代数 |
| [Magma](../theories/Algebra/Magma/Core.v) | `Class` | Set algebra / 集合上的代数 |
| [Monoid](../theories/Algebra/Monoid/Core.v) | `Class` | Set algebra / 集合上的代数 |
| [IsCommMonoid](../theories/Algebra/Monoid/Commutative.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [Semigroup](../theories/Algebra/Semigroup/Core.v) | `Class` | Set algebra / 集合上的代数 |
| [Adj](../theories/Cat/Adjunction.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [ApplicativeAp](../theories/Cat/Applicative/Application.v) | `Class` | Computational structures / 计算结构 |
| [Applicative](../theories/Cat/Applicative/Core.v) | `Class` | Computational structures / 计算结构 |
| [IsApplicativeOps](../theories/Cat/Applicative/Operations.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [ApplicativeOps](../theories/Cat/Applicative/Operations.v) | `Class` | Computational structures / 计算结构 |
| [ArrowOb](../theories/Cat/Arrow/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [ArrowHom](../theories/Cat/Arrow/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [Bicat](../theories/Cat/Bicategory/Core.v) | `Class` | Foundations and basic maps / 基础与基本映射 |
| [IsStrictTwoCat](../theories/Cat/Bicategory/Strict.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [BinoidalCat](../theories/Cat/Binoidal/Core.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [CCC](../theories/Cat/CCC/Core.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [CartCat](../theories/Cat/Cartesian/Core.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [Chain](../theories/Cat/Chain.v) | `Record` | Foundations and basic maps / 基础与基本映射 |
| [HasCoequalizer](../theories/Cat/Coequalizer.v) | `Class` | Chosen construction / 选定构造 |
| [HasColimit](../theories/Cat/Colimit/Core.v) | `Class` | Chosen construction / 选定构造 |
| [HasColimitsOfShape](../theories/Cat/Colimit/Core.v) | `Class` | Chosen construction / 选定构造 |
| [CommaOb](../theories/Cat/Comma/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [CommaHom](../theories/Cat/Comma/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [Comprehension](../theories/Cat/Comprehension.v) | `Record` | Dependent semantics / 依赖语义 |
| [ArrowApply](../theories/Cat/Computational/Arrow/Apply.v) | `Class` | Computational structures / 计算结构 |
| [Arrow](../theories/Cat/Computational/Arrow/Core.v) | `Class` | Computational structures / 计算结构 |
| [HasCoproduct](../theories/Cat/Coproduct/Core.v) | `Class` | Chosen construction / 选定构造 |
| [Cat](../theories/Cat/Core.v) | `Class` | Foundations and basic maps / 基础与基本映射 |
| [Cocone](../theories/Cat/Diagram/Dual.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [GenNat](../theories/Cat/Diagram/Generator.v) | `Class` | Foundations and basic maps / 基础与基本映射 |
| [TwoCocycle](../theories/Cat/Diagram/Cocycle.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [HasEqualizer](../theories/Cat/Equalizer.v) | `Class` | Chosen construction / 选定构造 |
| [HasExponential](../theories/Cat/Exponential/Core.v) | `Class` | Chosen construction / 选定构造 |
| [HasCartLift](../theories/Cat/Fibration.v) | `Class` | Chosen construction / 选定构造 |
| [HasFreeObj](../theories/Cat/FreeObject/Core.v) | `Class` | Chosen construction / 选定构造 |
| [IsCartF](../theories/Cat/Functor/Cartesian.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [CartFct](../theories/Cat/Functor/Cartesian.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [IsCCCF](../theories/Cat/CCC/Functor.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [CCCFct](../theories/Cat/CCC/Functor.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [Fct](../theories/Cat/Functor/Core.v) | `Record` | Foundations and basic maps / 基础与基本映射 |
| [IsGroupoid](../theories/Cat/Groupoid/Core.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [HasRightDivision](../theories/Cat/Groupoid/Division.v) | `Class` | Chosen construction / 选定构造 |
| [HasLimit](../theories/Cat/Limit/Core.v) | `Class` | Chosen construction / 选定构造 |
| [HasLimitsOfShape](../theories/Cat/Limit/Core.v) | `Class` | Chosen construction / 选定构造 |
| [Monad](../theories/Cat/Monad/Core.v) | `Class` | Computational structures / 计算结构 |
| [StrongMonad](../theories/Cat/Monad/Strength.v) | `Class` | Computational structures / 计算结构 |
| [MonoidalCat](../theories/Cat/Monoidal/Core.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [LaxMonoidalFct](../theories/Cat/Monoidal/Functor.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [MonoidObj](../theories/Cat/Monoidal/Monoid.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [PremonoidalCat](../theories/Cat/Premonoidal/Core.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [SymmetricPremonoidalCat](../theories/Cat/Premonoidal/Symmetric.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [FreydCat](../theories/Cat/Computational/Freyd/Core.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [HasStrength](../theories/Cat/Monoidal/Strength.v) | `Class` | Chosen construction / 选定构造 |
| [Mono](../theories/Cat/Morphism.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [Sub](../theories/Cat/Morphism.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [Nat](../theories/Cat/Natural.v) | `Class` | Foundations and basic maps / 基础与基本映射 |
| [HasProduct](../theories/Cat/Product/Core.v) | `Class` | Chosen construction / 选定构造 |
| [HasPullback](../theories/Cat/Pullback.v) | `Class` | Chosen construction / 选定构造 |
| [HasPushout](../theories/Cat/Pushout.v) | `Class` | Chosen construction / 选定构造 |
| [HasFiniteGen](../theories/Cat/Shape/Finite.v) | `Class` | Chosen construction / 选定构造 |
| [HasFiniteHomCover](../theories/Cat/Shape/Finite.v) | `Class` | Chosen construction / 选定构造 |
| [Sieve](../theories/Cat/Sieve.v) | `Class` | Families and matching / 族与匹配 |
| [SliceOb](../theories/Cat/Slice/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [SliceHom](../theories/Cat/Slice/Core.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [HasTerminal](../theories/Cat/Terminal.v) | `Class` | Chosen construction / 选定构造 |
| [HasInitial](../theories/Cat/Terminal.v) | `Class` | Chosen construction / 选定构造 |
| [ContextMap](../theories/DTT/Comprehension.v) | `Record` | Diagram and morphism data / 图式及态射数据 |
| [HasContextRepresentation](../theories/DTT/Context/Representation.v) | `Class` | Chosen construction / 选定构造 |
| [HasContextExtension](../theories/DTT/CwF.v) | `Class` | Chosen construction / 选定构造 |
| [CwF](../theories/DTT/CwF.v) | `Class` | Dependent semantics / 依赖语义 |
| [HasDisplay](../theories/DTT/Display/Core.v) | `Class` | Chosen construction / 选定构造 |
| [IsWellPointed](../theories/Topos/ETCS.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [HasAxiomChoice](../theories/Topos/ETCS.v) | `Class` | Chosen construction / 选定构造 |
| [ETCS](../theories/Topos/ETCS.v) | `Class` | Structured categories and functors / 带结构范畴及函子 |
| [Topos](../theories/Topos/Core.v) | `Class` | Elementary topos structure / 初等拓扑斯结构 |
| [HasNaturalNumbersObj](../theories/Topos/Nat.v) | `Class` | Chosen construction / 选定构造 |
| [HasSubObjClassifier](../theories/Topos/Sub.v) | `Class` | Chosen construction / 选定构造 |
| [Graph](../theories/Graph/Core.v) | `Class` | Foundations and basic maps / 基础与基本映射 |
| [GraphMap](../theories/Graph/Morphism.v) | `Record` | Foundations and basic maps / 基础与基本映射 |
| [FamC](../theories/Instance/Set/Fam/Cat.v) | `Record` | Families and matching / 族与匹配 |
| [FamF](../theories/Instance/Set/Fam/Cat.v) | `Record` | Families and matching / 族与匹配 |
| [FamS](../theories/Instance/Set/Fam/Core.v) | `Record` | Families and matching / 族与匹配 |
| [FamMap](../theories/Instance/Set/Fam/Fixed.v) | `Record` | Families and matching / 族与匹配 |
| [SectionS_resp](../theories/Instance/Set/Fam/Section.v) | `Record` | Families and matching / 族与匹配 |
| [SieveMatching](../theories/Instance/Set/Sieve/Matching.v) | `Record` | Families and matching / 族与匹配 |
| [IsCoskeletal](../theories/Instance/Set/Simplicial/Coskeletal.v) | `Class` | Fixed-data laws and relations / 固定数据上的定律及关系 |
| [HasHornFillers](../theories/Instance/Set/Simplicial/Horn.v) | `Class` | Chosen construction / 选定构造 |
| [HasKanFillers](../theories/Instance/Set/Simplicial/Horn.v) | `Class` | Chosen construction / 选定构造 |
| [Horn2Presentation](../theories/Instance/Set/Simplicial/Vertex/Filling.v) | `Record` | Witness and presentation data / 见证与呈现数据 |
| [HasHorn2Fillers](../theories/Instance/Set/Simplicial/Vertex/Horn2.v) | `Class` | Chosen construction / 选定构造 |
| [VtxFct](../theories/Instance/Set/Vertex/Functor.v) | `Record` | Families and matching / 族与匹配 |
| [is_unique](../theories/Meta.v) | `Record` | Witness and presentation data / 见证与呈现数据 |
| [Clos](../theories/Set/Closure/Core.v) | `Record` | Foundations and basic maps / 基础与基本映射 |
| [SetC](../theories/Set/Core.v) | `Record` | Foundations and basic maps / 基础与基本映射 |
| [LiftT](../theories/Set/Core.v) | `Record` | Witness and presentation data / 见证与呈现数据 |
| [HasFiniteCover](../theories/Set/Finite.v) | `Class` | Chosen construction / 选定构造 |
| [FunS_resp](../theories/Set/Morphism.v) | `Record` | Foundations and basic maps / 基础与基本映射 |

## First hierarchy-normalization slice

## 首批层级规范化

**Historical checkpoint:** the parameterized algebra interfaces and parent
instance registrations described in this section belong to the named earlier
baseline. For the current complete-record migration, use the
[current algebra section](#complete-algebra-hierarchy-current-migration).

**历史检查点：** 本节具参代数接口及父实例注册属于下方注明的旧基线。
当前完整记录迁移见[当前代数章节](#complete-algebra-hierarchy-current-migration)。

The user-approved serial slice starts from `1d29636` on `monoidal-cat-view`.
[AGENTS.md](../AGENTS.md#structural-hierarchies) now records the hierarchy
rules: mathematical structure names, retained `Has*` construction interfaces,
named ambient parameters, computed carrier/category views, one stored
immediate parent, `:>` with separate instance registration when needed,
shared dependent choices and minimal assumptions in general theorems.

用户授权的首批串行实施从 `monoidal-cat-view` 上的 `1d29636` 开始。
[AGENTS.md](../AGENTS.md#structural-hierarchies) 现记录层级规范：数学结构名、
保留的 `Has*` 构造接口、具名环境参数、计算性载体／范畴视图、唯一保存的直接
父结构、`:>` 及按需单独注册实例、共享依赖选择，以及一般定理的最弱前提。

[Group](../theories/Algebra/Group/Core.v) now declares
`GroupM :> Monoid G` directly and exports the same projection as an
inherited instance. The Boolean and endomorphism group constructors use
the named parent field; existing inverse proofs and operations are reused.
In that slice the monoidal category interface became
[MonoidalCat](../theories/Cat/Monoidal/Core.v), retaining the named category,
computed `MonoidalC`, tensor, natural isomorphisms and coherence laws. All
clients and documentation use that name. No compatibility aliases or new
intermediate algebra theories are introduced in this slice.

[Group](../theories/Algebra/Group/Core.v) 现直接声明 `GroupM :> Monoid G`，
并将同一投影导出为继承实例。布尔群与自同态群的构造使用具名父字段，复用
已有逆运算及证明。该批将幺半范畴接口改名为
[MonoidalCat](../theories/Cat/Monoidal/Core.v)，保留具名范畴、计算性
`MonoidalC`、张量、自然同构及相干律；所有客户端和文档同步使用新名。
本批没有添加兼容别名或新的代数中间理论。

The existing `rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0,
Dune 3.23.1) passed `dune build @all @runtest @install`. Thirty-nine new
and 286 existing temporary `Print Assumptions` checks all reported
`Closed under the global context`. The new checks cover both strict
carrier/equality and hom/equality universe orders, inherited monoid
inference, two groups on the same carrier, five transparent Boolean/model
reductions and explicitly enabled models. Existing Arrow, Applicative,
State and cartesian/CCC checks were rerun after the rename.

已有 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、Dune 3.23.1）
通过 `dune build @all @runtest @install`。新增 39 项及已有 286 项临时
`Print Assumptions` 检查均报告 `Closed under the global context`。
新增检查覆盖载体／相等与 Hom／相等的两种严格宇宙次序、继承幺半群推导、
同一载体上的两个群、五项透明布尔／模型归约，以及具体模型的显式启用。
已有 Arrow、Applicative、State 及笛卡尔／CCC 检查均在改名后重跑。

Strict bilingual HTML generated 278 modules per language and checked
links and anchors in 561 pages. The renamed monoidal interface, direct
group parent and adjacent field explanations were checked in both
languages. No permanent tests or shared test aliases were added; existing
interface/universe tests only change references to the renamed interface.
PDF export and updates to `typeprop` remain with the integration session.
ETCS parent sharing is the next bounded slice; Magma/Semigroup extraction
remains a later mathematical task with its own useful clients.

严格双语 HTML 每种语言生成 278 个模块，检查 561 页的链接与锚点；改名后的
幺半接口、直接群父结构及字段旁说明均已核对英中文。没有新增永久测试或
共享测试别名，原有接口／宇宙测试仅更新被改名接口的引用。PDF 导出及
`typeprop` 更新仍由集成会话负责。下一有限批次是 ETCS 父结构共享；
Magma／半群抽取属于后续需要实际客户端的独立数学任务。

## ETCS parent-sharing slice

## ETCS 父结构共享批次

This section records the earlier CCC-parent checkpoint. The later independent
Topos extraction below inserts `Topos` between `ETCS` and `CCC`, while preserving
the same chosen terminal, products and exponentials.

本节记录较早的 CCC 父结构检查点。下文的独立 Topos 抽取在 `ETCS` 与 `CCC`
之间插入 `Topos`，保留同一组选定终对象、积与指数。

The user explicitly approved this serial continuation from `a70a0a2` on
`monoidal-cat-view`, before integrating its prerequisite hierarchy changes.
[ETCS](../theories/Topos/ETCS.v) now stores one `ETCSC :> CCC C` parent
and registers that same projection for instance search. Its only category
view follows `ETCS → CCC → CartCat → Cat`; no direct ancestor bypass
or additional terminal, product or exponential choice is stored.

用户明确批准在前置层级变更集成前，从 `monoidal-cat-view` 上的 `a70a0a2`
串行继续。[ETCS](../theories/Topos/ETCS.v) 现只保存 `ETCSC :> CCC C`
父结构，并将同一投影注册到实例搜索。唯一范畴视图沿
`ETCS → CCC → CartCat → Cat` 转换，不增加直接祖先旁路，也不另存
终对象、积或指数选择。

The subobject classifier, well-pointedness and natural-numbers object are
explicitly indexed by `@hasTerminal C ETCSC`. Initial objects, pullbacks
and Type-valued epi-splitting witnesses remain supplementary fields;
no mathematical hypothesis or explicit model-selection policy changes.
Repository inspection found no concrete ETCS bundle assembly or qualified
use of the removed ETCS projections to migrate. Existing setoid NNO theory
and its explicitly chosen model retain their weaker interfaces.

子对象分类子、良点性及自然数对象均显式以 `@hasTerminal C ETCSC` 为索引。
始对象、拉回及 Type 值满态射分裂见证仍为补充字段，不改变数学前提或显式
模型选择规则。全库调查没有发现需要迁移的完整具体 ETCS 装配或被移除 ETCS
投影的限定引用。已有广集自然数对象理论及其显式选定模型保留较弱接口。

With the existing `rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0,
Dune 3.23.1), the affected ETCS module and full
`dune build @all @runtest @install` passed. Forty-nine temporary
`Print Assumptions` checks reported `Closed under the global context`.
They cover all inherited instances, dependent terminal choices, both
strict hom/equality universe orders, two ETCS structures on one category,
identity structured-functor clients and seven transparent assembly or
operation reductions. Native equality is used only to test definitional
projection reduction; mathematical operation checks use specified hom
equality. No permanent tests or shared test configuration were added.

使用已有 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1），受影响 ETCS 模块及全库 `dune build @all @runtest @install`
均通过。49 项临时 `Print Assumptions` 检查均报告
`Closed under the global context`，覆盖全部继承实例、依赖的终对象选择、
Hom／相等的两种严格宇宙次序、同一范畴上的两个 ETCS 结构、恒等带结构函子
客户端，以及七项透明装配或运算归约。原生相等仅用于测试投影的定义性归约，
数学运算检查使用指定 Hom 相等。没有新增永久测试或共享测试配置。

Strict bilingual HTML generated 278 modules per language and checked links
and anchors in 561 pages; both ETCS interface pages were inspected. Batch
PDF export and integration into `typeprop` remain with the integration
session. Magma/Semigroup extraction remains a separate subsequent task.

严格双语 HTML 每种语言生成 278 个模块，检查 561 页的链接与锚点，并核对
两种语言的 ETCS 接口页面。批次 PDF 导出及 `typeprop` 集成仍由集成会话
负责。Magma／半群抽取仍是单独的后续任务。

## Algebra hierarchy slice

## 代数层级批次

**Historical checkpoint:** the parameterized algebra interfaces and parent
instance registrations described in this section belong to the named earlier
baseline. For the current complete-record migration, use the
[current algebra section](#complete-algebra-hierarchy-current-migration).

**历史检查点：** 本节具参代数接口及父实例注册属于下方注明的旧基线。
当前完整记录迁移见[当前代数章节](#complete-algebra-hierarchy-current-migration)。

The user-approved serial continuation starts from `c3fa956` on
`monoidal-cat-view`. [Magma](../theories/Algebra/Magma/Core.v) now stores
one respectful multiplication and computes `MagmaS :> SetC := M`.
[Semigroup](../theories/Algebra/Semigroup/Core.v) stores
`SemigroupM :> Magma S` and adds associativity.
[Monoid](../theories/Algebra/Monoid/Core.v) stores
`MonoidSG :> Semigroup M` and adds only a two-sided unit; `SG` names the
semigroup parent distinctly from the setoid suffix `S`. Both parent
projections are exported as inherited instances. The group parent stays
`GroupM :> Monoid G`. Multiplication, its preservation proof and the
carrier are never duplicated along this chain.

用户授权的串行后续从 `monoidal-cat-view` 上的 `c3fa956` 开始。
[Magma](../theories/Algebra/Magma/Core.v) 现保存唯一保相等乘法，并计算
`MagmaS :> SetC := M`；[Semigroup](../theories/Algebra/Semigroup/Core.v)
保存 `SemigroupM :> Magma S` 并增加结合律；
[Monoid](../theories/Algebra/Monoid/Core.v) 保存
`MonoidSG :> Semigroup M`，只增加双侧单位元。`SG` 区分半群父结构与广集
后缀 `S`。两个父投影均导出为继承实例；群父结构仍为
`GroupM :> Monoid G`。沿此链不重复保存乘法、保相等证明或载体。

The moved operations are `magma_mul`, `magma_mul_proper`,
`magma_mul_l_resp` and `magma_mul_r_resp`; associativity is now
`semigroup_assoc`. Left/right multiplication maps need only a magma and
respect their fixed factors pointwise. The semigroup layer proves their
composition and left/right commutation laws without assuming a unit or
commutative multiplication. Existing `monoid_scope` clients retain their
multiplication/unit notation; `magma_scope` exposes the same operation
without requiring a monoid. No compatibility aliases retain the former
stronger operation names.

移动后的运算名为 `magma_mul`、`magma_mul_proper`、`magma_mul_l_resp` 与
`magma_mul_r_resp`，结合律现名为 `semigroup_assoc`。左／右乘映射只需要
原群，并逐点保持固定因子的相等。半群层证明它们的复合与左右交换律，不要求
单位元或乘法交换律。已有 `monoid_scope` 客户端保留乘法／单位元记号，
`magma_scope` 则在不要求幺半群的情况下提供同一运算。不为原先带较强结构
名称的运算保留兼容别名。

The Boolean model explicitly builds magma, semigroup, monoid and group in
that order. [EndMagma](../theories/Algebra/Magma/Category.v) and
[EndSemigroup](../theories/Algebra/Semigroup/Category.v) isolate respectful
composition and associativity; `EndMonoid` adds identities to that same
parent. Single-object categories, group laws and chain proofs consume the
weaker operation/law fields. [Set magma multiplication](../theories/Instance/Set/Magma.v)
packages the product-input map with only a named magma; `SetMonoidObj`
reuses it. Concrete structures are still explicitly enabled.

布尔模型按原群、半群、幺半群、群的次序显式构造。
[EndMagma](../theories/Algebra/Magma/Category.v) 与
[EndSemigroup](../theories/Algebra/Semigroup/Category.v) 分别抽出保相等复合
与结合律，`EndMonoid` 为同一父结构增加恒等箭头。单对象范畴、群定律及箭头
链证明使用较弱运算／定律字段。
[广集原群乘法](../theories/Instance/Set/Magma.v) 只需具名原群，即将乘积输入的
映射打包；`SetMonoidObj` 复用此构造。具体结构仍须显式启用。

With the existing `rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0,
Dune 3.23.1), `dune build @all @runtest @install` passed, including the
unchanged concrete computation regressions. All 89 temporary
`Print Assumptions` checks reported `Closed under the global context`.
They cover the entire inheritance chain, both strict carrier/equality
and hom/equality universe orders, multiple choices on one carrier, non-native setoid
equality, transparent Boolean/model/endomorphism computations and
negative checks against implicit concrete choices. Explicit nonassociative
and unit-free examples validate the weaker interfaces.

使用已有 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1），`dune build @all @runtest @install` 通过，包含保持原样的具体
计算回归。89 项临时 `Print Assumptions` 检查均报告
`Closed under the global context`，覆盖完整继承链、载体／相等及 Hom／相等的
两种严格宇宙次序、同一载体的多套选择、非原生广集相等、布尔／模型／自态射透明计算，
以及防止隐式选定具体结构的否定检查。显式非结合与无单位元示例验证较弱接口。

Strict bilingual HTML generated 283 modules per language and checked
links and anchors in 571 pages. Seven new or changed interface/model pages
were inspected in both languages. The inventory covers all 89 declarations
exactly once (62 classes and 27 records); all 29 `Has*` classes are retained.
No permanent tests or existing test files were changed. Batch PDF export
and `typeprop` integration remain with the integration session.

严格双语 HTML 每种语言生成 283 个模块，检查 571 页的链接及锚点，并核对七个
新增或修改接口／模型页面的英中文。清单恰好覆盖全部 89 个声明一次（62 个类
及 27 个记录），保留全部 29 个 `Has*` 类。没有新增永久测试，也没有修改旧测试
文件。批次 PDF 导出及 `typeprop` 集成仍由集成会话负责。

## Binoidal context prerequisite

## 双侧张量上下文前置基础

The current [BinoidalCat](../theories/Cat/Binoidal/Core.v) record stores
`BinoidalCatToCat :> Cat` and one `HasBinoidal` choice. The original
parameterized class used the computed `BinoidalC` view; that presentation
has migrated to the named-category `HasBinoidal C` interface. Both context
law groups now use `IsFct` on the shared tensor's exact maps. Units and
associators remain absent at this weakest layer; `is_central` still retains
Type-valued witnesses separately from choosing the tensor.

当前 [BinoidalCat](../theories/Cat/Binoidal/Core.v) 记录保存
`BinoidalCatToCat :> Cat` 及唯一 `HasBinoidal` 选择。原参数化类使用计算性的
`BinoidalC` 视图；该呈现现迁为具名范畴上的 `HasBinoidal C`。两组上下文
定律现对共享张量的原映射使用 `IsFct`。最弱一层仍不要求单位元或结合子；
`is_central` 继续单独保留 Type 值见证，与选取张量分离。

[MonoidalBinoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Binoidal.v) and
[ArrowBinoidal](../theories/Cat/Computational/Arrow/Binoidal.v) are explicit
adapters at this checkpoint. The monoidal category's primary view then stayed Cat; Arrow's primary
view stays its pure functor. No competing coercions or globally selected
models are introduced. See the [computation audit](./ComputationAudit.md#two-sided-context-and-centrality-prerequisite)
for the relationship to the remaining premonoidal and Freyd layers.

[MonoidalBinoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Binoidal.v) 与
[ArrowBinoidal](../theories/Cat/Computational/Arrow/Binoidal.v) 都是显式
在该阶段均为适配器。幺半范畴当时的主要视图为 Cat，Arrow 的主要视图仍为纯函子；不增加
竞争强制转换或全局选定模型。与后续预幺半及 Freyd 层的关系见
[计算审计](./ComputationAudit.md#two-sided-context-and-centrality-prerequisite)。

At the binoidal delivery, the inventory contained 287 modules, 63 classes
and 27 records,
with every interface listed once. Full-library build/test/install targets,
73 temporary assumption checks and strict bilingual HTML passed; the
[computation audit](./ComputationAudit.md#two-sided-context-and-centrality-prerequisite)
records the exact scope, state-order counterexample and remaining layers.

双侧张量交付时的清单包含 287 个模块、63 个类及 27 个记录，每个接口恰好列出一次。
全库构建／测试／安装目标、73 项临时公理检查及严格双语 HTML 均通过；
[计算审计](./ComputationAudit.md#two-sided-context-and-centrality-prerequisite)
记录确切范围、状态次序反例及剩余层次。


## Premonoidal parent layer

## 预幺半父结构层

[PremonoidalCat](../theories/Cat/Premonoidal/Core.v) is a complete record
with `PremonoidalCatToBinoidalCat :> BinoidalCat` and one indexed
`hasPremonoidal` choice. Use `PremonoidalCatOfBinoidalCat` directly to
assemble it; there is no extra conversion wrapper. The underlying category
and tensor actions are inherited once.

[HasAssociator](../theories/Cat/Premonoidal/Associator.v) chooses a
last-variable natural isomorphism family. `IsAssociator` constrains its
same components by first- and middle-variable naturality, centrality and
pentagon. `PremonoidalAssocLIso` and `PremonoidalAssocMIso` expose these
other natural-isomorphism views with exactly the stored inverses.
[HasUnitors](../theories/Cat/Premonoidal/Unitor.v) independently chooses
one unit and two central natural isomorphisms. `HasPremonoidal C BC`
combines these two packages on the same fixed tensor; `IsPremonoidal`
adds only their triangle compatibility. Inverse centrality and naturality
remain [derived laws](../theories/Cat/Premonoidal/Laws.v), with only the
relevant associator or unitor assumption.

`Reserved Notation` fixes grammar before the fields. Field-local `where`
interpretations permit `Iₚ`, associator and unitor notation in subsequent
fields; Rocq 9.3 does not export those interpretations. Public `Notation`
bindings therefore remain necessary after the declarations. `Iₚ[P]`
selects an explicit unit package; `Iₚ` infers the selected package.

[PremonoidalCat](../theories/Cat/Premonoidal/Core.v) 现为完整记录，保存
`PremonoidalCatToBinoidalCat :> BinoidalCat` 及唯一带索引的
`hasPremonoidal` 选择。直接使用 `PremonoidalCatOfBinoidalCat` 装配，
不增加转换包装；底层范畴与张量作用只继承一次。

[HasAssociator](../theories/Cat/Premonoidal/Associator.v) 选择一族在最后变量上
自然的同构；`IsAssociator` 为同一组分量规定第一、中间变量自然性、中心性及
五边形。`PremonoidalAssocLIso`、`PremonoidalAssocMIso` 保留原逆，给出另两种
自然同构视图。[HasUnitors](../theories/Cat/Premonoidal/Unitor.v) 独立选择唯一
单位及两个中心自然同构。`HasPremonoidal C BC` 在同一固定张量上组合两份选择，
`IsPremonoidal` 只增加三角形相容性。逆的中心性和自然性仍为
[导出定律](../theories/Cat/Premonoidal/Laws.v)，只要求对应的结合子或单位子选择。

`Reserved Notation` 在字段前固定语法，字段局部 `where` 使后续字段可以使用
`Iₚ`、结合子及单位子记号；Rocq 9.3 不导出这些解释，因此声明后的公开
`Notation` 绑定仍然必要。`Iₚ[P]` 显式选定单位选择，`Iₚ` 推断该选择。

[MonoidalPremonoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Premonoidal.v) is an explicit
adapter that reuses the existing tensor, unit, structure maps and inverse
components. At that checkpoint `MonoidalCat` retained its primary category view;
changing it to inherit the new parent and deriving the tensor bifunctor
are a later coordinated migration. No global model choices, symmetry or
interchange for arbitrary effects are added by the premonoidal interface.

[MonoidalPremonoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Premonoidal.v) 是显式适配器，
复用已有张量、单位对象、结构映射及逆分量。该阶段 `MonoidalCat` 仍保留原主要范畴
视图；改为继承新父结构及导出张量双函子属于后续协调迁移。预幺半接口没有
增加全局模型选择、对称性或任意效应的交换律。

The inventory at the premonoidal delivery contained 290 modules, 64 classes and 27 records,
covering all 91 interfaces exactly once and retaining all 29 `Has*`
classes. The [computation audit](./ComputationAudit.md#premonoidal-structure-prerequisite)
records validation and remaining computational-category work.

预幺半交付时的清单包含 290 个模块、64 个类及 27 个记录，全部 91 个接口恰好各列
一次，保留全部 29 个 `Has*` 类。[计算审计](./ComputationAudit.md#premonoidal-structure-prerequisite)
记录验证与剩余计算范畴工作。


## Monoidal inheritance and derived tensor

## 幺半继承与导出张量

[MonoidalCat](../theories/Cat/Monoidal/Core.v) remains parameterized in
this bounded migration. It stores one `monoidal_hasBinoidal` and the
indexed `MonoidalToHasPremonoidal` extension, plus interchange. The computed
`MonoidalToCat` view is the supplied category. Tensor maps, the bifunctor,
joint naturality and ordinary monoidal coherence remain derived.

[MonoidalCat](../theories/Cat/Monoidal/Core.v) 在本次有界迁移中仍为参数化接口，
保存一份 `monoidal_hasBinoidal`、以它为索引的 `MonoidalToHasPremonoidal`
扩展及交换律。计算性的 `MonoidalToCat` 视图就是给定范畴。张量映射、双函子、
联合自然性及通常幺半相干性仍由此导出。

[BifunctorMonoidal](../theories/Cat/Monoidal/Bifunctor.v) preserves the
convenient assembly from a supplied bifunctor and natural structural
isomorphisms. Cartesian and bicategory endomorphism models use it instead
of duplicating the parent laws. Its reconstructed tensor is naturally
isomorphic to the supplied functor with identity components; its arrow
map is compared by specified hom equality. The former explicit monoidal
to binoidal/premonoidal adapters are replaced by the actual parent chain.

[BifunctorMonoidal](../theories/Cat/Monoidal/Bifunctor.v) 保留由给定双函子
及自然结构同构装配模型的便利方式。笛卡尔与双范畴自同态模型复用它，不重复
证明父层定律。重建张量与给定函子通过恒等分量自然同构，态射映射使用指定
Hom 相等比较。先前显式的幺半到双侧张量／预幺半适配器已由实际父链替代。

[Cartesian lifting](../theories/Cat/Monoidal/CartesianLifting.v) retains
ordinary product notation in weaker lax clients. Applicative, strength,
Monad and Arrow specializations use the product/horizontal-composition
comparison laws. Monad–monoid functors retain the same underlying natural
transformations and transport their preservation witnesses explicitly.
This migration changes no `Has*` naming or computational Arrow interchange
assumptions. The [computation audit](./ComputationAudit.md#monoidal-parent-migration)
records validation and the remaining Arrow/Freyd work.

[笛卡尔提升](../theories/Cat/Monoidal/CartesianLifting.v) 让较弱 lax 客户端
继续使用通常积记号。Applicative、强度、Monad 及 Arrow 特化使用积／水平复合
比较定律。Monad–幺半群函子保留同一底层自然变换，显式运输保持性见证。
本迁移没有修改 `Has*` 命名或计算 Arrow 的效应交换前提。
[计算审计](./ComputationAudit.md#monoidal-parent-migration) 记录验证与剩余
Arrow／Freyd 工作。

At the monoidal migration, the inventory covered 291 modules and all 91 interfaces once
(64 classes, 27 records), retaining all 29 `Has*` classes. Full-library
build/test/install, 212 temporary assumption checks and strict bilingual
HTML (587 checked pages) passed. No old tests or shared test configuration
were modified; batch PDF export remains with integration.

幺半迁移时的清单覆盖 291 个模块，全部 91 个接口各一次（64 个类、27 个记录），
保留全部 29 个 `Has*` 类。全库构建／测试／安装、212 项临时公理检查及严格
双语 HTML（检查 587 页）通过。未修改旧测试或共享测试配置；批次 PDF 导出
仍由集成方负责。

## Computational Arrow inherits the same context parent

## 计算 Arrow 继承同一上下文父结构

[ArrowPremonoidal](../theories/Cat/Computational/Arrow/Premonoidal.v)
adds an explicit premonoidal construction for cartesian computational
Arrows. Its single parent is the existing `ArrowBinoidal A`; coercion and
inherited instance search follow `PremonoidalB` and `BinoidalC` to the
same computation category. All tensor/context choices are inherited once.
Pure images of the selected value associator/unitors provide the
structural isomorphisms, retaining their computational inverses. General
premonoidal laws provide inverse centrality and naturality.

[ArrowPremonoidal](../theories/Cat/Computational/Arrow/Premonoidal.v)
为笛卡尔计算 Arrow 增加显式预幺半构造。唯一父结构为已有
`ArrowBinoidal A`；强制转换及继承实例搜索沿 `PremonoidalB`、`BinoidalC`
到达同一计算范畴。全部张量／上下文选择仅继承一次。选定值结合子／单位子
的纯像提供结构同构，保留其可计算逆。一般预幺半定律给出逆中心性及自然性。

This added one theory module and no class/record interface. At that stage
the inventory covered 292 modules and all 91 interfaces once (64 classes,
27 records), retaining all 29 `Has*` classes. No model structure is
globally selected, and no effect interchange is added. The
[computation audit](./ComputationAudit.md#computational-arrow-premonoidal-structure)
records the proof reuse, validation and remaining symmetric/Freyd work.

该批增加一个理论模块，没有增加类／记录接口。该阶段清单覆盖 292 个模块，
全部 91 个接口各一次（64 个类、27 个记录），保留全部 29 个 `Has*` 类。
没有全局选定模型结构，也没有增加效应交换律。
[计算审计](./ComputationAudit.md#computational-arrow-premonoidal-structure)
记录证明复用、验证及剩余对称／Freyd 工作。

## Symmetric computations and the Freyd inclusion

## 对称计算与 Freyd 嵌入

[SymmetricPremonoidalCat](../theories/Cat/Premonoidal/Symmetric.v)
retains one `symmetric_hasBinoidal` choice and its indexed
`SymmetricPremonoidalToHasPremonoidal` extension, both available to
instance search. It stores central exchange, involution, one-variable
naturality, hexagon and unit compatibility. The inverse is the opposite
exchange; other-variable naturality and recovery of right action are
derived. [Cartesian values](../theories/Cat/Premonoidal/Cartesian.v) and
[computational Arrows](../theories/Cat/Computational/Arrow/Symmetric.v)
explicitly select this extension of their existing parent.

[SymmetricPremonoidalCat](../theories/Cat/Premonoidal/Symmetric.v)
保存唯一 `symmetric_hasBinoidal` 选择及以它为索引的
`SymmetricPremonoidalToHasPremonoidal` 扩展，两者均供实例搜索使用。它保存中心交换、对合、单变量自然性、六边形及单位相容性。逆为反序
交换；另一变量自然性及右作用的恢复均由此导出。
[笛卡尔值](../theories/Cat/Premonoidal/Cartesian.v)及
[计算 Arrow](../theories/Cat/Computational/Arrow/Symmetric.v)显式选定
对其已有父层的这一扩展。

[FreydCat C K](../theories/Cat/Computational/Freyd/Core.v) has the pure
ambient functor `FreydF :> Fct C K` as its unique primary view.
Its computed `FreydComputations` reindexes ambient hom-sets by value
objects, rather than choosing a second category. Supplementary named
`hasValueTerminal`, `hasValueProduct` and `hasSymmetricPremonoidal`
fields select the value and
computation structures. `FreydPureF` uses the shared
[InducedF](../theories/Cat/Induced.v) and has identity object map.
Tensor/unit object equalities determine every boundary transport in its
context, associator, unitor and symmetry preservation laws. All arrow
laws use specified hom equality, with no equality of functions or records.

[FreydCat C K](../theories/Cat/Computational/Freyd/Core.v) 以纯环境函子
`FreydF :> Fct C K` 为唯一主要视图。计算性 `FreydComputations`
按值对象重索引环境 Hom 广集，不额外选取范畴。辅助具名字段 `hasValueTerminal`、`hasValueProduct`
及 `hasSymmetricPremonoidal` 选定值与计算结构。`FreydPureF` 使用共享
[InducedF](../theories/Cat/Induced.v)，对象映射为恒等。张量／单位对象的
相等确定上下文、结合子、单位子及对称性保持律中的全部边界运输。所有态射
定律均使用指定 Hom 相等，不要求函数或记录相等。

[ArrowFreyd](../theories/Cat/Computational/Arrow/Freyd.v) retains the
same pure functor, value choices and symmetric computation parent.
All its object boundaries are reflexive and compute to identities.
At the symmetric/Freyd delivery, the inventory contained 297 modules and
93 interfaces (66 classes,
27 records), with all 29 `Has*` classes retained. The
[computation audit](./ComputationAudit.md#symmetric-contexts-and-freyd-foundation)
records validation and the remaining reverse translation/round trips.

[ArrowFreyd](../theories/Cat/Computational/Arrow/Freyd.v) 保留同一纯函子、
值选择及对称计算父层。其所有对象边界均为自反相等，计算为恒等。该阶段清单
包含 297 个模块、93 个接口（66 个类、27 个记录），保留全部 29 个 `Has*`
类。[计算审计](./ComputationAudit.md#symmetric-contexts-and-freyd-foundation)
记录验证及剩余逆向翻译／往返定律。

## Freyd reconstruction and round-trip comparisons

## Freyd 重建及往返比较

[TransportF](../theories/Cat/Functor/Transport.v) changes a functor's object
representatives along chosen isomorphisms, with a transparent natural
isomorphism to the original functor. Its shared boundary-naturality lemma
requires only a natural incoming boundary and an invertible outgoing one.
[Tensor-boundary laws](../theories/Cat/Binoidal/Transport.v) reuse the
existing context functors and centrality of transported identities.

[TransportF](../theories/Cat/Functor/Transport.v) 沿选定同构改变函子的对象
代表，并以透明自然同构与原函子比较。共享的边界自然性引理只要求入边界
自然、出边界可逆。[张量边界定律](../theories/Cat/Binoidal/Transport.v)
复用已有上下文函子及运输恒等的中心性。

[FreydArrow](../theories/Cat/Computational/Freyd/Arrow.v) reconstructs a
computational Arrow from the existing Freyd pure inclusion and transported
context action. It retains the selected value products and all supplied
tensor/unit equality witnesses. Naturality across boundary transformations
derives unit and associativity laws from the general premonoidal theory.

[FreydArrow](../theories/Cat/Computational/Freyd/Arrow.v) 从已有 Freyd
纯嵌入及运输后的上下文作用重建计算 Arrow，保留选定值积及给定的全部张量／
单位相等见证。边界自然变换上的自然性从一般预幺半理论导出单位及结合律。

[Round-trip comparisons](../theories/Cat/Computational/Freyd/RoundTrip.v)
recover Arrow pure maps and context in specified hom equality, and compare
the pure functors by natural isomorphism. The Freyd side supplies an actual
categorical equivalence of value-indexed computation categories, a natural
isomorphism of pure inclusions, and boundary comparisons for both actions,
both unitors, associator and symmetry. This comparison level concerns
these supplied structures and computations; it does not assert a
2-category equivalence or a characterization of an Arrow syntax.

[往返比较](../theories/Cat/Computational/Freyd/RoundTrip.v) 在指定 Hom
相等下恢复 Arrow 的纯映射与上下文，以自然同构比较纯函子。Freyd 方向给出
值索引计算范畴的实际范畴等价、纯嵌入的自然同构，以及两个作用、两个单位子、
结合子和对称性的边界比较。此比较层级涉及给定结构及计算，不主张二范畴
等价或 Arrow 语法刻画。

This slice added five modules without new classes or records. At that
delivery, the inventory covered 302 modules and all 93 interfaces once (66 classes,
27 records), retaining all 29 `Has*` classes. The
[computation audit](./ComputationAudit.md#freyd-reconstruction-and-round-trips)
records validation and the remaining computation-theory work.

该批增加五个模块，没有增加类或记录。该阶段清单覆盖 302 个模块、全部 93 个
接口各一次（66 个类、27 个记录），保留全部 29 个 `Has*` 类。
[计算审计](./ComputationAudit.md#freyd-reconstruction-and-round-trips)
记录验证及后续计算理论工作。

## Static computational Arrow

## 静态计算 Arrow

[StaticArrow](../theories/Cat/Computational/Arrow/Static.v) builds a
computational Arrow from an Applicative on chosen finite products and
exponentials. Its [StaticCat](../theories/Cat/Computational/Arrow/Static.v)
hom-sets are global effectful internal functions, using the base Hom
setoids unchanged. Pure inclusion names an ordinary map; context extension
maps the ordinary internal context operation. The construction requires
neither a monad nor a separately selected functor strength.

[StaticArrow](../theories/Cat/Computational/Arrow/Static.v) 从选定有限积与
指数上的 Applicative 构造计算 Arrow。
[StaticCat](../theories/Cat/Computational/Arrow/Static.v) 的 Hom 广集是
全局带效应内部函数，直接使用基底 Hom 广集。纯嵌入命名通常映射，上下文扩展
映射通常内部上下文运算。构造不要求 Monad 或另选的函子强度。

[Internal context diagrams](../theories/Cat/Exponential/Context.v) and
[shared-context lifting](../theories/Cat/Applicative/Lifting.v) are reusable
at their respective theory layers. Internal sequencing reorders the inputs
of the existing internal composition, so computation composition combines
the input computation's effects before the following computation's effects.
No interchange of two effects is assumed. Unit and associativity proofs
reuse the general lax laws, with no model-specific coherence proofs.

[内部上下文图](../theories/Cat/Exponential/Context.v)及
[共同上下文提升](../theories/Cat/Applicative/Lifting.v)分别属于可复用理论。
内部顺序组合调整已有内部复合的输入排列，使计算复合先组合输入计算的效应，
再组合后续计算的效应。不假设两个效应交换。单位与结合证明复用一般 lax
定律，没有增加模型专用的相干证明。

[Reader](../theories/Instance/Set/Reader.v) now keeps its environment and
ambient levels separate throughout its pure, tensorator, lax and Applicative
packaging. This repairs a signature restriction exposed by the static
client without changing its operations. Explicit closed-setoid instances
retain their existing universe closure bounds; abstract static Arrows keep
independent object, hom and hom-equality levels. No default model is enabled.

[Reader](../theories/Instance/Set/Reader.v) 现在在纯值、tensorator、lax 及
Applicative 包装中完整保留独立的环境与所在层级，修复静态客户端暴露的签名
限制，不改变运算。显式闭广集实例保留既有宇宙闭包限制；抽象静态 Arrow
保留独立的对象、Hom 及 Hom 相等层级。没有启用默认模型。

This slice added three modules without changing the 93 class/record
interfaces or the 29 `Has*` classes at that delivery, which covered 305
modules. The [computation audit](./ComputationAudit.md#static-arrow-construction)
records validation and the remaining syntax/representation comparisons.

本批增加三个模块，在该次交付时不改变 93 个类／记录接口及 29 个 `Has*` 类，
覆盖 305 个模块。[计算审计](./ComputationAudit.md#static-arrow-construction)
记录验证及剩余语法／表示比较。


## Static values and Applicative operations

## 静态值与 Applicative 运算

[StaticValues](../theories/Cat/Computational/Arrow/StaticValues.v) compares
terminal-input static computations with global Applicative values. Evaluation
and abstraction are transparent, respect the original hom equality, and are
mutually inverse in every external context. They commute with substitution.
The construction reuses the selected exponential-unit isomorphism; it adds
no chosen structures or class registrations.

[StaticValues](../theories/Cat/Computational/Arrow/StaticValues.v) 比较终输入
静态计算与全局 Applicative 值。求值和抽象透明、保持原有 Hom 相等，并在每个
外部上下文中互逆，也与替换交换。构造复用选定的指数单位同构，不增加选定
结构或类注册。

Pure values, ordinary result maps and ordered application are preserved and
reflected. Every binary Applicative lifting has a sequential static
representation: abstract the left value, then compose with the effectful
function selected by the right value. General evaluation diagrams live in
[exponential context theory](../theories/Cat/Exponential/Context.v), before
any effectful lifting. The binary diagram needs only products and
exponentials; terminal evaluation additionally needs the selected terminal.

纯值、通常结果映射和有序应用得到保持与反映。每个二元 Applicative 提升均有
顺序的静态表示：抽象左值，再与右值选出的带效应函数复合。一般求值图位于
[指数上下文理论](../theories/Cat/Exponential/Context.v)，先于任何效应提升。
二元图只要求积与指数，终求值另需选定终对象。

These results compare actual arrows and their specified equality. They do
not infer an arbitrary functor or its law records from global elements, or
establish a typed syntax equivalence. No well-pointedness, strength, monad
or effect commutativity is required. At that delivery, direct comparison with derived
Arrow fanout was still pending; it is completed below. The inventory then
covered 330 modules and the same 97 interfaces. Syntax is deferred until
the categorical semantics and its correspondences are established.

这些结果比较实际态射及其指定相等，不从全局元素推断任意函子或其定律记录，
也尚未建立带类型语法等价。不要求良点性、强度、Monad 或效应交换性。该次交付时，与导出
的 Arrow fanout 直接比较仍待完成，现已由下述批次完成。当时清单覆盖 330 个
模块及原有 97 个接口。语法层等范畴语义及对应关系建立后再讨论。


## Static Arrow fanout and binary lifting

## 静态 Arrow fanout 与二元提升

[StaticCartesian](../theories/Cat/Computational/Arrow/StaticCartesian.v)
compares the actual derived `first`, ordered `split` and `fanout` operations
with Applicative lifting. The internal function pairing is the existing
inverse product-exponential comparison, not another selected product or
independently proved universal property. Ordinary
[context diagrams](../theories/Cat/Exponential/Context.v) establish the
comparison before introducing effects. Right context is derived by pure
exchange from the original left context; no second action is selected.

[StaticCartesian](../theories/Cat/Computational/Arrow/StaticCartesian.v)
比较实际导出的 `first`、有序 `split` 及 `fanout` 与 Applicative 提升。内部
函数配对复用已有积指数比较的逆，不另选积或重新证明泛性质。通常
[上下文图](../theories/Cat/Exponential/Context.v)先于效应建立比较；右上下文
由原左上下文经纯交换导出，不另选第二个作用。

At terminal input, evaluation preserves ordered Applicative pairing and
pure postcomposition recovers every binary lifting. The inverse value map
reflects these same operations as actual Arrow fanout followed by the pure
binary operation. Hom equality and left-before-right effects are retained;
no interchange or monad is assumed. Generic diagrams need only products
and exponentials, with a terminal object added for unit evaluation.

在终输入处，求值保持有序 Applicative 配对，纯后合成恢复每个二元提升。
逆值映射将这些运算反映为实际 Arrow fanout 及其后的纯二元运算。保留 Hom
相等及从左到右的效应，不假设交换律或 Monad。一般图只要求积与指数，在
单位求值处另加终对象。

The current inventory covers 351 modules and 98 interfaces
(69 classes, 29 records), including all 29 `Has*` classes. Work continues
with categorical semantic structures and their correspondence conditions;
typed syntax is deferred until that semantic development is established.
The [audit](./ComputationAudit.md#static-cartesian-operation-comparisons)
records validation and the exact delivered comparison level.

当前清单覆盖 351 个模块及 98 个接口（69 个类、29 个记录），包括全部
29 个 `Has*` 类。后续继续范畴语义结构及其对应条件，待语义发展建立后再
讨论带类型语法。[审计](./ComputationAudit.md#static-cartesian-operation-comparisons)
记录验证及本次交付的精确比较层次。


## Terminal-input computation functors

## 终输入计算函子

[Global](../theories/Cat/Computational/Arrow/Global.v) reuses the covariant
Hom functor and pure inclusion to send a value object to its terminal-input
computation setoid. Ordered fanout supplies a lax monoidal structure into
the category of setoids. Its proof reuses
[general pairing laws](../theories/Cat/Computational/Arrow/Pairing.v), with
no Monad, exponentials or effect interchange. Value and computation
categories keep separate hom/equality sizes. This is generally a setoid-valued
functor; an endofunctor on the value category requires a suitable model or
representation condition.

[Global](../theories/Cat/Computational/Arrow/Global.v) 复用协变 Hom 函子与纯
嵌入，将值对象送到其终输入计算广集。有序 fanout 提供进入广集范畴的 lax
幺半结构，证明复用[一般配对律](../theories/Cat/Computational/Arrow/Pairing.v)，
不要求 Monad、指数或效应交换。值与计算范畴保留各自独立的 Hom／相等大小。
该构造一般为广集值函子；要得到值范畴上的自函子，需要适当模型或表示条件。

[Constant maps](../theories/Set/Constant.v) provide the independent
setoid-level primitive needed by the subsequent pure-value construction,
with target equality and no category imports. No interfaces or chosen
instances are added. The declaration inventory remains 97 interfaces.

[常值映射](../theories/Set/Constant.v)提供后续纯值构造所需的独立广集层原语，
使用目标相等，不导入范畴。没有新增接口或选定实例，声明清单仍为 97 个接口。


## Arrow values and static Applicative recovery

## Arrow 值与静态 Applicative 回收

[The setoid adapter](../theories/Instance/Set/Arrow.v) turns terminal-input
computations into `ArrowA`. Its computation hom carrier and equality levels
match the ambient setoid levels, while the computation-object level remains
independent. Pure values are pure constant arrows; the lax parent is the
same global-computation construction above. Binary lifting is actual
ordered fanout followed by a pure binary operation. Neither strength,
Monad nor exponentials are needed by this adapter, and imports select no
chosen model structure.

[广集适配器](../theories/Instance/Set/Arrow.v)将终输入计算组成 `ArrowA`。
计算 Hom 的载体及相等层级对应所在广集层级，计算对象层级仍独立。纯值是纯
常值箭头，lax 父结构恰为上述全局计算构造。二元提升为实际有序 fanout 后接
纯二元运算。此适配器不要求强度、Monad 或指数，导入也不选取模型结构。

[Static recovery](../theories/Instance/Set/StaticArrow.v) specializes to the
existing closed setoid model at a common carrier/equality level. Applying
the adapter to an Applicative's static Arrow yields a functor naturally
isomorphic to the original Applicative. The transparent comparison composes
two existing exponential-unit isomorphisms: evaluating the global element,
then evaluating the internal function through the original functor.
Both directions preserve pure values, pairing and every binary lifting.
No equality of functor records or proof fields is used.

[静态回收](../theories/Instance/Set/StaticArrow.v)特化到载体／相等使用同一
层级的已有闭广集模型。对 Applicative 的静态 Arrow 使用适配器，所得函子
与原 Applicative 自然同构。透明比较复合两个已有指数单位同构：求值全局
元素，再通过原函子求值内部函数。双向保持纯值、配对及每个二元提升，不要求
函子记录或证明字段相等。

This delivers the Applicative-to-static-Arrow-to-Applicative semantic round
trip on that model. It does not reconstruct every Arrow from its global
values; precise static/dynamic reconstruction conditions remain separate
semantic work. The inventory now covers 351 modules and all 98 interfaces.
Syntax remains deferred until the semantic development is established.

本批给出该模型上的 Applicative 经静态 Arrow 再回到 Applicative 的语义
往返，不从全局值重建任意 Arrow。精确的静态／动态重建条件仍是独立后续
语义工作。清单现覆盖 351 个模块及 98 个接口。语法继续等语义
建立后再讨论。


## Static interpretation into the original Arrow

## 解释静态计算回原 Arrow

[Global contexts](../theories/Cat/Computational/Arrow/GlobalContext.v)
attach a terminal-input computation to an ordinary input. Pure
substitution, ordered pairing and nested context require only selected
finite products. [Static evaluation](../theories/Cat/Computational/Arrow/StaticEvaluation.v)
adds selected exponentials and interprets a global internal function by
pure evaluation after that attachment. Pure names, ordered composition
and left context are preserved in the computation category's Hom equality.
The value/computation category sizes remain independent; no Applicative
endofunctor representation is needed by this general theory.

[全局上下文](../theories/Cat/Computational/Arrow/GlobalContext.v)将终输入
计算附在普通输入旁；纯替换、有序配对及嵌套上下文只要求选定有限积。
[静态求值](../theories/Cat/Computational/Arrow/StaticEvaluation.v)再加入
选定指数，以附加后的纯求值解释全局内部函数。在计算范畴的 Hom 相等下保持
纯命名、有序复合及左上下文。值／计算范畴大小仍独立，一般理论不要求
Applicative 自函子表示。

[The setoid interpreter](../theories/Instance/Set/StaticInterpret.v)
provides `StaticInterpretF` from the static category of an Arrow's
extracted Applicative into its original computation category. The existing
closed setoid model uses a common carrier/equality level, matched by the
computation hom-setoids, with an independent computation-object level.
The object map is the original Arrow's pure object map. Identity-component
`StaticInterpretPureIso` compares the composite static pure inclusion
with the original pure functor. This slice delivers interpretation and
operation preservation; the subsequent reconstruction results are described
below. No model choice is enabled by import. At delivery, the inventory
contained 97 interfaces over 344 modules; syntax stays deferred.

[广集解释器](../theories/Instance/Set/StaticInterpret.v)提供
`StaticInterpretF`：从 Arrow 抽取的 Applicative 的静态范畴，进入原计算
范畴。已有闭广集模型使用共用的载体／相等层级，计算 Hom 广集与之匹配，计算
对象层级仍独立。对象映射是原 Arrow 的纯对象映射。恒等分量的
`StaticInterpretPureIso` 将复合后的静态纯嵌入与原纯函子自然比较。本批是
保持运算的解释；满性、忠实性、逆向重建及 ArrowApply 的后续进度见下节。
导入不启用模型选择。本切片交付时清单为 344 个模块、97 个接口；语法继续暂缓。


## Static representations and inverse reconstruction

## 静态表示与逆向重建

[StaticRepresentation](../theories/Cat/Computational/Arrow/StaticRepresentation.v)
states `is_static_arrow` as invertibility of the specified global-function
evaluation maps. It is equivalent to supplied Type-valued unique fibers,
using native computation equality. The transparent inverse preserves pure
names, ordered composition and the same context action. Every
Applicative-generated static Arrow satisfies this criterion over any base
with the selected finite products and exponentials. The proof reuses the
existing terminal-input value/function inverse, without well-pointedness.

[StaticRepresentation](../theories/Cat/Computational/Arrow/StaticRepresentation.v)
以指定全局函数求值映射的可逆性定义 `is_static_arrow`，并以原生计算相等
证明它等价于给定 Type 值唯一纤维。透明逆保持纯命名、有序复合及同一上下文
作用。任意具有选定有限积与指数的基底上，由 Applicative 生成的静态 Arrow
均满足该条件；证明复用已有终输入值／函数逆，不要求良点性。

[The setoid reconstruction](../theories/Instance/Set/StaticRepresentation.v)
identifies the criterion with full faithfulness of the existing interpreter
at the closed model's common carrier/equality bound. `StaticRepresentationEq`
gives an actual category equivalence with the original Arrow's value-indexed
computation category, using the general
[fully faithful inverse](../theories/Cat/Functor/FullyFaithful.v).
The two inverse functors preserve pure arrows and context, with composition
inherited from their functor laws. This conclusion concerns the objects used
by the Arrow; it does not select representatives for other ambient objects.
The general theory retains independent category hom sizes, and the setoid
client retains an independent computation-object size.

[广集重建](../theories/Instance/Set/StaticRepresentation.v)在闭模型的共同
载体／相等界下，将该条件与已有解释函子的完全忠实性联系起来。
`StaticRepresentationEq` 复用[一般完全忠实逆](../theories/Cat/Functor/FullyFaithful.v)，
给出与原 Arrow 值索引计算范畴的实际范畴等价。两个互逆函子保持纯箭头与
上下文，复合保持性由函子定律给出。结论涉及 Arrow 使用的对象，不为其他
环境对象选取代表。一般理论保留独立范畴 Hom 大小，广集客户端保留独立计算
对象大小。

At static reconstruction delivery the inventory covered 347 modules and
97 interfaces (68 classes, 29 records), including all 29 `Has*` classes.
The following slice adds ArrowApply and its Kleisli instance; the reverse
Monad construction and typed syntax remain deferred. The
[audit](./ComputationAudit.md#static-representation-and-inverse-reconstruction)
records exact hypotheses, temporary computations and validation.

静态重建交付时清单为 347 个模块、97 个接口（68 个类、29 个记录），包括全部
29 个 `Has*` 类。下个切片增加 ArrowApply 及其 Kleisli 实例，反向 Monad
构造和带类型语法继续暂缓。[审计](./ComputationAudit.md#static-representation-and-inverse-reconstruction)
记录精确假设、临时计算及验证。


## Dynamic Arrow application and Kleisli models

## 动态 Arrow 应用与 Kleisli 模型

[ArrowApply](../theories/Cat/Computational/Arrow/Apply.v) stores exactly one
`ArrowApplyA :> Arrow` parent. Its existing pure-functor and object-map views
remain available through that chain; arrow maps still use `fmap`. The new
operation accepts a native computation Hom value and an ordinary input,
then runs that computation. Pure pairing, input computation substitution
and output computation postcomposition are its three laws, matching
[Control.Arrow](https://downloads.haskell.org/ghc/9.6.7.20250131/docs/libraries/base-4.18.3.0/Control-Arrow.html)
after expanding `first` on pure arrows. The fixed-computation application
law follows from these fields and ordinary Arrow equations in native Hom
equality; it does not assume that pointwise tests determine computations.

[ArrowApply](../theories/Cat/Computational/Arrow/Apply.v)仅保存一个
`ArrowApplyA :> Arrow` 父结构，沿该链恢复已有纯函子及对象映射视图，箭头
映射仍使用 `fmap`。新增运算接受原生计算 Hom 值与通常输入，并运行该计算。
三条定律分别表达纯配对、输入计算代入及输出计算后合成，对应
[Control.Arrow](https://downloads.haskell.org/ghc/9.6.7.20250131/docs/libraries/base-4.18.3.0/Control-Arrow.html)
在纯箭头上展开 `first` 后的定律。固定计算应用律由这些字段与通常 Arrow
方程在原生 Hom 相等下导出，不假设逐点测试决定计算相等。

This interface uses the setoid base, matching computation hom carrier and
equality levels to their ambient setoid levels, with an independent
computation-object level. It requires no selected exponentials. It does
not provide an internal representation of computation homs in every
abstract CCC. [Pointwise strength](../theories/Instance/Set/Strength.v)
first proves that any supplied setoid strength pairs a fixed context with
the functor result, so its components are unique in specified equality.
Its carrier/equality levels remain independent.

该接口使用广集基底，将计算 Hom 载体及相等层级对应于所在广集层级，计算
对象层级独立，不要求选定指数。它不提供任意抽象 CCC 中计算 Hom 的内部
表示。[逐点强度](../theories/Instance/Set/Strength.v)先证明任意给定广集
强度将固定上下文配到函子结果旁边，因此其分量在指定相等下唯一；该结论
保留独立载体／相等层级。

[KleisliArrowApply](../theories/Instance/Set/KleisliApply.v) extends the
exact existing Kleisli Arrow of a supplied strong Monad. Applying a
Kleisli computation is ordinary respectful function evaluation. The
input-substitution law reuses the general pointwise strength result and
Kleisli extension; no model-specific law proof is copied. Native
Kleisli Hom-as-input uses the stated common carrier/equality bound.
[StateArrowApply](../theories/Instance/Set/State.v) explicitly selects this
construction for the existing state Monad, retaining separate state
carrier/equality levels below that bound. Imports select no model instance.

[KleisliArrowApply](../theories/Instance/Set/KleisliApply.v)扩充所给强 Monad
恰好已有的 Kleisli Arrow，应用 Kleisli 计算就是通常保相等函数求值。输入
代入律复用一般逐点强度及 Kleisli 扩张，不重复具体模型定律证明。将原生
Kleisli Hom 作为输入使用已声明的共同载体／相等界。
[StateArrowApply](../theories/Instance/Set/State.v)为已有状态 Monad 显式选择
此构造，状态载体／相等层级仍在该界下独立。导入不选取模型实例。

The inventory now covers 351 modules and all 98 interfaces (69 classes,
29 records), including the same 29 `Has*` classes. This delivers the
strong-Monad-to-ArrowApply direction on the stated base. Constructing a
Monad from ArrowApply and proving the desired reverse comparisons remain
subsequent semantic work; syntax remains deferred. The
[audit](./ComputationAudit.md#lawful-arrowapply-and-kleisli-dynamic-application)
records validation and exact boundaries.

清单现覆盖 351 个模块、全部 98 个接口（69 个类、29 个记录），保留原有 29 个
`Has*` 类。本批交付上述基底上的强 Monad 到 ArrowApply 方向；从 ArrowApply
构造 Monad 及所需反向比较仍属后续语义工作，语法继续暂缓。
[审计](./ComputationAudit.md#lawful-arrowapply-and-kleisli-dynamic-application)
记录验证及精确边界。


## Dynamic Arrow adjunction and Monad recovery

## 动态 Arrow 伴随及 Monad 回收

[Dynamic naming and evaluation](../theories/Cat/Computational/Arrow/Dynamic.v)
provide inverse respectful Hom maps. Naming uses only the ordinary Arrow;
its inverse uses ArrowApply. The
[dynamic adjunction](../theories/Cat/Computational/Arrow/Monad.v) reuses
`AdjFromHom`, with the pure indexed inclusion on the left and the
covariant Hom functor at terminal input on the right. `ArrowMonad` then
reuses `AdjMonad`, retaining a natural isomorphism to the existing
`ArrowGlobalF`. The unit is the existing pure global value; multiplication
runs the returned computation; extension runs a selected continuation.
The computation-object, native Hom carrier and equality levels remain
independent. No exponential choice or new interface class is introduced.

[动态命名与求值](../theories/Cat/Computational/Arrow/Dynamic.v)提供互逆的
保相等 Hom 映射，命名只使用通常 Arrow，逆向使用 ArrowApply。
[动态伴随](../theories/Cat/Computational/Arrow/Monad.v)复用
`AdjFromHom`，左侧是索引后的纯包含，右侧是终端输入处的协变 Hom
函子。`ArrowMonad` 再复用 `AdjMonad`，保留到已有 `ArrowGlobalF`
的自然同构。单位是已有纯全局值，乘法运行返回的计算，扩张运行选出的续延。
计算对象、原生 Hom 载体及相等层级保持独立，不选择指数，也不增加接口类。

[Kleisli recovery](../theories/Instance/Set/KleisliRecovery.v) compares
this Monad for `KleisliArrowApply M` with the original supplied strong
Monad. Evaluation at the singleton and constant computation are transparent
inverse natural transformations. Both preserve unit and multiplication,
so `KleisliRecoveryIso` is an isomorphism in the existing `MonadCat`.
Recovery also preserves Kleisli extension and effect order. This client
retains the Kleisli model's stated common native carrier/equality bound;
state carrier and equality may still occupy distinct smaller levels.
An arbitrary ArrowApply round trip, compatibility with all additional
computational structures and typed syntax remain subsequent work.

[Kleisli 回收](../theories/Instance/Set/KleisliRecovery.v)比较
`KleisliArrowApply M` 对应的 Monad 与原有强 Monad。在单元素处求值与常值
计算构成透明互逆自然变换；双向保持单位及乘法，因此 `KleisliRecoveryIso`
是已有 `MonadCat` 中的同构。回收也保持 Kleisli 扩张及效应次序。此客户端
保留 Kleisli 模型声明的共同原生载体／相等界；状态载体及相等仍可处于不同的
较小层级。任意 ArrowApply 的往返、全部附加计算结构的相容性及带类型语法
仍属后续工作。

The current inventory covers 354 modules and the same 98 interfaces
(69 classes, 29 records), including all 29 `Has*` classes. The
[audit](./ComputationAudit.md#dynamic-arrow-adjunction-and-monad-recovery)
records the finite phase's validation and precise scope.

当前清单覆盖 354 个模块及原有 98 个接口（69 个类、29 个记录），包括全部
29 个 `Has*` 类。[审计](./ComputationAudit.md#dynamic-arrow-adjunction-and-monad-recovery)
记录此有限阶段的验证及精确范围。


## Kleisli comparison and explicit setoid strength foundations

## Kleisli 比较及显式广集强度基础

[AdjKleisliF](../theories/Cat/Monad/KleisliComparison.v) inverse-
transposes Kleisli arrows of an induced Monad into the adjunction target.
Its full-faithfulness witness keeps transposes as explicit preimages.
This general theorem requires no strength or finite products and does
not select target object representatives.
[SetStrength](../theories/Instance/Set/StrengthConstruction.v) explicitly
supplies coherent tensorial strength for a setoid endofunctor, using its
arrow action on pairing with a fixed ordinary value. `SetStrongM` keeps
the supplied Monad as its unique parent; compatibility follows from
naturality of unit and multiplication. Carrier/equality levels remain
independent. These are constructions, not new classes or globally enabled
model instances. The inventory now covers 356 modules and the same 98
interfaces; dynamic Arrow reconstruction will use these foundations.

[AdjKleisliF](../theories/Cat/Monad/KleisliComparison.v)将诱导 Monad
的 Kleisli 箭头逆转置到伴随目标；全忠实见证保留转置作为显式原像。此一般
定理不需要强度或有限积，也不选择目标对象代表。
[SetStrength](../theories/Instance/Set/StrengthConstruction.v)通过函子对
固定通常值配对的箭头作用，显式提供广集自函子的相干张量强度。`SetStrongM`
保留所给 Monad 为唯一父结构，相容性来自单位及乘法自然性，载体／相等层级
保持独立。这些是构造，不是新类或全局启用的模型实例。清单现覆盖 356 个
模块及原有 98 个接口，动态 Arrow 重建将复用这些基础。


## Reconstructing native dynamic Arrows

## 重建原生动态 Arrow

[DynamicRecovery](../theories/Cat/Computational/Arrow/DynamicRecovery.v)
explicitly gives the recovered Monad canonical strength and reuses the
existing Kleisli Arrow. Dynamic evaluation specializes the general
adjunction comparison; naming inherits its laws from the full-faithful
inverse. The object maps are identity on value indices, and two transparent
natural isomorphisms compare both composites with identity. This gives
the equivalence with the indexed computation category, without choosing
representatives for unrelated objects of the ambient category.

[DynamicRecovery](../theories/Cat/Computational/Arrow/DynamicRecovery.v)
显式为回收 Monad 赋予规范强度，并复用已有 Kleisli Arrow。动态求值专门化
一般伴随比较，命名从全忠实逆继承定律。对象映射在值索引上恒等，两个透明
自然同构将两侧复合与恒等比较。这给出与索引计算范畴的等价，不为环境范畴的
其他对象选择代表。

Both directions preserve pure arrows, sequential composition and ordinary
left context. The context proof first extracts a weaker
[ordinary-Arrow naming law](../theories/Cat/Computational/Arrow/Dynamic.v)
using the inverse pure unit-context square. These comparisons retain
independent computation-object, native Hom carrier and equality levels.
At a common native carrier/equality bound, `ArrowKleisliApply` reuses the
same recovered strong Monad and preserves dynamic application in both
directions after reindexing the supplied computation value through naming
or evaluation. Neither operation preservation nor inverse comparisons
require equality of structure records or their law fields.

双向保持纯箭头、顺序复合和通常左上下文。上下文证明先通过纯单位上下文
逆方块提取较弱的[普通 Arrow 命名定律](../theories/Cat/Computational/Arrow/Dynamic.v)。
这些比较保持独立计算对象、原生 Hom 载体及相等层级。在共同原生载体／相等
界上，`ArrowKleisliApply` 复用同一个回收强 Monad，通过命名或求值重索引所给
计算值后，双向保持动态应用。运算保持性及互逆比较均不要求结构记录或定律
字段相等。

The current inventory covers 357 modules and the same 98 interfaces
(69 classes, 29 records), including all 29 `Has*` classes. Cross-conversion
compatibility involving the derived Applicative remains a separate semantic
follow-up; syntax remains deferred. The
[audit](./ComputationAudit.md#native-dynamic-arrow-reconstruction)
records hypotheses, temporary checks and validation.

当前清单覆盖 357 个模块及原有 98 个接口（69 个类、29 个记录），包括全部
29 个 `Has*` 类。涉及派生 Applicative 的跨转换相容性仍为单独的语义后续工作，
语法继续暂缓。[审计](./ComputationAudit.md#native-dynamic-arrow-reconstruction)
记录假设、临时检查及验证。


## Dynamic reconstruction on the updated integration baseline

## 更新集成基线上的动态重建

Handoff synchronization rebases the task onto
`5631b64a7ad8e854638cd116169ca6ef5ceee761`. The upstream batch adds six
modules, the fixed-monoid property `IsCommMonoid`, and the bundled
triangle-label function `TwoCocycle`. The latter exposes its unique
`two_cocycle_triangle :>` function and retains Type-valued normalization
and tetrahedron laws. These additions match the existing distinction
between fixed-data properties and computational bundles.

交接同步将任务重基到 `5631b64a7ad8e854638cd116169ca6ef5ceee761`。上游
批次增加六个模块、固定幺半群上的性质 `IsCommMonoid`，以及三角标签
函数结构包 `TwoCocycle`；后者暴露唯一 `two_cocycle_triangle :>` 函数，保留
Type 值归一化及四面体定律。这些新增接口符合已有的固定数据性质／计算结构包
区分。

Three new upstream clients and two references in their new universe
regression still used multiplication and associativity names moved by the
task's earlier hierarchy slice. These references and group-equation
documentation now use `magma_mul_proper`, `magma_mul_l_resp`,
`magma_mul_r_resp` and `semigroup_assoc`. Mathematical operations, law
statements, public construction names and test assertions are retained.
The current inventory covers 363 modules and all 100 interfaces exactly
once (70 classes, 30 records), including the unchanged 29 `Has*` classes.

三个上游新客户端及其新宇宙回归中的两处引用仍使用本任务此前层级批次已迁移
的乘法及结合律名称。这些引用及群方程说明现使用 `magma_mul_proper`、
`magma_mul_l_resp`、`magma_mul_r_resp` 及 `semigroup_assoc`，保留数学运算、
定律陈述、公共构造名称及测试断言。当前清单覆盖 363 个模块及全部 100 个接口
各一次（70 个类、30 个记录），原有 29 个 `Has*` 类不变。

## Direct Applicative compatibility

## 直接 Applicative 相容性

[The shared comparison theory](../theories/Cat/Applicative/Morphism.v)
adds a Type-valued predicate on an existing natural transformation: preserve
pure and ordered pairing. Naturality then gives preservation of every binary
lifting and, with chosen exponentials, application in every ordinary context.
Identity, vertical composition and a chosen natural-isomorphism inverse retain
these laws. This is fixed-data theory; it adds no class, record, coercion path
or chosen model instance.

[共用比较理论](../theories/Cat/Applicative/Morphism.v)在已有自然变换上添加
Type 值谓词，要求保持纯值与有序配对。自然性随后给出每个二元提升，以及
选定指数时任意通常上下文中应用的保持性。恒等、垂直复合及选定自然同构逆
均保留这些定律。这是固定数据理论，不新增类、记录、强制转换路径或选定
模型实例。

[Dynamic compatibility](../theories/Cat/Computational/Arrow/DynamicApplicative.v)
uses the existing naming functor, pure/context preservation and general
Kleisli fanout law. The recovered Monad's Applicative and the Arrow's own
Applicative have an operation-preserving natural isomorphism in both
directions, with independent computation-object, native carrier and equality
sizes. No closed structure or equality of strength records is required.

[动态相容性](../theories/Cat/Computational/Arrow/DynamicApplicative.v)使用
已有命名函子、纯值／上下文保持性及一般 Kleisli fanout 律。回收 Monad 的
Applicative 与 Arrow 自身的 Applicative 双向具有保持运算的自然同构，计算
对象、原生载体及相等大小独立。不要求闭结构或强度记录相等。

[The native Kleisli comparison](../theories/Instance/Set/KleisliApplicative.v)
retains the existing recovery model's common carrier/equality bound and the
original Monad's supplied strength. Evaluation/constant components are reused
on the actual Applicative functors, without equating their functor law
records. Both comparison triangles agree with the existing Monad recovery
maps, and Monad recovery preserves the derived Applicative in both directions.
[Static recovery](../theories/Instance/Set/StaticArrow.v) also exposes its
existing pure/pairing comparisons through this same predicate.

[原生 Kleisli 比较](../theories/Instance/Set/KleisliApplicative.v)保留已有
回收模型的共同载体／相等界及原 Monad 所给强度。在实际 Applicative 函子上
复用求值／常值分量，不等同函子定律记录。两个比较三角与已有 Monad 回收
映射一致，Monad 回收也双向保持导出 Applicative。
[静态回收](../theories/Instance/Set/StaticArrow.v)同样通过此谓词暴露已有
纯值／配对比较。

The current source inventory is 370 modules and 100 interfaces (70 classes,
30 records), including all 29 `Has*` classes. This slice adds three theory/client
modules and no bundled interface. See the [computation audit](./ComputationAudit.md)
for assumptions, temporary validation and the agreed endpoint through free
constructions; typed syntax is outside that completion boundary.

当前源码清单为 370 个模块及 100 个接口（70 个类、30 个记录），包含全部
29 个 `Has*` 类。本批新增三个理论／客户端模块，不新增打包接口。假设、临时
验证及以自由构造为终点的已定范围，见[计算审计](./ComputationAudit.md)；
有类型语法不属于该完结范围。

This direct-comparison slice is now rebased onto integrated
`8db08e33d0e859c9a62980a2c313b4fb00398607`. All 48 task commits retain their
contents in the range comparison. The new upstream cocycle-completion client
uses the task's existing `magma_mul_proper` and `semigroup_assoc` names. Two
explicit Monoid universe instances in its new simplicial-model regression
are reordered to the existing hierarchy's carrier/equality/law parameter
order, preserving both native size profiles and every strict inequality.
No new interface or shared test configuration is introduced by this adaptation.

本次直接比较切片现已重基到集成版本
`8db08e33d0e859c9a62980a2c313b4fb00398607`，范围比较确认全部 48 个任务
提交内容不变。新增上游 cocycle 补全客户端改用任务已有的
`magma_mul_proper` 与 `semigroup_assoc` 名称。新增单纯模型回归中的两处
显式 Monoid 宇宙实例按现有层级的载体／相等／定律参数顺序排列，保留两种
原生大小配置及每条严格不等式。此适配不新增接口或共享测试配置。

## Independent elementary topos layer

## 独立初等拓扑斯层

[Topos](../theories/Topos/Core.v) now owns the elementary-topos part of
[ETCS](../theories/Topos/ETCS.v). Its one immediate parent is `ToposToCCC :> CCC`;
pullbacks and the classifier are supplementary chosen structures. The classifier
is indexed by the same terminal object inherited through `CCC` and
`CartCat`. ETCS stores `ETCSToTopos :> Topos`, retaining its chosen initial
object, well-pointedness, epi-splitting and NNO. No terminal, product, exponential,
pullback or classifier choice is duplicated. Parent records supply coercions; their chosen-structure fields
provide inherited instances.

[Topos](../theories/Topos/Core.v) 现持有 [ETCS](../theories/Topos/ETCS.v)
中的初等拓扑斯部分。唯一直接父结构为 `ToposToCCC :> CCC`，拉回与分类子为
补充选定结构；分类子以经 `CCC` 和 `CartCat` 继承的同一终对象为索引。
ETCS 保存 `ETCSToTopos :> Topos`，保留选定始对象、良点性、满态射分裂和
自然数对象。不重复选择终对象、积、指数、拉回或分类子；父记录提供强制转换，
其选择结构字段提供继承实例。

The classifier interface and proofs live in
[Topos/Sub.v](../theories/Topos/Sub.v), without any ETCS dependency.
Clients import that module directly. Following the user's module-layout
decision, [Topos/Nat.v](../theories/Topos/Nat.v) contains the optional NNO
structure, and [Topos/ETCS.v](../theories/Topos/ETCS.v) contains the stronger
set-theory bundle. The old ETCS directory and compatibility imports are
removed. Direct ETCS assembly still first assembles its Topos parent; no
classification property or Type-valued computational witness changes.

分类子接口和证明位于 [Topos/Sub.v](../theories/Topos/Sub.v)，不依赖 ETCS，
客户端直接导入该模块。按用户的目录整理决定，
[Topos/Nat.v](../theories/Topos/Nat.v) 保存可选自然数结构，
[Topos/ETCS.v](../theories/Topos/ETCS.v) 保存较强的集合论公理束。
原 ETCS 目录及兼容导入均已移除；直接装配 ETCS 仍须先装配其 Topos 父结构，
分类泛性质及 Type 值计算见证均不改变。

This extraction adds one bundled class. It does not add a model or derive
initial objects, finite colimits or internal logic. In particular, the base
Topos interface requires neither well-pointedness, choice, NNO nor a chosen
initial object. Subsequent sections deliver internal-logic fragments and
the ambient initial-object theorem; finite colimits and meaningful models
remain open milestones of issue #16.

本次抽取增加一个打包类，不增加模型，也不证明始对象、有限余极限或内部逻辑。
特别地，基础 Topos 接口不要求良点性、选择、自然数对象或选定始对象；后续
章节已交付内部逻辑片段及环境始对象定理；有限余极限与有意义模型仍为
issue #16 的开放里程碑。

## Characteristic arrows and pullback stability / 特征箭头与拉回稳定性

[Cat.Subobject](../theories/Cat/Subobject.v) derives `pullback_mono` for a
supplied square and packages its first projection as `PullbackMono`.
`pullback_subobject` transports that square to an equivalent subobject
representative through the existing `pullback_iso` construction. It retains
the comparison factor and requires neither a classifier nor chosen
pullbacks. The generic `pullback_congr` in
[Cat.Pullback](../theories/Cat/Pullback.v) transports a square along specified
arrow equalities while retaining its universal mediators.
[Sub_fmap](../theories/Instance/Set/Subobject.v) now uses `PullbackMono`
instead of proving monicity again; its domain and underlying arrow remain
the chosen pullback and first projection by conversion.

[Cat.Subobject](../theories/Cat/Subobject.v) 对给定方形证明 `pullback_mono`，
并以 `PullbackMono` 将第一投影组合成单态射。`pullback_subobject` 通过已有
`pullback_iso` 构造将方形传到等价子对象表示，保留比较因子；不要求分类子或
选定拉回。[Cat.Pullback](../theories/Cat/Pullback.v) 中的通用
`pullback_congr` 沿指定箭头相等传递方形，保留其泛中介。
[Sub_fmap](../theories/Instance/Set/Subobject.v) 改用 `PullbackMono`，不再重复
证明单态性；其定义域及底层箭头仍定义转换为选定拉回及第一投影。

[Topos.Sub](../theories/Topos/Sub.v) adds characteristic-arrow laws under
only named terminal/classifier choices. `classifier_char_proper` and its
`char_proper` instance ignore changes to monicity witnesses when underlying
arrows are equal. `classifier_char_subobject_eq` identifies equality of
characteristic arrows with mutual factorization of subobjects, without
identifying their domains or witness records. `classifier_char_pullback`
classifies any supplied inverse-image square by precomposition, using the
general pullback-pasting theorem. The truth subobject has characteristic
identity; the largest subobject has the constantly true characteristic.
The existing `classifier_char_unique` witness and the new equivalence
reflection keep their mediator data transparent.
No extra chosen pullbacks, CCC structure, well-pointedness, choice or NNO
are assumptions of these laws. Subsequent sections develop internal logic
and ambient initiality; finite colimits and meaningful models remain open.

[Topos.Sub](../theories/Topos/Sub.v) 仅在具名的终对象及分类子选择下增加特征
箭头律。`classifier_char_proper` 及其 `char_proper` 实例在底层箭头相等时
忽略单态性见证的差异。`classifier_char_subobject_eq` 将特征箭头相等刻画为
子对象相互分解，不识别其定义域或见证记录。`classifier_char_pullback` 复用
一般拉回粘合定理，以预合成分类任意给定的逆像方形。真子对象的特征箭头为
恒等，最大子对象的特征箭头为恒真。这些律不假定额外选定拉回、CCC 结构、
良点性、选择或 NNO。后续章节已发展内部逻辑并推导环境始对象；有限余极限
与有意义模型仍开放。
已有 `classifier_char_unique` 见证及新的等价反向映射均保留透明的中介数据。

## The generic truth subobject / 泛真子对象

[Topos.Representation](../theories/Topos/Representation.v) constructs
`ClassifiedSub f` as the chosen inverse image of truth, reusing
[Sub_fmap](../theories/Instance/Set/Subobject.v). Classifying this subobject
recovers `f`; pulling back truth along a subobject's characteristic arrow
recovers that subobject under mutual factorization. These laws make truth
a universal element of the explicitly lifted `SubF` on the opposite category.
`SubobjectRepresentation` then applies the existing
[lifted universal-element representation theorem](../theories/Instance/Set/Representable.v).
Its forward map takes the inverse image of truth; its inverse returns the
already chosen characteristic arrow. Both maps retain transparent data.
Subobject values are lifted as well. Native hom carriers and equality
witnesses remain independent; the lifted
comparison uses explicit common ambient bounds rather than resizing.
Only a named terminal choice, classifier and chosen pullbacks are required.
This optional module adds no model choice, structure field or global
selection instance, and does not change the base Topos imports.

[Topos.Representation](../theories/Topos/Representation.v) 复用
[Sub_fmap](../theories/Instance/Set/Subobject.v)，以真子对象的选定逆像构造
`ClassifiedSub f`。分类该子对象恢复 `f`；沿子对象的特征箭头拉回真子对象，
在相互分解等价下恢复原子对象。因此包装后的真子对象是反范畴上显式提升的 `SubF` 的泛元素。
`SubobjectRepresentation` 直接应用已有的
[提升泛元素表示定理](../theories/Instance/Set/Representable.v)：正向映射取真
子对象的逆像，逆向映射返回已有的选定特征箭头，二者均保留透明数据。原生
Hom 载体与相等见证保持独立；子对象值也显式提升到共同环境界，不使用大小重设。
前提仅为具名的终对象选择、分类子和选定拉回。此可选模块不增加模型选择、
结构字段或全局选择实例，也不改变基础 Topos 导入。

## Finite intersections of subobjects / 子对象的有限交

[Cat.SubobjectIntersection](../theories/Cat/SubobjectIntersection.v) views
the existing Type-valued factorization preorder as `SubCat X`, reusing
`PreorderCat`. Its identity and composition use an explicit transparent
`SubFactorPreorder`, since the old preorder instance proofs are opaque.
This retains actual comparison arrows without changing the old instances.
Parallel comparison witnesses have the thin category's singleton equality;
they are not identified by native equality. The largest subobject is
terminal without any limit choices. With chosen pullbacks, `s ∩Sub t`
retains the chosen pullback domain and the composite through its first
projection as its monomorphism. Factoring any arrow through the intersection
is equivalent to factoring through both subobjects, with transparent maps.

`SubCat_HasTerminal` and `SubCat_HasProduct` expose the existing terminal
and product interfaces and require explicit enabling. Commutativity pairs
the swapped projections using the transparent general product mediator;
associativity reuses the general product associator. Properness,
idempotence and the largest-subobject unit law use the same universal
property. No separate lattice structure or global chosen instance is added.
[Instance.Set.SubobjectIntersection](../theories/Instance/Set/SubobjectIntersection.v)
extends the existing inverse-image operation: it preserves subobject
inclusion, largest subobjects and binary intersections. All comparison
factors remain transparent. Only named chosen pullbacks are required;
these statements do not require a classifier, terminal object in the
ambient category, CCC or ETCS. They provide finite intersections, not the
remaining initial-object/finite-colimit or full internal-logic milestones.

[Cat.SubobjectIntersection](../theories/Cat/SubobjectIntersection.v) 复用
`PreorderCat`，将既有的 Type 值分解预序视为 `SubCat X`。由于旧预序实例
证明不透明，其恒等与复合显式使用透明的 `SubFactorPreorder`，保留实际比较
箭头，不改变旧实例。平行比较见证具有薄范畴的单元素相等，不以原生相等识别。
最大子对象不需要极限选择即为终对象。有选定拉回时，`s ∩Sub t` 保留选定
拉回定义域，以经过第一投影的复合作为单态射。任意箭头经过交分解等价于
经过两个子对象分解，两个方向均透明保留见证。

`SubCat_HasTerminal` 与 `SubCat_HasProduct` 使用已有终对象及积接口，由使用者
显式启用。交换律通过透明的一般积中介将交换后的投影配对，结合律复用一般积
的结合同构；保相等、幂等和最大子对象
单位律使用同一泛性质。不增加独立格结构或全局选定实例。
[Instance.Set.SubobjectIntersection](../theories/Instance/Set/SubobjectIntersection.v)
扩展原逆像操作，证明其保持子对象包含、最大子对象及二元交，所有比较因子
保持透明。前提仅为具名的选定拉回，不要求环境范畴的终对象、分类子、CCC
或 ETCS。这只提供有限交，不计为始对象／有限余极限或完整内部逻辑里程碑。

## Classifier conjunction / 分类对象上的合取

[Topos.Conjunction](../theories/Topos/Conjunction.v) defines `Conj` as the
characteristic arrow of `⟨truth, truth⟩` from the selected terminal object.
For predicates with a common context, `f ∧Ω g` applies this arrow to their
pair. The construction, its Proper instance, substitution law and truth
criterion require only named terminal, classifier and product choices.
The criterion says both predicates are constantly true, retaining their
specified Hom-equality witnesses. The generic `classifier_char_factor`
also retains the actual factor through a monomorphism; identifying a
classifier by this criterion uses no selected pullbacks or products.

With an additional named pullback choice, the characteristic arrow of
`s ∩Sub t` is `χ s ∧Ω χ t`. Reconstruction by inverse image gives the
corresponding subobject intersection with transparent comparison factors.
Commutativity, associativity, idempotence and the truth unit are transported
from the existing subobject-intersection laws. No exponentials, CCC, ETCS,
well-pointedness or classical principles enter these statements. The module
is optional, with no base import change or globally enabled chosen structure.
This is the conjunction fragment; implication, joins, bottom and other
Heyting logic, initial objects/finite colimits and meaningful models remain
separate milestones.

[Topos.Conjunction](../theories/Topos/Conjunction.v) 将从选定终对象出发的
`⟨truth, truth⟩` 的特征箭头定义为 `Conj`。同一上下文上的谓词以 `f ∧Ω g`
表示将该箭头作用于二者的配对。构造、Proper 实例、代入律及为真判据仅要求
具名的终对象、分类子与积选择。判据断言两个谓词均恒真，保留其指定 Hom
相等见证。一般的 `classifier_char_factor` 还保留经过单态射的实际分解因子；
由此判据确定分类箭头不需要选定拉回或积。

另有具名拉回选择时，`s ∩Sub t` 的特征箭头为 `χ s ∧Ω χ t`。通过逆像重构，
得到对应的子对象交及透明比较因子。交换、结合、幂等与真单位律均从既有
子对象交定律传递。不使用指数、CCC、ETCS、良点性或经典逻辑原理。模块保持
可选，不改变基础导入，也不全局启用任何选定结构。这仅为合取片段；蕴含、
并、底及其余 Heyting 逻辑、始对象／有限余极限和有意义模型仍为独立里程碑。

## Predicate entailment / 谓词蕴含序

[Topos.PredicateOrder](../theories/Topos/PredicateOrder.v) defines `f ⊢Ω g`
as an actual factor from `ClassifiedSub f` to `ClassifiedSub g`. The explicit
`PredicatePreorder` reuses the generic inverse-image preorder construction
with the transparent subobject preorder. Identity and transitivity retain
identity and composite arrows. Mutual entailment is equivalent to the
specified Hom equality; respectful transport uses transparent classifier
reflection rather than equality of functions or proof fields. Entailment
also says that the consequent is true on the antecedent's chosen subobject.

Classification commutes with precomposition up to subobject equivalence.
Together with existing inverse-image monotonicity, this gives a transparent
entailment factor after substitution. The constantly true predicate is top.
These statements require named terminal, classifier and pullback choices,
with no products. Adding named products gives conjunction's Type-valued
greatest-lower-bound property and its introduction/elimination factors;
`f ⊢Ω g` is equivalently `f ∧Ω g ≈ f`. No separate lattice bundle or global
chosen model is added. This supplies entailment and finite meets; the next
section develops the implication arrow. Joins, bottom and other remaining
milestones stay open.

[Topos.PredicateOrder](../theories/Topos/PredicateOrder.v) 将 `f ⊢Ω g`
定义为从 `ClassifiedSub f` 到 `ClassifiedSub g` 的实际分解因子。显式的
`PredicatePreorder` 以透明子对象预序复用一般预序逆像构造，恒等与传递保留
恒等及复合箭头。相互蕴含等价于指定的 Hom 相等，保相等运输使用透明分类
反射，不比较函数或证明字段。蕴含也表示后件在前件的选定子对象上为真。

分类与预合成按子对象等价相容，结合既有逆像单调性，得到代入后的透明蕴含
因子。恒真谓词为最大元。这些结论要求具名终对象、分类子和拉回选择，不需要
积。另加具名积选择，得到合取的 Type 值最大下界性质及引入／消去因子；
`f ⊢Ω g` 等价于 `f ∧Ω g ≈ f`。不另加格结构束或全局选定模型。此阶段
提供蕴含序与有限交，下一节发展蕴含箭头；并、底及其他未交付里程碑仍保持开放。

## Classifier implication / 分类对象上的蕴含

[Cat.EqualizerMorphism](../theories/Cat/EqualizerMorphism.v) packages a
candidate equalizer's same inclusion as `EqualizerMono`, reusing the existing
hom-extensionality theorem. Its Type-valued factor correspondence retains the
universal mediator without selecting limits. Separately,
[subobject restriction](../theories/Instance/Set/SubobjectRestriction.v)
observes that intersection uses the same pullback as inverse image along its
first subobject. The existing inverse-image factor theorem therefore gives
`r ∩Sub s ≲Sub t ↔ Sub_fmap r s ≲Sub Sub_fmap r t`, with transparent factors
and only named pullbacks.

[Topos.Implication](../theories/Topos/Implication.v) classifies the equalizer
of `Conj` and first projection as `Imp`. Applying it to a pair gives
`f ⇒Ω g`. Named terminal, classifier, product and equalizer choices suffice
for the arrow, Proper, substitution and the criterion
`f ⇒Ω g ≈ truth ∘ ! ↔ f ∧Ω g ≈ f`; no pullbacks or exponentials are needed
at that layer. With named pullbacks, subobject restriction transfers to
predicate entailment and gives the transparent Heyting adjunction
`r ∧Ω f ⊢Ω g ↔ r ⊢Ω f ⇒Ω g`, together with evaluation. Equalizer choices are
not registered globally. A topos client explicitly enables the existing
`ProductPullbackEqualizer` with its inherited products and pullbacks; no
Topos/ETCS field or choice is duplicated. There is no ETCS, classical logic,
global-point or model assumption. Joins, bottom, remaining internal logic,
finite colimits and meaningful models remain later milestones.

[Cat.EqualizerMorphism](../theories/Cat/EqualizerMorphism.v) 复用既有 Hom
外延定理，将候选等化子的同一包含打包为 `EqualizerMono`。其 Type 值分解
对应保留泛中介，不选择极限。另有
[子对象限制](../theories/Instance/Set/SubobjectRestriction.v)利用交与沿第一个
子对象的逆像使用同一拉回这一事实；已有逆像分解定理直接给出
`r ∩Sub s ≲Sub t ↔ Sub_fmap r s ≲Sub Sub_fmap r t`。因子透明，前提仅为
具名拉回选择。

[Topos.Implication](../theories/Topos/Implication.v) 将 `Conj` 与第一投影的
等化子分类为 `Imp`，作用于配对记为 `f ⇒Ω g`。具名终对象、分类子、积及
等化子选择已足以构造箭头，证明 Proper、代入及判据
`f ⇒Ω g ≈ truth ∘ ! ↔ f ∧Ω g ≈ f`；此层不需要拉回或指数。另加具名拉回，
将子对象限制传到谓词序，得到透明的 Heyting 伴随律
`r ∧Ω f ⊢Ω g ↔ r ⊢Ω f ⇒Ω g` 及求值。等化子选择不全局注册；拓扑斯客户端
以自身继承的积与拉回显式启用已有 `ProductPullbackEqualizer`，不重复保存
Topos/ETCS 字段或选择。不假定 ETCS、经典逻辑、全局点或模型。并、底、
其余内部逻辑、有限余极限及有意义模型仍属后续里程碑。

## Universal quantification along projections / 沿投影的全称量化

[Cat.ProductPullback](../theories/Cat/ProductPullback.v) obtains the pullback
of an arbitrary arrow along first projection from the product universal
property. The mediator is the original product pairing. `SubProduct s A`
displays the corresponding inverse image with the same domain `sub s × A`
and arrow `s × id`, using the existing pullback-monicity theorem. Only a
named product choice is needed; no pullback structure is selected.

[Topos.Forall](../theories/Topos/Forall.v) names the constantly true predicate
on `A` as `ForallTruth A : Hom 1 (Ω ^ A)` and classifies that monomorphism
from the terminal object as `Forall A`. For `f : Hom (X × A) Ω`, the notation
`∀Ω[A] f` applies this arrow to `ƛ f`. The construction, Proper, truth
criterion and context-substitution law need named terminal, classifier,
products and exponentials relative to those products. They reuse the
existing exponential β/η and substitution laws. The truth criterion says
that `∀Ω[A] f` is constantly true exactly when `f` is constantly true;
it does not use a test on external global elements.

With named pullbacks, the explicit product square compares the classified
subobject of `r ∘ π1` with `SubProduct (ClassifiedSub r) A`. This gives the
Type-valued right adjunction `r ∘ π1 ⊢Ω f ↔ r ⊢Ω ∀Ω[A] f`, evaluation,
monotonicity and instantiation by a term in the same context. Context
substitution commutes with quantifying the unchanged object `A`; no
arbitrary-morphism quantifier or complete hyperdoctrine is claimed. Actual
Topos clients use exactly their inherited product, exponential, terminal,
classifier and pullback choices. No new structure fields or globally
selected model instances are added. The next section develops bottom;
joins, remaining internal logic, ambient finite colimits
and meaningful models stay open.

[Cat.ProductPullback](../theories/Cat/ProductPullback.v) 从积泛性质得到任意
箭头沿第一投影的拉回，中介就是原有积配对。`SubProduct s A` 使用已有拉回
单态性定理，以同一对象 `sub s × A` 及箭头 `s × id` 展示相应逆像。前提仅为
具名积选择，不选择拉回结构。

[Topos.Forall](../theories/Topos/Forall.v) 将 `A` 上的恒真谓词命名为
`ForallTruth A : Hom 1 (Ω ^ A)`，并将从终对象出发的该单态射分类为
`Forall A`。对 `f : Hom (X × A) Ω`，记号 `∀Ω[A] f` 将此箭头作用于 `ƛ f`。
构造、Proper、为真判据及上下文代入律要求具名终对象、分类子、积和相对于
同一积的指数选择，复用已有指数 β/η 及代入律。为真判据表示 `∀Ω[A] f` 恒真
当且仅当 `f` 恒真，不通过外部全局元素来测试。

另加具名拉回，通过显式积方形将 `r ∘ π1` 的分类子对象与
`SubProduct (ClassifiedSub r) A` 比较，得到 Type 值右伴随
`r ∘ π1 ⊢Ω f ↔ r ⊢Ω ∀Ω[A] f`、求值、单调性以及用同一上下文中项的实例化。
上下文代入与对未改变对象 `A` 的全称量化相容；本批不声称任意态射的量词
或完整超教义。实际 Topos 客户端恰好使用继承的积、指数、终对象、分类子及
拉回选择，不新增结构字段或全局选定模型实例。下一节发展底；并、其余内部
逻辑、环境范畴有限余极限及有意义模型仍保持开放。

## False predicates and least subobjects / 假谓词与最小子对象

[Topos.Bottom](../theories/Topos/Bottom.v) defines `Bottom : Hom 1 Ω` by
universally quantifying the truth-value variable: `∀Ω[Ω] π2` in context `1`.
The predicate `⊥Ω` substitutes that same global arrow into any context.
Its substitution law and its expression as quantification of the variable
use the existing quantifier-substitution law, without identifying a context
with its product with `1`. Named terminal, classifier, products and relative
exponentials suffice for these arrows and equations.

With named pullbacks, quantifier instantiation by any predicate `f` gives
`⊥Ω ⊢Ω f`. Predicate equality reflection yields the leastness/uniqueness
criterion `f ⊢Ω ⊥Ω ↔ f ≈ ⊥Ω`, preserving the reverse factor.
`SubBottom X := ClassifiedSub (⊥Ω : Hom X Ω)` factors through every
subobject. Existing classification and inverse-image comparisons transport
these factors and prove inverse image preserves bottom. No proof records
or subobject witnesses are identified by native equality.

`SubCat_HasInitial X` explicitly packages this least subobject as initial in
the existing thin category `SubCat X`. It uses the original `HasInitial`
interface through terminality in the opposite category. Import does not
enable that choice globally. This is an initial object of the subobject
category. The separate [ambient initial construction](../theories/Topos/Initial.v)
below now upgrades the false subobject of `1` to ambient initiality.
Finite colimits, remaining internal logic and meaningful models stay open.
The next section constructs predicate joins.

[Topos.Bottom](../theories/Topos/Bottom.v) 在上下文 `1` 中对真值变量作全称
量化，以 `∀Ω[Ω] π2` 定义 `Bottom : Hom 1 Ω`。谓词 `⊥Ω` 将同一全局箭头
代入任意上下文。其代入律及在任意上下文中量化真值变量的刻画复用已有量词
代入律，不将上下文与其同 `1` 的积识别。这些箭头与方程仅要求具名终对象、
分类子、积和相对指数。

另加具名拉回，通过用任意谓词 `f` 作量词实例化得到 `⊥Ω ⊢Ω f`。谓词相等
反射给出最小性／唯一性判据 `f ⊢Ω ⊥Ω ↔ f ≈ ⊥Ω`，保留反向因子。
`SubBottom X := ClassifiedSub (⊥Ω : Hom X Ω)` 经过每个子对象分解；既有
分类与逆像比较运输这些因子，并证明逆像保持底。不用原生相等识别证明记录
或子对象见证。

`SubCat_HasInitial X` 在已有薄范畴 `SubCat X` 中显式将最小子对象打包为
始对象，经由反范畴中的终性复用原 `HasInitial` 接口，导入不全局启用该选择。
这是子对象范畴的始对象；下面独立的
[环境始对象构造](../theories/Topos/Initial.v)现将 `1` 的假子对象提升为环境
始对象。有限余极限、其余内部逻辑和有意义模型仍开放。下一节构造谓词并。

## Disjunction as a least upper bound / 作为最小上界的析取

[Topos.ImplicationLaws](../theories/Topos/ImplicationLaws.v) first extracts
exchange `r ⊢Ω (s ⇒Ω t) ↔ s ⊢Ω (r ⇒Ω t)` from the existing conjunction
adjunction and commutativity. Both directions retain actual factors.
The truth-antecedent law `(truth ∘ !) ⇒Ω f ≈ f` follows from the same
adjunction and conjunction's truth unit. These laws need named terminal,
classifier, pullbacks, products and equalizers, without exponentials.

[Topos.Disjunction](../theories/Topos/Disjunction.v) then defines the body
`(((f ∘ π1) ⇒Ω π2) ∧Ω ((g ∘ π1) ⇒Ω π2)) ⇒Ω π2` in `X × Ω`.
Quantifying its truth-value variable for the two projections gives one
arrow `Disj : Hom (Ω × Ω) Ω`; `f ∨Ω g` applies it to `⟨f,g⟩`.
It equals `∀Ω[Ω] (disjunction_body f g)` by the existing quantifier
substitution law. These arrows, Proper instances and substitution laws need
named terminal/classifier/products, exponentials relative to those same
products, and equalizers; they do not need selected pullbacks.
`∨Ω` is right associative at the existing implication level 46; `∧Ω` binds
more tightly. Parenthesize mixed implication/disjunction formulas, as above.

Adding named pullbacks, implication exchange gives the two introduction
factors. Quantifier instantiation by a common upper bound `r` then gives
`(f ∨Ω g) ⊢Ω r ↔ (f ⊢Ω r ∧ g ⊢Ω r)`. This is a correspondence of
Type-valued factors; both directions are transparent. Monotonicity,
commutativity, idempotence, associativity and the false-unit law follow from
this least-upper-bound property. No native equality of predicates, factors
or proof records is required. Actual Topos clients explicitly derive the
equalizers from their inherited products/pullbacks, retaining the same
terminal/classifier/product/exponential choices. No global model or chosen
structure is registered. This supplies predicate joins; subobject unions
and their categorical coproducts, ambient finite colimits,
existential quantifiers, further logic and meaningful models remain later
bounded stages.

[Topos.ImplicationLaws](../theories/Topos/ImplicationLaws.v) 首先由已有合取
伴随与交换性抽出交换律 `r ⊢Ω (s ⇒Ω t) ↔ s ⊢Ω (r ⇒Ω t)`，两个方向均
保留实际因子。真前件定律 `(truth ∘ !) ⇒Ω f ≈ f` 来自同一伴随及合取的
真单位元。这些定律只需具名终对象、分类子、拉回、积及等化子，不要求指数。

[Topos.Disjunction](../theories/Topos/Disjunction.v) 随后在 `X × Ω` 中定义
公式体 `(((f ∘ π1) ⇒Ω π2) ∧Ω ((g ∘ π1) ⇒Ω π2)) ⇒Ω π2`。对两个投影的
真值变量作全称量化，得到同一箭头 `Disj : Hom (Ω × Ω) Ω`；`f ∨Ω g` 将它
作用于 `⟨f,g⟩`。既有量词代入律给出它与 `∀Ω[Ω] (disjunction_body f g)`
相等。这些箭头、Proper 实例及代入律仅需具名终对象／分类子／积、绑定同一积
的指数以及等化子，不要求选定拉回。`∨Ω` 在既有蕴含层级 46 右结合，`∧Ω`
结合更紧；蕴含与析取混用时按上述公式加括号。

另加具名拉回，蕴含交换给出两个引入因子。用共同上界 `r` 作全称实例化得到
`(f ∨Ω g) ⊢Ω r ↔ (f ⊢Ω r ∧ g ⊢Ω r)`；此为 Type 值因子的对应，两个方向
均透明。单调、交换、幂等、结合及假单位元律来自同一最小上界性质，不要求
谓词、因子或证明记录的原生相等。实际 Topos 客户端显式从继承的积／拉回
推导等化子，保持同一终对象／分类子／积／指数选择，不注册全局模型或选定
结构。本批给出谓词并；子对象并及其范畴余积、环境有限余极限、存在
量词、其余逻辑及有意义模型留待后续有界阶段。

## Generic preorder adjunctions outside Topos / Topos 之外的通用预序伴随

[Cat.Logic.Adjunction](../theories/Cat/Logic/Adjunction.v) is an independent
categorical-logic prerequisite. It uses the existing
[preorder categories and functors](../theories/Cat/Preorder.v) and
[adjunction construction](../theories/Cat/Adjunction.v). It imports no
Topos module and assumes no truth-value objects, classifiers, limits or
quantifier constructions.
Given `F : Fct (PreorderCatAt R) (PreorderCatAt S)`, the reverse functor `G`
and maps `S (F x) y ↔ R x (G y)`, `PreorderAdj F G H` assembles `F ⊣ G`
using `AdjFromHom`. The relation witnesses remain arrows. Both native hom
maps retain the corresponding supplied maps definitionally; unit/counit
and naturality use the existing adjunction theory.

No native inverse equations between comparison witnesses are required:
parallel witnesses have the specified singleton equality in these thin
categories. This preserves their data without making arbitrary Type-valued
predicate families a posetal hyperdoctrine, identifying witness records or
truncating them into Prop. `preorder_adjunction_correspondence` recovers
the two witness maps from an existing adjunction; it asserts no equality
between chosen correspondences.

Object, relation-witness, hom-equality and law bounds are separate for both
preorder categories. The existing adjunction interface embeds their homs
in a sufficient common ambient setoid category; this is an upper bound,
not resizing or identification of native levels. `PreorderFAdj` specializes
the bridge to two monotone functions through the existing `PreorderF`,
keeping their supplied monotonicity maps. Neither constructor is a global
instance or chooses model structures by import.

The general bridge was delivered independently. The next section packages
the already proved Topos projection-substitution/forall correspondence as
an actual client of that integrated prerequisite. Classifier-specific
arrows stay specialized; reusable order/adjunction reasoning belongs here
or in the existing general theories. This does not supply arbitrary-arrow
quantifiers, Beck–Chevalley, Frobenius or a full hyperdoctrine, and does not
complete #6 or #16.

[Cat.Logic.Adjunction](../theories/Cat/Logic/Adjunction.v) 是独立的范畴逻辑
前置，复用既有[预序范畴／函子](../theories/Cat/Preorder.v)及
[伴随构造](../theories/Cat/Adjunction.v)，不导入 Topos 模块，不假定真值
对象、分类子、极限或量词构造。给定
`F : Fct (PreorderCatAt R) (PreorderCatAt S)`、反向函子 `G` 及映射 `S (F x) y ↔ R x (G y)`，`PreorderAdj F G H` 用
`AdjFromHom` 组装 `F ⊣ G`。关系见证保持为箭头；两个原生 Hom 映射定义上
保留给定对应映射，单位／余单位及自然性复用既有伴随理论。

不要求比较见证的原生互逆等式：薄范畴中平行见证使用指定的单元素相等。
这保留数据，不把任意 Type 值谓词族直接当作偏序超教义，不识别见证记录或
将它们截断成 Prop。`preorder_adjunction_correspondence` 从既有伴随取回
两个见证映射，不断言选定对应相等。

两个预序范畴各有独立的对象、关系见证、Hom 相等及定律界。既有伴随接口将
Hom 嵌入足够大的共同环境广集范畴；这是上界，不是重设大小或等同原生层级。
`PreorderFAdj` 通过既有 `PreorderF` 对两个单调函数特化，保留其给定单调
映射。两个构造均非全局实例，导入不选择模型结构。

一般桥梁已独立交付；下一节将已证明的 Topos 投影代入／forall 对应打包为
该已集成前置的实际客户端。分类子特有箭头保持为特化，通用序／伴随推理
放在此处或既有一般理论中。不声称任意态射量词、Beck–Chevalley、Frobenius
或完整超教义，也不关闭 #6 或 #16。

## Actual projection-quantifier adjunction / 实际投影量词伴随

[Topos.PredicateCategory](../theories/Topos/PredicateCategory.v) uses
`PredicatePreorder X` and the existing `PreorderCat` to define
`PredicateCat X`. Objects are classifier arrows on `X`; morphisms are the
same Type-valued classified-subobject factors. Their specified parallel
hom equality is thin, while identity/composition retain the transparent
original factors. `PredicateReindexF k` reuses `PreorderF` and exactly
`predicate_le_subst k` on arrows. This only needs named terminal,
classifier and pullback choices. Its object maps respect identity and
contravariant composition up to the original classifier-arrow `HomEq`;
there is no native equality claim about selected functors or factor data.

Adding named products and exponentials relative to the same products,
[Topos.ForallAdjunction](../theories/Topos/ForallAdjunction.v) defines
`PredicateForallF A X` using exactly the old `forall_predicate A` and
`predicate_forall_mono A`. `PredicateForallAdj A X` applies the independent
`Cat.Logic.Adjunction.PreorderAdj` bridge to the existing correspondence
`r ∘ π1 ⊢Ω f ↔ r ⊢Ω ∀Ω[A] f`. Thus projection substitution is left adjoint
to this forall functor in the existing `Adj` interface. No new proof of
that universal property or model choices is introduced.

The two transposes are definitionally the original forward/reverse factor
maps. The unit applies the same forward map to the weakened predicate's
transparent identity; the counit is exactly `predicate_forall_eval`.
Beta/eta, naturality and triangles then follow from the existing adjunction
interface using specified thin hom equality. They do not equate unrelated
computational factors by native equality. Actual Topos clients keep the
same inherited terminal/classifier/pullback/product/exponential choices;
no equalizer, initial-object, choice or NNO assumption is needed.

This is an actual client of the previously integrated general bridge, with
that bridge still outside Topos. It packages quantification only along a
fixed product projection. Arbitrary-arrow quantifiers, complete indexed
coherence, full hyperdoctrines, Beck–Chevalley/Frobenius, ambient
finite colimits and meaningful models remain separate work.

[Topos.PredicateCategory](../theories/Topos/PredicateCategory.v) 通过既有
`PreorderCat` 将 `PredicatePreorder X` 变成 `PredicateCat X`。对象是 `X`
上的分类箭头，态射仍是同一 Type 值分类子对象因子；平行 Hom 相等是指定的
薄相等，恒等／复合仍保留透明原有因子。`PredicateReindexF k` 复用
`PreorderF`，箭头映射恰为 `predicate_le_subst k`，仅需具名终对象、分类子
及拉回。其对象映射按原分类箭头的 `HomEq` 满足恒等及逆变复合，不断言选定
函子或因子数据的原生相等。

另加具名积及绑定同一积的指数，
[Topos.ForallAdjunction](../theories/Topos/ForallAdjunction.v) 以原有
`forall_predicate A` 和 `predicate_forall_mono A` 定义 `PredicateForallF A X`。
`PredicateForallAdj A X` 将独立的 `Cat.Logic.Adjunction.PreorderAdj` 桥梁
应用于已有对应 `r ∘ π1 ⊢Ω f ↔ r ⊢Ω ∀Ω[A] f`，在既有 `Adj` 接口中证明
此 forall 函子是投影代入的右伴随，不重证泛性质或另选模型数据。

两个转置定义上就是原有正／反向因子映射。单位是同一正向映射作用于弱化谓词
的透明恒等因子，余单位恰为 `predicate_forall_eval`。Beta／eta、自然性及
三角律随后复用既有伴随接口，使用指定薄 Hom 相等，不以原生相等识别不同
计算因子。实际 Topos 客户端保持同一继承终对象／分类子／拉回／积／指数
选择，不增加等化子、始对象、选择或 NNO 前提。

这是已集成一般桥梁的实际客户端，桥梁仍位于 Topos 之外；本批只打包固定
积投影上的量化。任意态射量词、完整索引相干、完整超教义、Beck–Chevalley／
Frobenius、环境有限余极限及有意义模型仍属后续工作。

## Pointwise comparisons into preorder targets / 到预序目标的逐点比较

[Cat.Logic.Natural](../theories/Cat/Logic/Natural.v) is a second independent
categorical-logic prerequisite outside Topos. For an arbitrary source
category `C`, a target `PreorderCatAt R`, and functors `F G`,
`PreorderN F G H` turns witnesses `H : ∀ c, R (F c) (G c)` into the existing
`Nat F G`. Naturality uses the specified thin target hom equality.
There is no source preorder or source thinness assumption, no classifier
or limits, and no new transformation interface. Both functors are supplied
explicitly, retaining their arrow maps rather than inferring functor data
from pointwise object images.

`PreorderNatIso F G H` accepts both comparisons at every object and retains
both as its forward/inverse components. Inverse naturality comes from the
existing `InvN` construction. Public native equations expose the
supplied components definitionally. The inverse laws use target `HomEq`,
without native inverse equations between comparison witnesses or native
equality of the functors' object maps. `preorder_nat_eq` compares arbitrary
parallel transformations by the existing `NatEq`; it does not identify
their component functions or proof records by Rocq equality.

The target's object, relation, hom-equality and law bounds remain separate,
as do the source category's native bounds. There are no global instances,
Proper registrations, model choices or new notation. The separate
[Topos reindex client](../theories/Topos/PredicateReindex.v) below now uses
the classifier's comparison factors for identity/composition natural
isomorphisms and `NatEq` for their coherence diagrams. The general
prerequisite itself does not provide a complete pseudofunctor/hyperdoctrine,
arbitrary-arrow quantifiers, Beck–Chevalley or Frobenius.

[Cat.Logic.Natural](../theories/Cat/Logic/Natural.v) 是 Topos 之外的第二个
独立范畴逻辑前置。给定任意源范畴 `C`、目标 `PreorderCatAt R` 及函子
`F G`，`PreorderN F G H` 将 `H : ∀ c, R (F c) (G c)` 组装为既有 `Nat F G`。
自然性使用指定的薄目标 Hom 相等，不要求源范畴是预序或薄范畴，不需要
分类子／极限，也不新造变换接口。显式给出两个函子，保留其箭头映射，不从
逐点对象像反推函子数据。

`PreorderNatIso F G H` 接受每个对象处的双向比较，并将其保留为正／反分量；
逆的自然性来自既有 `InvN`。公开原生方程给出这些分量与给定见证的
定义相等。互逆律使用目标 `HomEq`，不要求比较见证原生互逆或函子对象映射
原生相等。`preorder_nat_eq` 以既有 `NatEq` 比较任意平行变换，不用 Rocq
相等识别分量函数或证明记录。

目标的对象、关系、Hom 相等与定律界保持独立，源范畴的各原生界亦独立。
没有全局实例、Proper 注册、模型选择或新记号。下面独立的
[Topos 重索引客户端](../theories/Topos/PredicateReindex.v)现复用分类子比较
因子构造恒等／复合自然同构，并以 `NatEq` 验证相干图。一般前置自身不提供
完整伪函子／超教义、任意态射量词、
Beck–Chevalley 或 Frobenius。

## Predicate reindex comparisons / 谓词重索引比较

[Topos.PredicateReindex](../theories/Topos/PredicateReindex.v) is an optional
client of the independently integrated general preorder comparison bridge.
It requires only the named terminal, classifier and pullback choices used
by `PredicateCat` and `PredicateReindexF`. It adds no product, exponential,
CCC, ETCS or model-choice premise. The existing reindex object/arrow maps
are unchanged.

`PredicateReindexEqIso H` transports reindexing along a specified context
arrow equality `H : k ≈ k'`. It compares `f ∘ k` and `f ∘ k'` by the
transparent classifier-reflection factors. `PredicateReindexIdIso X`
compares reindexing by the context identity with `IdF`;
`PredicateReindexCompIso k l` compares `Rk ∘F Rl` with `R(l ∘ k)`.
All three directly use `PreorderNatIso` with explicit functor endpoints.
Six public native equations retain the forward factor and the factor
computed by the general `InvN` construction.

The two unit diagrams compare the composite comparison followed by
base unit-law transport with whiskering of the identity comparison
followed by the corresponding existing functor unitor. The association
diagram compares the two paths for three substitutions, explicitly using
`CompF_assoc` and base `comp_assoc` transport. Parallel paths agree by
`preorder_nat_eq` in existing `NatEq`. No native equality of context
arrows, functor records, comparison components or chosen factors is used.
Even a reflexive base-arrow equality may select a classifier factor
different from the identity factor.

The temporary payload probe makes this distinction observable: comparisons
retain factor 42 in both directions, while the inverse composite has 84
and the identity has 0. The left unit paths compute to 84/42, the right
unit paths to 84/126, and the association paths to 84/210. They satisfy the
specified natural equality. These are computational interface probes,
not meaningful models or native equalities of the paths.

This supplies the selected reindex comparisons and the two unit/one
association diagrams. It does not package a pseudofunctor or hyperdoctrine,
nor provide arbitrary-arrow quantifiers, Beck–Chevalley/Frobenius,
finite colimits or meaningful models. Those remain separate work for
#6/#16. No global instance, Proper registration or notation is added;
the classifier-specific assembly stays here while the comparison theory
remains outside Topos.

[Topos.PredicateReindex](../theories/Topos/PredicateReindex.v) 是独立集成的
一般预序比较桥梁的可选客户端，仅需 `PredicateCat`／`PredicateReindexF`
已有的具名终对象、分类子和拉回选择，不增加积、指数、CCC、ETCS 或模型
选择前提。既有重索引对象／箭头映射不变。

`PredicateReindexEqIso H` 沿指定上下文箭头相等 `H : k ≈ k'` 运输重索引，
用透明分类反射因子比较 `f ∘ k` 与 `f ∘ k'`。
`PredicateReindexIdIso X` 将上下文恒等重索引与 `IdF` 比较；
`PredicateReindexCompIso k l` 将 `Rk ∘F Rl` 与 `R(l ∘ k)` 比较。
三者均显式给出函子端点并直接应用 `PreorderNatIso`。六个公开原生方程
保留正向因子，以及一般 `InvN` 构造算出的反向因子。

两张单位图比较以下路径：复合比较后沿基范畴单位律运输；恒等比较的
whiskering 后接对应既有函子单位比较。结合图比较三次代入的两条路径，
显式使用 `CompF_assoc` 和基范畴 `comp_assoc` 运输。平行路径通过
`preorder_nat_eq` 在既有 `NatEq` 中相等，不使用上下文箭头、函子记录、
比较分量或选定因子的原生相等。即使基箭头相等自反，也可选出不同于恒等
因子的分类比较因子。

临时负载探针使此区别可计算：正反比较均保留因子42，逆复合为84而恒等
为0；左单位两路为84／42，右单位为84／126，结合为84／210。它们满足
指定自然相等，只是计算接口探针，不作为有意义模型或路径原生相等。

本批提供选定重索引比较及两张单位／一张结合图，不打包完整伪函子或超教义，
不提供任意态射量词、Beck–Chevalley／Frobenius、有限余极限或有意义模型；
这些仍是 #6／#16 的后续工作。不增加全局实例、Proper 注册或记号；分类子
特有组装留在此处，一般比较理论保持在 Topos 之外。

## Derived strict ambient initial object / 推导严格的环境始对象

[Topos.Initial](../theories/Topos/Initial.v) derives an actual initial object
of the ambient category from named terminal, classifier, pullback, product
and relative exponential choices. Each elementary Topos supplies exactly
these inherited choices. No initial-object assumption, well-pointedness,
epi splitting, choice or NNO is needed. This extends the earlier bottom
result from the thin subobject category to the ambient category itself.

`ToposInitial` is the domain of `SubBottom 1`. False is true on this
classified subobject by the original classified truth criterion. More
generally, `bottom_true_section` splits every monomorphism into a context
where false is true: leastness factors its false subobject through that
monomorphism, and the characteristic-arrow criterion factors the identity
through the false subobject. Applying this section to the equalizer of
two parallel arrows proves `bottom_true_hom_eq`. Equalizers come from the
existing `ProductPullbackEqualizer`, using the same products and pullbacks;
the existing `EqualizerMono` bundles its inclusion. There is no extra
chosen equalizer premise or new universal-property proof.

For any object `X`, `InitialProductSub X` displays `ToposInitial × X` as a
subobject of `1`. Its terminal arrow is monic: an incoming arrow makes its
source false, so all parallel arrows from that source agree. Leastness
then supplies `ToposInitial → ToposInitial × X`; projecting gives the actual
universal arrow `topos_init X`. Uniqueness follows from the same
false-context equality theorem. The public data equation retains exactly
this least-subobject factor and product projection.

`topos_initial_universal` proves the existing Type-valued `is_initial`
property, with its category explicitly fixed. `Topos_HasInitial` packages
that witness through terminality in the opposite category, preserving
native object/arrow computations. It is a plain optional definition:
import does not globally enable it, alter Topos/ETCS fields or replace an
existing initial-object choice. `topos_initial_strict f` proves every
arrow `f : X → ToposInitial` invertible, retaining `topos_init X` as its
transparent inverse. All uniqueness and inverse laws use specified
hom equality, without equality of proof fields or a classical principle.

This delivers the ambient initial-object milestone and its strictness.
Finite coproducts/finite colimits, further quantifier stability and
meaningful models remain separate work. Earlier explicit-universe breaking
records are unaffected; this optional construction introduces no old API,
universe or choice migration.

[Topos.Initial](../theories/Topos/Initial.v) 从具名终对象、分类子、拉回、积及
相对指数选择推导环境范畴的实际始对象；每个初等 Topos 已通过继承提供这些
选择。不要求始对象、良点性、满态射分裂、选择或 NNO。这将此前子对象薄
范畴中的底结果推进到环境范畴本身。

`ToposInitial` 是 `SubBottom 1` 的定义域。由原分类为真判据，假在此分类
子对象上为真。一般地，`bottom_true_section` 分裂每个映入假为真上下文的
单态射：最小性使假子对象经该单态射分解，特征箭头判据再将恒等经假子对象
分解。将所得截面用于一对平行箭头的等化子，得到 `bottom_true_hom_eq`。
等化子由既有 `ProductPullbackEqualizer` 使用同一积和拉回提供，包含箭头由
既有 `EqualizerMono` 打包，不增加独立等化子前提或重证泛性质。

对任意 `X`，`InitialProductSub X` 将 `ToposInitial × X` 展示为 `1` 的
子对象。它的终箭头是单态射：映入此积使源成为假上下文，因而该源出发的
平行箭头都相等。最小性随后给出 `ToposInitial → ToposInitial × X`，投影
得到实际泛箭头 `topos_init X`，唯一性复用同一假上下文相等定理。公开数据
方程恰好保留此最小子对象分解因子和积投影。

`topos_initial_universal` 显式固定范畴，证明既有 Type 值 `is_initial`。
`Topos_HasInitial` 经反范畴终性打包此见证，保持对象／箭头的原生计算。
它是普通可选定义；导入不全局启用，不改 Topos／ETCS 字段，也不替换已有
始对象选择。`topos_initial_strict f` 证明每个 `f : X → ToposInitial` 可逆，
保留 `topos_init X` 为透明逆。唯一性及互逆律均用指定 Hom 相等，不要求
证明字段相等或经典原理。

本批完成环境始对象及其严格性里程碑。有限余积／有限余极限、后续量词稳定性
和有意义模型仍属后续工作。此前显式宇宙 breaking 记录不变；此可选构造不
迁移旧 API、宇宙或选择。

## Images and epimorphic factors / 像与满分解箭头

[Cat.Image](../theories/Cat/Image.v) keeps the general candidate property
`is_image f m` outside Topos. It retains the factor through the candidate
monomorphism and its factor into every other containing subobject.
`image_factor_epi` proves any supplied factor through this image
epimorphic using only named equalizers, with no classifier or limits
beyond equalizers. The following Topos construction is its actual client.

[Topos.Image](../theories/Topos/Image.v) constructs the image of every
ambient arrow `f : X → Y`. It uses named terminal, classifier, pullback,
product and relative exponential choices, without an initial object,
classical logic, epi splitting or choice. Each elementary Topos supplies
these same inherited choices. This is a core prerequisite toward finite
coproducts/colimits; those constructions are still separate work.

The exponential `Ω ^ Y` parametrizes predicates on `Y` internally.
`image_contains f` universally quantifies their evaluations on `f` over
`X`. Its classified subobject `ImagePredicates f` is the family of
containing predicates. `image_predicate f` then universally quantifies the
evaluation of that family at a variable `y`. Thus it is their intersection.
The existing forall truth criterion, substitution law and product swap
show this intersection true on `f`. Quantification ranges over objects
of the category, without testing only global points or adding a new
power-object or existential-quantifier interface.

Any containing predicate `q` has an existing `exp_name q`.
Its evaluation law shows that name factors through `ImagePredicates f`.
Instantiating the intersection by this retained factor proves
`image_predicate f ⊢Ω q`. Classifying the intersection gives `ToposImage f`;
classification also supplies the actual arrow `topos_image_factor f`
whose composite with the image inclusion is `f` in specified HomEq.

`topos_image_universal f s` is the Type-valued correspondence between
`ToposImage f ≲Sub s` and a factorization of `f` through `s`. It retains
both factor maps. `topos_image_mediator` projects the minimality factor,
and `topos_image_mediator_unique` gives its full uniqueness property by
monicity. A monomorphism is equivalent to its own image. Equal arrows have
images related by actual mutual factors, without native equality of the
chosen internal predicate-family objects or their proof fields.

`topos_image_is_image` assembles the general candidate property from the
same factor and minimality maps. `topos_image_factor_epi` applies
`Cat.Image.image_factor_epi` with equalizers from the existing
product/pullback conversion. The general proof takes parallel arrows
agreeing after this factor and uses their equalizer. The actual Topos
client supplies `ProductPullbackEqualizer`; the general proof uses the
existing `EqualizerMono`. The original arrow factors
through the composite of that inclusion with the image inclusion. Image
minimality then splits the equalizer inclusion, so its commutativity law
gives equality of the original parallel arrows. No independently selected
equalizer or epi section is assumed; the epimorphism law does not assert
native equality of underlying arrows.

All selected factors remain transparent; the equality and epimorphism
proofs use the specified hom equality. The optional module adds no global
instance, Proper registration, notation or changes to existing choices.
This delivers least images and epi–mono factorization. It does not yet
prove image pullback stability or regularity, construct finite coproducts
or coequalizers, or deliver a meaningful model. Those remain open under
#16, together with further quantifier stability.

[Cat.Image](../theories/Cat/Image.v) 将一般候选性质 `is_image f m` 放在
Topos 之外，保留经候选单态射的因子及进入任意其他包含子对象的因子。
`image_factor_epi` 仅用具名等化子证明经此像的任意给定分解箭头为满态射，
不要求分类子或其他极限；下面的 Topos 构造是它的实际客户端。

[Topos.Image](../theories/Topos/Image.v) 构造每条环境箭头 `f : X → Y` 的像。
仅使用具名终对象、分类子、拉回、积及相对指数选择，不要求始对象、经典逻辑、
满态射分裂或选择；初等 Topos 已继承提供这些同一选择。这是通向有限余积／
余极限的核心前置，尚不计这些余极限完成。

指数 `Ω ^ Y` 内部参数化 `Y` 上的谓词。`image_contains f` 对谓词在 `f`
上的求值沿 `X` 作全称量化，其分类子对象 `ImagePredicates f` 是包含谓词族。
`image_predicate f` 再全称量化该族在可变 `y` 处的求值，因而是它们的交。
既有全称为真判据、代入律及积交换证明此交在 `f` 上为真。量化范围是范畴
中的对象，不只测试全局点，也不增加幂对象或存在量词接口。

每个包含谓词 `q` 都有既有名称 `exp_name q`；其求值律证明名称经
`ImagePredicates f` 分解。用此保留的因子实例化交，得到
`image_predicate f ⊢Ω q`。分类此交得到 `ToposImage f`，分类还给出实际
箭头 `topos_image_factor f`，与像包含的复合按指定 HomEq 等于 `f`。

`topos_image_universal f s` 是 `ToposImage f ≲Sub s` 与 `f` 经 `s` 分解
之间的 Type 值对应，保留两个方向的因子映射。`topos_image_mediator`
投影最小性因子，`topos_image_mediator_unique` 由单态性给出完整唯一性。
单态射与自身的像等价；相等箭头的像由实际相互因子联系，不要求选定内部
谓词族对象或其证明字段原生相等。

`topos_image_is_image` 由同一分解因子与最小性映射组装一般候选性质。
`topos_image_factor_epi` 将原积／拉回转换所得等化子交给
`Cat.Image.image_factor_epi`。一般证明对因子后相等的平行箭头取等化子；
Topos 实际客户端提供 `ProductPullbackEqualizer`，一般证明复用既有
`EqualizerMono`。
原箭头经等化子包含与像包含的复合分解，像的最小性随后分裂等化子包含，
其交换律给出原平行箭头相等。不假定独立等化子选择或满态射截面；满性定律
也不声称底层箭头原生相等。

所有选定因子保持透明，相等及满性证明使用指定 Hom 相等。可选模块不增加
全局实例、Proper 注册、记号或改变原有选择。本批交付最小像及满—单分解；
像的拉回稳定性／正则性、有限余积／余等化子、有意义模型及进一步量词稳定性
仍在 #16 中开放。


## Ambient finite coproducts / 环境有限余积

[Cat.Exponential.DoubleDual](../theories/Cat/Exponential/DoubleDual.v)
defines `ExpDoubleDualUnit R X : X → R^(R^X)` in any category with named
products and relative exponentials. Its application and naturality laws use
the existing exponential bifunctor and specified hom equality. This general
construction needs neither a terminal object nor a classifier; the following
Topos construction is its actual client.

[Topos.Coproduct](../theories/Topos/Coproduct.v) derives binary coproducts
from the same named terminal object, classifier, pullbacks, products and
exponentials as an elementary Topos. It assumes no initial object, coproduct,
NNO, well-pointedness, classical principle or splitting of epis.

At the classifier `Ω`, double-dual evaluation is monic: the classifier of
the equalizer of the product projections supplies singleton tests. Applying
two equal evaluations to the same singleton test detects equality of their
inputs. `ToposDoubleDualMono X` retains the general evaluation arrow.

For `A` and `B`, set `P = (Ω^A) × (Ω^B)`. Each double evaluation extends
along its respective projection into `Ω^P`. `ToposCoproductSub A B`
classifies the join of these two image predicates; `ToposCoproduct A B` is
its underlying object. The image factors and join introductions give actual
injections `topos_inl` and `topos_inr`. Image minimality and the join
universal property retain a factor into every subobject containing both
raw inputs.

Given `f : A → Z` and `g : B → Z`, precomposition of predicates gives
`Ω^Z → P`, hence a lift `Ω^P → Ω^(Ω^Z)`. Naturality of double evaluation
shows that both raw inputs land in `ToposDoubleDualMono Z`. Minimality
of their support therefore lets the lift factor through that mono.
`topos_copair f g` is this retained classifier factor, with both beta laws.
For uniqueness, equalize two proposed arrows out of the support. Agreement
on the injections puts both raw inputs in the composite subobject, and
minimality splits the equalizer. Its equation gives equality of the arrows.

`topos_coproduct_universal` exposes the full Type-valued coproduct property.
The optional `Topos_HasCoproduct` packages it through the existing opposite
product interface, without rebuilding dual theory. Its object, injections
and copair reduce to the same constructed data; the existing coproduct
Proper and composition laws apply after explicit selection.

`ToposFiniteCoproductColimits n` combines that binary choice with
`Topos_HasInitial` through the existing opposite finite-product construction.
It supplies all colimits of `DiscreteCat (Fin n)`, including the empty
shape. The existing `FiniteCoproduct`, injections, copairs, beta laws and
uniqueness remain available with these explicitly supplied choices.
Neither importing this module nor having a Topos registers initial objects
or coproducts globally, and a previously chosen coproduct can coexist.

This delivers ambient finite coproducts. It does not establish their
disjointness or pullback stability, coequalizers or all finite colimits,
image stability/regularity, further quantifier stability or a meaningful
model. No old mathematical interface, universe contract or choice changes.

[Cat.Exponential.DoubleDual](../theories/Cat/Exponential/DoubleDual.v)
在具有具名积及相对指数的任意范畴中定义
`ExpDoubleDualUnit R X : X → R^(R^X)`。其应用与自然性定律复用既有指数
双函子及指定 Hom 相等，不要求终对象或分类子；下面的 Topos 构造是其实际
客户端。

[Topos.Coproduct](../theories/Topos/Coproduct.v) 从初等 Topos 的同一具名
终对象、分类子、拉回、积及指数推导二元余积，不假设始对象、余积、NNO、
良点性、经典原则或满态射分裂。

在分类子 `Ω` 处，双对偶求值为单态射：两个积投影的等化子的分类箭头给出
单元素测试。将两个相等求值应用于同一单元素测试，便检测输入相等。
`ToposDoubleDualMono X` 保留一般求值箭头。

对 `A`、`B`，取 `P = (Ω^A) × (Ω^B)`，两侧双重求值沿各自投影扩展到
`Ω^P`。`ToposCoproductSub A B` 分类这两个像谓词的并，
`ToposCoproduct A B` 是其底层对象。像分解与并引入给出实际注入
`topos_inl`、`topos_inr`。像最小性与并泛性质保留进入任意包含两侧原输入
的子对象的因子。

给定 `f : A → Z`、`g : B → Z`，谓词预合成给出 `Ω^Z → P`，从而得到
提升 `Ω^P → Ω^(Ω^Z)`。双重求值的自然性说明两侧原输入均落入
`ToposDoubleDualMono Z`，支撑最小性遂使提升经此单态射分解。
`topos_copair f g` 就是这一保留的分类子因子，并满足两条 β 律。
唯一性对支撑上的两个候选出发箭头取等化子；它们在注入上相等，使两侧原输入
进入复合子对象，最小性于是分裂等化子，其方程给出两箭头相等。

`topos_coproduct_universal` 暴露完整 Type 值余积性质。可选
`Topos_HasCoproduct` 经既有反积接口打包，不重建对偶理论；其对象、注入与
余配对原生归约到同一构造数据，显式选择后即可用既有余积 Proper 及复合律。

`ToposFiniteCoproductColimits n` 经既有反有限积构造，将此二元选择与
`Topos_HasInitial` 组合，提供包括空形状在内的 `DiscreteCat (Fin n)`
全部余极限。既有 `FiniteCoproduct`、注入、余配对、β 律及唯一性仍可显式
传入这些选择后使用。导入或具有 Topos 均不全局注册始对象或余积；已有余积
选择可共存。

本批交付环境有限余积，不计其不交性或拉回稳定性、余等化子或全部有限余极限、
像稳定性／正则性、进一步量词稳定性或有意义模型完成。不改变旧数学接口、
宇宙契约或选择。
