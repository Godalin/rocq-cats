# Bundled interfaces and underlying views

# 打包接口与底层视图

The lax monoidal interface now bundles its underlying functor and structure
in one class, exposing a single coercion to `Functor`. The first follow-up
from the library-wide survey now adds bundled cartesian and cartesian closed
functors. Existing fixed-data preservation interfaces remain available for
general theorems alongside those bundles.

Lax monoidal 接口现已将底层函子及结构打包在同一个类中，只提供一条到
`Functor` 的强制转换。全库调查后的首项后续工作现已添加打包的笛卡尔函子及
笛卡尔闭函子。已有固定数据保持性接口继续与打包接口共存，服务于一般定理。

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

[LaxMonoidalFunctor MC MD](../theories/Cat/Monoidal/Functor.v) now stores
`LaxMonoidalF :> Functor C D`, the unit comparison, natural tensorator and
three coherence laws. Clients use `L X` and `fmap L f`. The
[identity](../theories/Cat/Monoidal/Functor.v) and
[constant](../theories/Cat/Monoidal/Constant.v) constructors explicitly
choose their underlying functors. The
[monoid transport](../theories/Cat/Monoidal/Transport.v) remains derived
from `L`, including its action on homomorphisms.

[LaxMonoidalFunctor MC MD](../theories/Cat/Monoidal/Functor.v) 现在保存
`LaxMonoidalF :> Functor C D`、单位比较、自然 tensorator 及三条相干律。
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
candidates. [CartesianFunctor](../theories/Cat/Functor/Cartesian.v) stores one
`Functor` with inherited `IsCartesianF` evidence. It requires only the named
source terminal/products. [CCCFunctor](../theories/Cat/Functor/Closed.v) adds
exponential comparison invertibility, with the single coercion chain
`CCCFunctor → CartesianFunctor → Functor`. Its derived `IsCCCF` instance
shares the stored cartesian evidence. Preservation adapters, identity and
composition constructors reuse the existing proofs and computational witnesses.

2026-11-10 的后续工作基于集成提交
`b7455f5869a76862c0388967f31719058789fc47`，实现了调查中的前两个候选。
[CartesianFunctor](../theories/Cat/Functor/Cartesian.v) 保存一个 `Functor`
及继承的 `IsCartesianF` 证据，仅要求具名来源终对象／积。
[CCCFunctor](../theories/Cat/Functor/Closed.v) 增加指数比较可逆性，唯一强制
转换链为 `CCCFunctor → CartesianFunctor → Functor`；派生的 `IsCCCF` 实例
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
| [Functor](../theories/Cat/Functor/Core.v), [Nat](../theories/Cat/Natural.v) | Object map or component family / 对象映射或分量族 | Already expose the unique computational view / 已暴露唯一计算视图 |
| [Monad](../theories/Cat/Monad/Core.v), [MonoidObject](../theories/Cat/Monoidal/Monoid.v) | Endofunctor or ambient carrier / 自函子或所在范畴的载体 | Model for the new lax bundle; fixed-data law predicates also remain / 可作为 lax 打包范式，同时保留固定数据定律谓词 |
| [CwF](../theories/DTT/CwF.v) | `TyTmF :> Functor (C^op) FamCat` | Already bundles the functor and context extension; inherited terminal/context structures use `::` / 已打包函子和上下文扩张，用 `::` 继承结构 |
| [GraphMap](../theories/Graph/Morphism.v), [GeneratorNat](../theories/Cat/Diagram/Generator.v), [Chain](../theories/Cat/Chain.v) | Vertex map or component family / 顶点映射或分量族 | Existing coercions support direct application / 已支持直接作用 |
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

[MonoidalCategory C](../theories/Cat/Monoidal/Core.v) now has the computed
field `MonoidalC :> Cat := C`. It exposes the supplied category without
storing another one or changing any constructor argument. Clients can write
`Functor MC MD`, `@Ob MC` and `Functor (MC ×C MC) MC`. Tensor, associators,
unitors and their laws still use the named category and selected structure.
Two monoidal structures on the same category remain distinct choices;
recovering their category does not identify their tensor data. The conversion
does not enable any concrete monoidal instance.

[MonoidalCategory C](../theories/Cat/Monoidal/Core.v) 现通过计算字段
`MonoidalC :> Cat := C` 暴露给定范畴，不另存一个范畴，也不改变构造器参数。
客户端可写 `Functor MC MD`、`@Ob MC`、`Functor (MC ×C MC) MC`。张量、
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
| [CCCFunctor](../theories/Cat/Functor/Closed.v) | `CCCFunctor → CartesianFunctor → Functor → object function` / 经笛卡尔函子和普通函子到对象函数 | Already complete; no direct bypass / 已完整，不增加直接旁路 |
| [LaxMonoidalFunctor](../theories/Cat/Monoidal/Functor.v), [Monad](../theories/Cat/Monad/Core.v), [VertexFunctor](../theories/Instance/Set/Vertex/Functor.v) | Each goes through its unique `Functor` to the object function / 各自经唯一底层函子到对象函数 | Keep `fmap` for arrows; the respectful vertex-map adapter stays explicit / 态射保留 `fmap`，保相等顶点映射的适配器保持显式 |
| [CwF](../theories/DTT/CwF.v) | `CwF → Functor → object function`; an image is a [FamC](../theories/Instance/Set/Fam/Cat.v) / 函子像为相干族 | Its selected primary view is the type-and-term functor; adding a category view needs a separate interface decision / 主要视图已选为类型与项函子，增加范畴视图须另行决定 |
| [FamC and FamF](../theories/Instance/Set/Fam/Cat.v), [FamS](../theories/Instance/Set/Fam/Core.v) | `FamC → FamS → fiber function`; `FamF → FunS_resp → base function`; fibers go through `SetC → Type` / 相干族到纤维函数，相干族态射到基底函数，纤维经广集到类型 | Already chainable; the fiber action of a family morphism remains explicit / 已可连续使用，族态射的纤维作用保持显式 |
| [Cocone](../theories/Cat/Diagram/Dual.v), [Nat](../theories/Cat/Natural.v) | `Cocone → Nat → component function` / 余锥经自然变换到分量函数 | Already complete; keep the opposite-cone construction underneath / 已完整，底层保留反范畴上的锥构造 |
| [Sub and Mono](../theories/Cat/Morphism.v), [SliceHom](../theories/Cat/Slice/Core.v) | Subobjects reach a monomorphism, then its ambient arrow; `Mono` also exposes its domain object / 子对象经单态射到所在范畴的箭头，单态射还暴露定义域对象 | Preserve existing targets; check both paths before extending / 保留现有目标，扩展前核对两条路径 |
| [MonoidObject](../theories/Cat/Monoidal/Monoid.v) | The carrier target is `@Ob C`, not a fixed record such as `SetC` / 载体目标是所在范畴的对象类型，而非固定广集记录 | Dependent targets can stop chaining; use `MonoidCarrier A` when a concrete further view is needed / 依赖目标可能中断连续转换，具体底层视图需要时显式使用载体投影 |
| [CCC](../theories/Cat/CCC.v), [ETCS](../theories/ETCS/Core.v) | Both have a named category; neither has a category coercion or a stored CCC parent in ETCS / 均有具名范畴，尚无范畴强制转换；ETCS 未保存 CCC 父结构 | Candidates for computed category views; an ETCS-to-CCC adapter must share existing choices rather than duplicate them / 可考虑计算性范畴视图；ETCS 到 CCC 须复用已有选择，不能重复存储 |
| [Group](../theories/Algebra/Group/Core.v), [Monoid](../theories/Algebra/Monoid/Core.v) | `Group → Monoid → SetC → Type`; the parent remains an inherited instance / 群经幺半群、广集到载体类型，父结构仍是继承实例 | Implemented in the computational-model continuation below, reusing the stored parent and named setoid / 已在下述计算模型后续工作中实现，复用保存的父结构及具名广集 |
| [IsGroupoid](../theories/Cat/Groupoid/Core.v), [IsStrictTwoCat](../theories/Cat/Bicategory/Strict.v) | Witnesses on a fixed category/bicategory, including designated equality and comparison data / 固定范畴或双范畴上的见证，含指定相等及比较数据 | A parameter view is possible, but needs a client; do not collapse higher structure or change coherence / 参数视图技术上可行，待具体客户端；不折叠高阶结构、不改变相干性 |
| [Dual chosen structures](../theories/Cat/Colimit/Core.v), [HasInitial](../theories/Cat/Terminal.v), [HasCoproduct](../theories/Cat/Coproduct/Core.v), [HasCoequalizer](../theories/Cat/Coequalizer.v), [HasPushout](../theories/Cat/Pushout.v) | `::` inherits the original theory on opposite categories / 用实例继承反范畴上的原理论 | Keep the dual presentation and ordinary wrappers; these are choices on named data, not missing carrier bundles / 保留对偶呈现及通常包装，这是具名数据上的选择，不是缺少载体的结构包 |
| [HasLimitsOfShape](../theories/Cat/Limit/Core.v), [HasFiniteHomCover](../theories/Cat/Shape/Finite.v), [HasKanFillers](../theories/Instance/Set/Simplicial/Horn.v) | Inherited structures depend on diagrams, endpoints or horn indices / 继承结构依赖图式、端点或 horn 索引 | Use instance inheritance; no single uniform carrier conversion is needed / 使用实例继承，无须统一载体转换 |
| [Closure](../theories/Set/Closure/Core.v), respectful maps, [GraphMap](../theories/Graph/Morphism.v), [GeneratorNat](../theories/Cat/Diagram/Generator.v), [Chain](../theories/Cat/Chain.v), sections and matching families | Already expose their operation or component function / 已暴露运算或分量函数 | Keep their existing unique functional view / 保留已有唯一函数视图 |
| Remaining `Has*`/preservation interfaces, [Adjunction](../theories/Cat/Adjunction.v), [Comprehension](../theories/Cat/Comprehension.v), [Sieve](../theories/Cat/Sieve.v) | Operations, relations or multiple views on fixed data / 固定数据上的运算、关系或多个视图 | Retain explicit parameters as detailed below; no blanket category/functor coercions / 按下文保留显式参数，不统一增加范畴或函子转换 |
| [ArrowOb](../theories/Cat/Arrow/Core.v), [CommaOb](../theories/Cat/Comma/Core.v), [SliceOb](../theories/Cat/Slice/Core.v), commuting-square records, [Horn2Presentation](../theories/Instance/Set/Simplicial/Vertex/Filling.v), [is_unique](../theories/Meta.v), [LiftT](../theories/Set/Core.v) | Multiple endpoints or witness/presentation records / 多个端点或见证、呈现记录 | No new hierarchy edge justified / 不据此新增层级边 |
| [Cat](../theories/Cat/Core.v), [Graph](../theories/Graph/Core.v), [Bicat](../theories/Cat/Bicategory/Core.v) | Foundational structures, not an existing inheritance chain / 基础结构，尚非继承链 | Keep object/vertex types and derived underlying categories explicit / 对象、顶点类型及派生底层范畴保持显式 |

Temporary elaboration checks confirmed `Functor MC MD`, coexistence of two
structures on one category, unchanged lax object/arrow use, both strict
hom/equality universe orders, and transparent identities in setoid and
endofunctor models. They also checked existing family/CwF chains: with the
relevant interface modules imported, `U x : Type`, `f x : famC_base V` and
`(T X) a : Type` elaborate directly. For
`A : MonoidObject SetCartesianMonoidal`, `A : @Ob SetCat` works, but
`A : SetC` and `A : Type` do not; `MonoidCarrier A : Type` does.
The coercion graph matches declared targets, so reduction of a dependent
target to a concrete record does not automatically add another graph edge.

临时 elaboration 检查确认了 `Functor MC MD`、同一范畴上两个结构共存、
lax 对象／态射用法不变、Hom 与相等宇宙的两种严格次序，以及广集和自函子
模型的恒等运算保持透明。相干族和 CwF 的已有链也已检查：导入相关接口模块后，
`U x : Type`、`f x : famC_base V` 和 `(T X) a : Type` 均可直接使用。
对 `A : MonoidObject SetCartesianMonoidal`，`A : @Ob SetCat` 可用，
但 `A : SetC`、`A : Type` 不可用，显式 `MonoidCarrier A : Type` 可用。
强制转换图按声明的目标匹配；依赖目标能归约为某个具体记录，不会自动增加
一条新的图边。

The first change implements the monoidal category view; the continuation
below adds group/monoid views. CCC/ETCS views remain follow-up candidates.
`Cat` has no coercion to its object type, and `Functor` still uses its
object function as its sole function coercion; arrow mapping stays `fmap`.

首项修改实现幺半结构的底层范畴视图；下述后续工作增加群／幺半群视图。
CCC／ETCS 视图仍属于后续候选。`Cat` 没有到对象类型的强制转换；`Functor`
仍以对象函数为唯一函数强制转换，态射映射保留 `fmap`。

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

## Computational-model continuation

## 计算模型接口后续工作

The continuation on `monoidal-cat-view`, following `3a47f38`, applies the
same design to the algebraic foundations of the computational models.
[Monoid M](../theories/Algebra/Monoid/Core.v) has the computed field
`MonoidS :> SetC := M`. [Group G](../theories/Algebra/Group/Core.v) registers
its existing `hasMonoid` projection as a coercion, keeping its `::` instance
registration. The unique chain is `Group → Monoid → SetC → Type`.
Constructor arguments and the chosen algebraic operations are unchanged.
At this point the library has 26 field coercions and three explicit
coercion commands; module and class/record counts remain unchanged.

`monoidal-cat-view` 在 `3a47f38` 之后的后续工作，将同样的设计应用到计算
模型的代数基础。[Monoid M](../theories/Algebra/Monoid/Core.v) 增加计算字段
`MonoidS :> SetC := M`；[Group G](../theories/Algebra/Group/Core.v) 将已有
`hasMonoid` 投影注册为强制转换，同时保留其 `::` 实例注册。唯一转换链为
`Group → Monoid → SetC → Type`。构造器参数和选定代数运算均保持原样。
此时全库共有 26 个字段强制转换、三个显式强制转换命令，模块及类／记录数不变。

Given `HG : Group G`, clients can pass `HG` where `Monoid G` or `SetC`
is expected and bind `x : HG` as an element of the original setoid. For
example, `SetMonoidObject HG` builds the internal monoid object using the
same selected operations. The [lax transport](../theories/Cat/Monoidal/Transport.v)
now uses `L A` and `Hom A B` through the existing monoid-carrier view.
Its tensorator notation keeps explicit carrier projections: constructing
a pair before checking its dependent endpoint does not distribute
coercions into both pair components.

给定 `HG : Group G`，客户端可在要求 `Monoid G` 或 `SetC` 的位置传入
`HG`，也可用 `x : HG` 绑定原广集的元素。例如 `SetMonoidObject HG` 使用
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
`Applicative → LaxMonoidalFunctor → Functor → object function`, preserving
the selected parent functor and `fmap`. Its pure operation is a natural
transformation with unit/product compatibility, rather than a competing
function coercion. See the [computation audit](./ComputationAudit.md#lawful-applicative-slice)
for the proved laws, Reader model, size checks and remaining boundaries.

下一串行切片实现了 [Applicative](../theories/Cat/Applicative/Core.v)，唯一转换链
为 `Applicative → LaxMonoidalFunctor → Functor → object function`，保留
选定父函子和 `fmap`。纯值运算是满足单位／积相容律的自然变换，不增加竞争的
函数强制转换。已证定律、Reader 模型、大小检查及剩余边界见
[计算模型审计](./ComputationAudit.md#lawful-applicative-slice)。

The operation-comparison slice adds
[ApplicativeOps](../theories/Cat/Applicative/Operations.v) and
[ApplicativeAp](../theories/Cat/Applicative/Application.v). Each has a single
`Functor → object function` view, preserving `fmap`; pure and application
stay explicit operations. Their conversions retain that same functor and
compare the supplied operations by designated equality. No competing
coercion to the structural Applicative is registered.

运算比较切片增加 [ApplicativeOps](../theories/Cat/Applicative/Operations.v)
及 [ApplicativeAp](../theories/Cat/Applicative/Application.v)，两者均只有
`Functor → object function` 视图，保留 `fmap`；纯值及应用仍为显式运算。
转换保留同一底层函子，使用指定相等比较所给运算，不注册到结构式 Applicative
的竞争强制转换。

The strength phase adds [StrongMonad](../theories/Cat/Monad/Strength.v)
with the unique chain `StrongMonad → Monad → Functor → object function`.
Its `hasStrength` field inherits a chosen structure on that same functor;
no second functor view is introduced. The
[MonadA conversion](../theories/Cat/Monad/Applicative.v) is an explicit
construction, preserving the parent functor and `fmap`, rather than another
coercion path. The [State model](../theories/Instance/Set/State.v) likewise
provides explicitly selected values.

强度阶段增加 [StrongMonad](../theories/Cat/Monad/Strength.v)，唯一转换链为
`StrongMonad → Monad → Functor → object function`。`hasStrength` 字段继承同一
函子上的选定结构，不增加第二个函子视图。
[MonadA 转换](../theories/Cat/Monad/Applicative.v) 为显式构造，保留父函子及
`fmap`，不增加竞争的强制转换路径；[状态模型](../theories/Instance/Set/State.v)
同样只提供须显式选定的值。

## Follow-up candidates

## 后续候选

| Candidate / 候选 | Current boundary / 当前边界 | Proposed treatment / 建议处理 | Main clients and risk / 主要客户端及风险 |
| --- | --- | --- | --- |
| [iso](../theories/Cat/Core.v), [NatIso](../theories/Cat/Natural.v) | Sigma bundles with `.1`/`.2` projections; unique forward arrow/transformation / 通过 `.1`、`.2` 访问的依赖和，具有明确正向箭头／自然变换 | Consider named records with a forward-map coercion while retaining `is_iso` and `is_NatIso_of` / 可考虑具名前向映射的记录，同时保留固定映射上的可逆性接口 | Foundation-wide migration, including [CatCat equivalence](../theories/Cat/CatCat.v) and [representations](../theories/Instance/Set/Representable.v); separate prerequisite task, not a local rename / 牵涉范畴等价及表示，须作为独立前置任务 |
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
| [Adjunction F G](../theories/Cat/Adjunction.v) | Relates two specified functors; keep left/right views explicit / 关联两个指定函子，左右视图应显式访问 |
| [HasCartesianLift P](../theories/Cat/Fibration.v), [HasFreeObjects U](../theories/Cat/FreeObject/Core.v) | Choose lifts or universal arrows for the existing functor; a future bundled fibration/right-adjoint view can reuse these interfaces / 为已有函子选择提升或泛箭头，未来打包视图可复用这些接口 |
| [HasDisplay](../theories/DTT/Display/Core.v), [HasContextExtension and CwF](../theories/DTT/CwF.v), [HasContextRepresentation](../theories/DTT/Context/Representation.v) | Describe interchangeable presentations over a fixed presheaf/family functor; CwF already supplies the complete bundled object / 描述固定预层／族函子上的可互换呈现，完整打包对象已有 CwF |
| [Monoid](../theories/Algebra/Monoid/Core.v), [Group](../theories/Algebra/Group/Core.v) | Selected algebraic structure on a fixed setoid; `Group` inherits its monoid with `::`; [SetMonoidObject](../theories/Instance/Set/Monoid.v) already supplies a bundled carrier presentation / 固定广集上的选定代数结构，已有继承及带载体的幺半群对象呈现 |
| [MonoidalCategory](../theories/Cat/Monoidal/Core.v), [CCC](../theories/Cat/CCC.v), [ETCS](../theories/ETCS/Core.v), [IsGroupoid](../theories/Cat/Groupoid/Core.v), [IsStrictTwoCat](../theories/Cat/Bicategory/Strict.v) | Named-category/bicategory extensions; retain explicit chosen structures, equality relations and comparison maps / 具名范畴／双范畴上的扩展，保留显式结构、相等关系及比较映射 |
| `HasTerminal`, products, coproducts, exponentials, (co)equalizers, pullbacks/pushouts, [HasLimit and HasLimitsOfShape](../theories/Cat/Limit/Core.v), [colimit interfaces](../theories/Cat/Colimit/Core.v) | Choose constructions for fixed categories/diagrams; their derived functors remain derived / 为固定范畴／图式选择构造，其诱导函子仍是派生构造 |
| [HasFiniteCover](../theories/Set/Finite.v), [finite generators/covers](../theories/Cat/Shape/Finite.v), [horn fillers](../theories/Instance/Set/Simplicial/Horn.v), [two-horn fillers](../theories/Instance/Set/Simplicial/Horn2.v), [IsCoskeletal](../theories/Instance/Set/Simplicial/Coskeletal.v) | Additional evidence or choices for fixed sets/categories/simplicial objects / 固定集合、范畴或单纯对象上的额外证据或选择 |
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
