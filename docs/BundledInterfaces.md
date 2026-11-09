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
