# Monad Applicative and Arrow audit

# Monad、Applicative 与 Arrow 审计

[Issue #35](https://github.com/Godalin/rocq-cats/issues/35) starts with a
source-level prior-art audit. The first implementation slice is **lax monoidal
transport of monoid objects and homomorphisms** (milestones B and G). This is
an existing mathematical result, with an existing Lean formalization; its
purpose here is integration with the library's Type-valued setoid equality
and independent universes. No formalization-priority claim is made.

[#35](https://github.com/Godalin/rocq-cats/issues/35) 首先要求审计已有形式化成果。
首个实现切片为 **lax monoidal 函子对幺半群对象及同态的传输**（B、G 里程碑）。
这是已有数学结果，Lean 也已有形式化；本库的任务是将其接入 Type 值广集相等
及独立宇宙层级。这里不主张形式化优先性。

## Revisions and evidence

## 版本及证据

Sources were read on 2026-11-09 at the following fixed revisions. The audit
checks declarations and proof bodies, not just module names or explanatory
comments. Third-party projects were not compiled and their transitive axioms
were not kernel-audited. “Not established” below describes the checked source,
not a claim that no such theorem exists anywhere in the project.

以下固定版本的源码于 2026-11-09 阅读，检查范围包括声明与证明体，而不只看模块名
或说明文字。未编译第三方项目，也未对其传递依赖作内核公理审计。下文“未确立”
限定于检查到的源码，不声称整个项目不存在相关定理。

| Project / 项目 | Revision / 版本 |
| --- | --- |
| [jwiegley/category-theory][w] | `99869fd8d9117e900dea862d8612033848aa01dd` |
| [Lean mathlib4][m] | `9bac2d0692944a775113f7c130fd5e5b4608a854` |
| [Lean core][l] (mathlib's pinned toolchain) | `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a` (`v4.36.0-rc2`) |
| [agda/agda-categories][a] | `ade267a5a02688fb97ec9d6e03ab6192be94439e` |
| [UniMath/UniMath][u] | `7a4b03cce49449f45ce0d4285615165172f50546` |
| Rocq-Cats integration baseline / 集成基线 | `8ae7cbd9f09c1738e9e30f4c637004552338036d` |

The tables retain the issue's eight evidence columns. Equational laws of
operations are distinguished from preservation/reflection of a typed
syntactic equational theory.

下表保留 issue 要求的八项证据栏。运算等式定律与有类型语法等式理论的
保持／反映定理分别记录。

| Project/commit | Directly checked module/theorem | Laws included | Categorical characterization | Structural conversions | Equational theory results | Extra axioms/size constraints | Missing lemmas or compatibility boundary |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Wiegley `99869fd` | [Theory/Coq/Applicative.v][w-app]; [Applicative/Proofs.v][w-app-proofs]: `IsApplicative`, `EndoApplicative_Applicative`, `Identity_IsApplicative`, `arrow_IsApplicative`, `Compose_IsApplicative` | The operation class stores `pure` and `ap`, without law fields; separate categorical witnesses for named instances | `IsApplicative` returns the categorical `Applicative` structure on `ToAFunctor H` | Categorical structure → operations; identity, reader and composite witnesses | Computation lemmas; no typed three-way translation theorem in these declarations | Coq-type/function model; the checked `arrow_IsApplicative` proof uses `extensionality`; [Coq model][w-coq] documents its funext boundary | `IsApplicative`'s result does not mention its supplied operation instance: it alone does not prove that arbitrary supplied `pure`/`ap` agree with the categorical operations |
| Wiegley `99869fd` | [Functor/Applicative.v][w-capp]; [Monoidal.v][w-lax]; [Monoidal/Pure.v][w-pure]: `Applicative`, `LaxMonoidalFunctor`, `pure_natural`, `fmap_pure` | Tensorator naturality, two unit laws, associativity; naturality of strength-derived `pure` | Bundles tensorial strength and lax monoidal structure over a closed monoidal base | `pure` from unit comparison and strength; `ap` from tensorator and evaluation | Naturality rewrites; the four conventional `ap` laws are not proved by the checked `Applicative` declaration | Arbitrary categories with specified hom equality; `LaxMonoidalFunctor` additionally stores `pure_left`, `pure_right`, `ap_assoc` **isomorphisms** | In particular `ap_assoc : (F X ⊗ F Y) ⊗ F Z ≅ F (X ⊗ (Y ⊗ Z))` is extra data, not part of the minimal lax interface; compatibility between strength and tensorator needs separate attention |
| Wiegley `99869fd` | [Monad/Strong.v][w-strong]; [Kleisli/Premonoidal.v][w-kprem]; [Premonoidal/Freyd.v][w-freyd]: `StrongMonad`, `dstr`, `dstr'`, `Freyd_Kleisli`, `Freyd_Id` | Strength coherence and compatibility with unit/multiplication; premonoidal and centrality laws | Kleisli computations with separately functorial tensoring; central pure inclusion | Strong monad on a symmetric monoidal base → Kleisli premonoidal structure and the file's `Freyd` | Structural preservation lemmas; no computational Arrow syntax equivalence established here | Tensorial strength is input; `Freyd` uses native object equalities and transported identities | The source explicitly omits cartesian values, symmetric premonoidal structure, and symmetry preservation from `Freyd`; its result is an effectful-category interface, not the full classical Freyd characterization |
| Wiegley `99869fd` | [Construction/Day.v][w-day]: `Day`, `Day_Tensor`, `lu_iso`, `ru_iso`, `day_assoc_iso`; [Sets/Coend.v][w-coend]: `SetsCoend` | Functor laws, natural unitors and associator, inverse laws | Covariant setoid-valued Day convolution via generated coend equality | Coend mediators and natural maps in both arguments | Pointwise/setoid coherence ingredients, not an Applicative/Day equivalence | Concrete coend equality is inductive in `Type`; output size must accommodate object-indexed sums and homs | The checked file explicitly defers the packaged monoidal structure and its pentagon/triangle proofs; do not infer them from the existence of `day_assoc_iso` |
| Wiegley `99869fd` | [Theory/Profunctor.v][w-prof]; [Compose.v][w-prof-comp]; [Laws.v][w-prof-laws]: `Profunctor`, `prof_compose`, `prof_unit_left_iso`, `prof_unit_right_iso`, `prof_assoc_iso`; [Cayley.v][w-cayley]: `To_Cayley`, `From_Cayley` | Profunctor functor laws and composition unit/associator isomorphisms; Cayley functor laws | Profunctors are `Cᵒᵖ × D → Sets`; Cayley is a category-level Yoneda-style representation | Profunctor composition; category-to-Cayley and evaluation back | `Cayley_Left`/`Cayley_Right` reassociate composition | Profunctors are kept in per-pair functor categories for universe reasons | Composition laws defer a bundled bicategory; ordinary profunctors do not supply strong promonads. Category-level Cayley is not the paper's internal-hom monoid representation |
| Lean/mathlib `9bac2d0`; core `b35cb10` | [Init/Control/Lawful/Basic.lean][l-lawful]: `LawfulApplicative`, `LawfulMonad`; [Control/Applicative.lean][m-app]: `instLawfulApplicativeComp`, lawful `Const` | Functor compatibility, `pure_seq`, `map_pure`, `seq_pure`, `seq_assoc`; Monad laws supply inherited Applicative laws | Lawful operations on type constructors | Lawful Monad includes lawful Applicative; lawful composition and constant applicatives | Actual operation equalities, not merely operation instances; no three-way categorical syntax comparison here | Law witnesses live in `Prop`; native equality and Lean extensionality/proof-irrelevance regime, not Type-valued setoid witnesses | An adapter to a generic categorical lax interface and preservation/reflection of Arrow calculi are separate obligations |
| Lean/mathlib `9bac2d0` | [Monoidal/Functor.lean][m-lax]: `Functor.LaxMonoidal`, `Functor.OplaxMonoidal`, `Functor.Monoidal`; [Monoidal/Mon.lean][m-mon]: `monObjObj`, `map.instIsMonHom`, `mapMon`, `mapMonIdIso`, `mapMonCompIso` | Tensorator naturality and three coherences; transported monoid and homomorphism laws; functor laws | Lax monoidal functors preserve monoid objects | Full functor on monoid-object categories; identity/composition comparison isomorphisms | Preservation of unit/multiplication by mapped homomorphisms | Independent object/hom universes; laws use native equality in `Prop` | This already covers the mathematical content of milestone B's transport theorem; Rocq-Cats needs integration with its own equality and universe discipline |
| Lean/mathlib `9bac2d0` | [DayConvolution.lean][m-day]: `DayConvolution`, `LawfulDayConvolutionMonoidalCategoryStruct`, `monoidalOfLawfulDayConvolutionMonoidalCategoryStruct`; [Closed.lean][m-day-closed]: `DayConvolutionInternalHom` | Chosen pointwise left Kan extensions, coherence for selected convolution structures; internal-hom/end data | General monoidal targets, not only endofunctors on types | Promotes suitable lawful data to monoidal structure | No lawful Applicative ↔ Day-monoid ↔ computational Arrow diagram established by these declarations | Requires selected extensions and tensor preservation of the stated colimits; internal homs additionally require ends and closedness | The source lists a lax-monoidal universal characterization and the `Type` case as TODOs; closed module also has an instance-packaging TODO. Read theorem bodies rather than treating every header TODO as current coverage |
| Agda `ade267a` | [Functor/Monoidal.agda][a-lax]: `IsMonoidalFunctor`, `IsStrongMonoidalFunctor`; [Monad/Strong.agda][a-strong]: `Strength`, `StrongMonad`; [Object/Monoid.agda][a-mon]: `IsMonoid`, `Monoid⇒`; [Construction/Kleisli.agda][a-kl] | Tensorator naturality, unit/associativity; strength and monad compatibility; monoid/homomorphism laws | Setoid-style hom equality with separate `o`, `ℓ`, `e`; lax vs strong distinguished | Strong → lax forgetful construction; monoidal Kleisli construction takes a **commutative** monad over a symmetric base | Certified diagrams; no three-way typed equational comparison in the inspected modules | All four inspected modules use `--safe --without-K`; joined levels bound records | Monoidal Kleisli under commutativity is stronger than the premonoidal Kleisli result needed for sequential effects; do not impose commutativity on all computational Arrows |
| UniMath `7a4b03c` | [Monoidal/Functors.v][u-lax]: `lax_monoidal_functor`, `make_lax_monoidal_functor`; [StrongMonad.v][u-strong]: `left_strength`, `left_strong_monad`; [CategoriesOfMonoids.v][u-mon]: `MON`; [Monads/Kleisli.v][u-kl]; [MonadsAsMonoidsElementary.v][u-mm] | Monoidal functor coherence; strength, unit/multiplication compatibility; monoid category laws | Hom-sets with identity-type equality; monad/monoid framework | Kleisli triple → Monad; endofunctor-monoid development | Structural equations; no three-way typed syntax theorem established here | UniMath foundations and hom-set truncation; strength-law propositionality explicitly uses `impred` and `homset_property`; transitive axiom usage not audited | This foundation is not a drop-in replacement for proof-relevant designated setoid equality; a bridge and the direct computation comparisons remain separate work |

The most important compatibility gaps are therefore substantive: operation
instances without laws, extra invertibility requirements in a purported lax
interface, missing compatibility with supplied operations, incomplete Day
coherence packaging, and a Freyd interface weaker than its classical name.
None of these establishes a new theorem merely by being absent from one
checked module.

关键兼容边界涉及实质内容：无定律的运算实例、lax 接口额外要求可逆、未关联
传入运算的结构谓词、Day 相干性封装尚未完成，以及弱于经典定义的 Freyd 接口。
某项结果未出现在被检查模块中，本身并不能证明其新颖性。

## Paper coverage and local reuse

## 论文覆盖及本库复用

The paper snapshot is [arXiv:1406.4823v1][paper], submitted 2014-05-29.
Its TeX source directly supplies the statements labelled `thm:monoid`
(the issue's Theorem 8.1) and `thm:Cayley` (the issue's Theorem 2.9).
This audit does not establish that all numbering and hypotheses coincide
with the 2017 journal version. The paper's associator orientation must also
be translated to this library's chosen orientation.

论文快照为 2014-05-29 提交的 [arXiv:1406.4823v1][paper]。其 TeX 源码可直接核查
`thm:monoid`（issue 所称定理 8.1）与 `thm:Cayley`（issue 所称定理 2.9）。
本次审计不主张全部编号与假设均与 2017 年期刊版一致；论文结合子的方向也须
转换为本库所选方向。

| Paper statement / 论文陈述 | Assumptions / 假设 | Local theorem or prerequisite / 本库定理或前置 | Checked third-party evidence / 已核查第三方证据 | Verification gap / 待验证边界 |
| --- | --- | --- | --- | --- |
| Lax functors preserve monoids (`thm:monoid`) | Two monoidal categories; unit comparison, natural tensorator, three coherences | [LaxMonoidObject, lax_monoid_hom and LaxMonoidF](../theories/Cat/Monoidal/Transport.v) reuse [MonoidObject and MonoidCat](../theories/Cat/Monoidal/Monoid.v) | mathlib `monObjObj`, `mapMon`, `mapMonCompIso` | Object and homomorphism transport implemented; identity/composition comparison of transport in the lax functor remains separate work. No closedness, strength, symmetry or coends required |
| Generalized Cayley (`thm:Cayley`) | A monoid whose carrier is exponentiable for the required tensor order; a chosen right internal hom is sufficient | General monoidal closed structure still needed; [CCC internal hom](../theories/Cat/Exponential/InternalHom.v) is a cartesian client | Wiegley's `Construction/Cayley.v` is category-level, not this statement | Endomorphism monoid; monoid homomorphism `rep`; ambient retraction `abs ∘ rep ≈ id`; do not claim `abs` preserves multiplication |
| Free monoid objects | Suitable countable coproducts, tensor preservation and explicit size/coherence data | Reuse [colimit theory](../theories/Cat/Colimit/Core.v) and [free-object interface](../theories/Cat/FreeObject/Core.v) where applicable | Not audited as an exact theorem in this slice | Specify sufficient existence assumptions before construction; neither a free monoidal category nor a free monad is this theorem |
| Monad as a monoid | Endofunctor category under composition | Already proved: [monad_monoid_laws and monad_monoid_equiv](../theories/Cat/Monad/Monoid.v); [is_monad](../theories/Cat/Monad/Core.v) already exists | Wiegley and UniMath have relevant developments | Reuse the existing presentation; no second Monad definition |
| Applicative as a Day monoid | Correct Day tensor, unit, coherence and size/existence conditions; strength when required | Direct lax/operation interfaces precede any new coend theory | Wiegley's Day ingredients; mathlib's selected Kan-extension formulation | Build the actual correspondence and law preservation; a module named Day is insufficient |
| Arrow as a strong profunctor monoid | Strong profunctors, chosen composition/coends, unit and associativity coherence | No computational Arrow interface in this baseline; [Cat/Arrow](../theories/Cat/Arrow/Core.v) is the ordinary arrow category | Wiegley's profunctor composition and weakened Freyd presentation | Strong promonads, full Arrow/Freyd correspondence and exact typed equational statements remain |

## Lawful Applicative slice

## 带定律的 Applicative 切片

The serial continuation after `1495819` adds
[Applicative](../theories/Cat/Applicative/Core.v) over a named category,
terminal object and binary products. It stores one cartesian lax monoidal
endofunctor and a natural pure map. Its two additional laws identify the pure
terminal component with the lax unit and identify the pure product component
with tensorial combination of pure components. Thus the pure map is monoidal.
No exponential structure is required by this interface. The unique coercion
chain is `Applicative → LaxMonoidalFunctor → Functor → object function`;
arrow maps retain `fmap`, and concrete choices remain explicit.

`1495819` 之后的串行后续工作增加
[Applicative](../theories/Cat/Applicative/Core.v)，依赖具名范畴、终对象及二元积。
它保存一个笛卡尔 lax 幺半自函子及自然纯值映射。两条新增定律分别将纯终值分量
与 lax 单位关联，将纯积分量与两个纯分量的张量组合关联，因此纯值映射是幺半的。
基础接口不要求指数结构。唯一强制转换链为
`Applicative → LaxMonoidalFunctor → Functor → object function`；
态射映射保留 `fmap`，具体选择继续显式启用。

[Binary lifting](../theories/Cat/Monoidal/Lifting.v) is first developed for
arbitrary lax monoidal functors and operations. Naturality, unary-map
substitution and preservation of general associativity diagrams do not use
pure values or exponentials. This supplies the reusable argument behind
Applicative composition. The shared
[internal composition evaluation lemma](../theories/Cat/Exponential/InternalHom.v)
comes from the existing exponential beta law and product associator.

[二元提升](../theories/Cat/Monoidal/Lifting.v) 首先针对任意 lax 幺半函子及运算
发展。自然性、一元映射代入及一般结合图的保持均不使用纯值或指数，提供了
Applicative 复合律背后的通用论证。共享的
[内部复合求值引理](../theories/Cat/Exponential/InternalHom.v) 来自已有指数 β 律
及积结合子。

With chosen exponentials, [application](../theories/Cat/Applicative/Closed.v)
is lifted evaluation. The proved classical laws are identity, homomorphism,
interchange and composition, including the curried pure composition followed
by three applications. All allow a shared arbitrary context. Homomorphism
allows both pure inputs to vary in that context; the pure function in the
mapping law and the pure argument in interchange are fixed global values
pulled back into the context. The equations use designated hom equality and
retain Type-valued witnesses; they do not equate functor or law records.

选定指数后，[应用](../theories/Cat/Applicative/Closed.v) 定义为提升后的求值。
已证明恒等、同态、交换和复合四条经典定律；复合律包含纯柯里化复合函数之后
连续三次应用的完整形式。全部允许任意共同上下文。同态律允许两个纯输入均随
上下文变化；映射律中的纯函数及交换律中的纯参数是拉入上下文的固定全局值。
等式使用指定 Hom 相等并保留 Type 值见证，不比较函子或定律记录的原生相等。

The explicitly selected [ReaderA](../theories/Instance/Set/Reader.v)
uses respectful maps, constant functions and pointwise pairing. Postcomposition
reuses the foundational composition laws. Its environment equality level is
separate, and a small environment permits the ambient carrier universe to be
strictly larger than the equality universe. Temporary checks instantiate the
abstract interface and application at both strict hom/equality universe
orders and check transparent Reader pure/map/pair/application computation.

显式选择的 [ReaderA](../theories/Instance/Set/Reader.v) 使用保相等映射、
常值函数及逐点配对，后合成复用基础复合定律。环境相等层级单独保留，小环境
允许所在广集载体宇宙严格大于相等宇宙。临时检查在 Hom／相等宇宙的两种严格
次序下实例化抽象接口及应用，并检查 Reader 纯值、映射、配对及应用的透明计算。

This is a sufficient lawful Applicative presentation, not a claim that an
arbitrary cartesian lax endofunctor determines a natural pure map. The reverse
construction from coherent operation interfaces is described below. Tensorial
strength and its compatibility laws, Monad conversion and computational Arrow
are delivered in the later slices below. The Reader model does not impose
size bounds on the abstract interface. No general coend or Day convolution
construction is introduced by this slice.

这是一种充分的带定律 Applicative 呈现，不主张任意笛卡尔 lax 自函子都确定
自然纯值映射。下文给出从相干运算接口的反向构造；张量强度及其相容律、Monad
转换和计算 Arrow 在下方的后续切片交付。Reader 模型的大小界不施加给抽象接口。
此切片不引入一般余端或 Day 卷积构造。

The existing `rocq-cats` switch (Rocq/Stdlib 9.2.0, Dune 3.23.1) passed
`dune build @all @runtest @install`. Twenty-nine temporary assumption checks
for lifting, pure/application laws, internal composition, the Reader model
and its computations all reported `Closed under the global context`.
Strict bilingual HTML export generated 260 modules per language and checked
links and anchors in 525 pages. New interface explanations were inspected in
both languages. No permanent test source or shared test alias was added;
batch PDF export remains with the integration session.

已有 `rocq-cats` switch（Rocq／Stdlib 9.2.0、Dune 3.23.1）通过
`dune build @all @runtest @install`。提升、纯值／应用定律、内部复合、Reader
模型及其计算的 29 项临时公理检查均报告 `Closed under the global context`。
严格双语 HTML 为每种语言导出 260 个模块，并检查 525 页的链接及锚点。
新增接口说明已在两种语言中核查。没有新增永久测试源码或共享测试别名，
批次 PDF 导出仍由集成会话负责。

## Coherent operation presentations and reconstruction

## 相干运算呈现及重建

[ApplicativeOps](../theories/Cat/Applicative/Operations.v) independently
stores an endofunctor, a natural pure map and a binary lifting operation.
Its fixed-data law class `IsApplicativeOps` requires respectfulness, result
and input substitution, preservation of pure pairs, left/right terminal
units and preservation of associativity diagrams with different intermediate
types. Every equation is an equation of arrows, not merely of global values.
No exponentials are required. The lifted identity on a product reconstructs
the tensorator; the pure terminal component reconstructs the unit comparison.
`OperationsA` proves the lax and pure compatibility laws from these operations.

[ApplicativeOps](../theories/Cat/Applicative/Operations.v) 独立保存自函子、
自然纯值映射及二元提升运算。固定数据定律类 `IsApplicativeOps` 要求保相等性、
结果及输入代入、纯配对保持、左右终单位律，以及具有不同中间类型的结合图保持。
所有方程都是态射方程，不只对全局值成立；不要求指数对象。积上恒等的提升恢复
tensorator，纯终分量恢复单位比较；`OperationsA` 从这些运算证明 lax 定律及
纯值相容律。

With chosen exponentials,
[ApplicativeAp](../theories/Cat/Applicative/Application.v) stores only the
endofunctor, natural pure map and application family. Currying, functorial
mapping and application reconstruct binary lifting. Its laws explicitly
require this reconstructed lifting to satisfy `IsApplicativeOps`.
`ApplicationA` then reconstructs the structural Applicative. Conversely,
lifting evaluation exposes application, and input substitution plus the
exponential beta law recover every original binary operation. A general
pointwise transport lemma transfers the fixed-data operation laws; it does
not equate functions or proof fields.

选定指数后，[ApplicativeAp](../theories/Cat/Applicative/Application.v)
只保存自函子、自然纯值映射及应用族。柯里化、函子映射及应用恢复二元提升；
定律显式要求恢复的提升满足 `IsApplicativeOps`，再由 `ApplicationA` 重建
结构式 Applicative。反向则通过提升求值暴露应用，输入代入及指数 β 律恢复
每个原二元运算。通用逐点运输引理运输固定数据上的运算定律，不比较函数或
证明字段的原生相等。

All conversions retain the underlying functor by computation and preserve
pure, binary lifting, application, tensorator and unit as applicable, using
designated hom equality. Application preservation also holds in arbitrary
shared contexts, so rewriting it and pure preservation transfers the four
classical laws from `ApplicationA`. These are coherent operation presentations:
no claim is made that four equations on global values alone supply all the
naturality/coherence data in an arbitrary CCC. These particular conversions
need no additional tensorial strength. The general tensorial-strength
foundation, strong-monad conversion and computational Arrow are described
below.
No Day convolution or extra model construction is introduced.

全部转换通过计算保留底层函子，并按适用情形使用指定 Hom 相等保持纯值、二元
提升、应用、tensorator 及单位。应用保持也对任意共同上下文成立，重写该比较及
纯值保持即可从 `ApplicationA` 运输四条经典定律。这是相干运算呈现：不主张仅
四条全局值方程就在任意 CCC 中提供全部自然性及相干数据。这些具体转换不额外
要求张量强度；一般张量强度基础、强 Monad 的顺序转换及计算 Arrow 见下文。
没有引入 Day 卷积或额外模型构造。

Validation uses the existing `rocq-cats` switch. Full-library build, tests
and installation passed. Temporary checks cover both strict hom/equality
universe orders, rewriting under the bundled operation, absence of implicitly
selected model instances, all four transferred classical laws over an abstract
CCC and ten transparent Reader computations through the conversions.
Seventy-seven temporary `Print Assumptions` checks reported
`Closed under the global context`, including the previous lifting/application
slice. Strict bilingual HTML export generated 262 modules per language and
checked links and anchors in 529 pages. Both languages of the new interface
explanations were inspected. The checks do not add permanent test sources or
shared test aliases. Batch PDF export remains with the integration session.

验证使用已有 `rocq-cats` switch，全库构建、测试和安装通过。临时检查覆盖
Hom／相等宇宙的两种严格次序、打包运算内部的重写、模型实例未被隐式选定、
抽象 CCC 上四条经运输的经典定律，以及经转换后的十项 Reader 透明计算。
包括前一提升／应用切片在内，77 项临时 `Print Assumptions` 均报告
`Closed under the global context`。严格双语 HTML 为每种语言导出 262 个模块，
并检查 529 页的链接及锚点；新增接口说明已在两种语言中核查。检查没有新增永久
测试源码或共享测试别名，批次 PDF 导出仍由集成会话负责。

## Tensorial-strength foundation

## 张量强度基础

[HasStrength](../theories/Cat/Monoidal/Strength.v) chooses a natural map
carrying an ordinary left tensor context through an effectful right input,
with unit and associator coherence. Its base is a named monoidal structure,
not necessarily cartesian. It is distinct from an invertible tensorator.
[StrongMonad](../theories/Cat/Monad/Strength.v) retains the existing ordinary
Monad as its unique underlying view and adds this chosen strength together
with compatibility with monad unit and multiplication. No commutativity,
closedness or implicit model selection is required.

[HasStrength](../theories/Cat/Monoidal/Strength.v) 选取自然映射，将左侧通常
张量上下文穿过右侧带效应输入，满足单位及结合子相干律。基底是具名幺半结构，
不必是笛卡尔结构；它不同于可逆 tensorator。
[StrongMonad](../theories/Cat/Monad/Strength.v) 保留已有普通 Monad 为唯一
底层视图，增加此选定强度及其与 Monad 单位、乘法的相容性。不要求交换性、
闭结构或隐式选定模型。

[Kleisli extension](../theories/Cat/Monad/Extension.v) and its unit,
substitution and associativity laws reuse the existing Monad operations.
Contextual extension in the strength module then transports an ordinary
tensor context through an effectful argument. Its associativity theorem
reassociates nested contexts and keeps effect order. This foundation is
independently reusable; the finite-product Applicative conversion below is
derived from these laws, rather than assumed as an extra field here.

[Kleisli 扩张](../theories/Cat/Monad/Extension.v) 及其单位、代入和结合律
复用已有 Monad 运算。强度模块中的上下文扩张继而将通常张量上下文穿过带效应
参数；其结合律重排嵌套上下文括号，保留效应次序。此基础可独立复用；下文
有限积上的 Applicative 转换由这些定律导出，并未作为额外字段假定。

The initial foundation slice passed the full build/test/install targets
with the existing `rocq-cats` switch. Temporary checks instantiated both
strict hom/equality universe orders and all 18 initial foundation assumption
checks were closed under the global context.
No permanent tests or shared environment changes were added.

初始基础切片在已有 `rocq-cats` switch 下通过全库构建、测试和安装。临时检查
实例化了 Hom／相等宇宙的两种严格次序，最初 18 项基础公理检查均无额外假设。没有新增永久测试或改动
共享环境。

## Strong Monad to ordered Applicative

## 强 Monad 到有序 Applicative

[Contextual binding](../theories/Cat/Monad/Context.v) specializes the general
strength extension to named finite products. Its endpoints expose those
products directly, and its equations cover equality, context substitution,
pure substitution, return, ordinary mapping and associative sequencing.
[Cartesian strength projection](../theories/Cat/Monoidal/CartesianStrength.v)
uses only strength naturality and its unit law to discard an ordinary
context without changing the effectful input.

[上下文绑定](../theories/Cat/Monad/Context.v) 将一般强度扩张特化到具名有限积，
端点直接暴露这些积。方程覆盖相等、上下文代入、纯值代入、返回、通常映射及
顺序组合的结合律。[笛卡尔强度投影](../theories/Cat/Monoidal/CartesianStrength.v)
仅用强度自然性及其单位律，证明丢弃通常上下文不改变带效应输入。

[MonadA](../theories/Cat/Monad/Applicative.v) takes a `StrongMonad` over the
cartesian monoidal structure determined by the named terminal object and
products. It retains the underlying functor by computation and uses the
original monad unit as its natural pure map. Binary combination binds the
left computation, then the right, then returns their pair. Naturality,
both unit laws, associativity and pure-product compatibility are proved
from the binding laws. The contextual pairing equation `monad_pair_pre`
keeps computations stored in an ordinary context abstract during the proof;
all temporary proof opacity is restored. No strength for an arbitrary
functor, commutativity, exponential objects or invertible tensorator is
assumed. With chosen exponentials, the existing application construction
and four classical laws apply directly to `MonadA`.

[MonadA](../theories/Cat/Monad/Applicative.v) 输入具名终对象及积所确定的笛卡尔
幺半结构上的 `StrongMonad`，通过计算保留底层函子，以原 Monad 单位作为自然
纯值映射。二元组合先绑定左计算，再绑定右计算，最后返回配对。自然性、左右
单位律、结合律及纯积相容律均由绑定定律证明。上下文配对方程 `monad_pair_pre`
在证明中保持存于通常上下文的计算抽象，全部临时证明不透明性均已恢复。不假定
任意函子具有强度，不要求交换性、指数对象或可逆 tensorator。选定指数后，已有
应用构造及四条经典定律可直接用于 `MonadA`。

The explicit [State model](../theories/Instance/Set/State.v) supplies the
ordinary `StateM`, coherent `StateStrength` and `StateStrongM`; `StateA`
is derived solely by the general conversion. No second set of model-specific
Applicative laws is proved. State and ambient equality/carrier levels remain
separate, subject to the actual function-space/product size bounds.
Explicit ambient universe parameters prevent the natural transformations
from unnecessarily identifying the ambient carrier and equality levels.
Importing the model does not select a monad, strength or Applicative instance.

显式[状态模型](../theories/Instance/Set/State.v) 提供普通 `StateM`、相干
`StateStrength` 及 `StateStrongM`；`StateA` 完全由一般转换导出，没有重复证明
模型专用的 Applicative 定律。状态及所在广集的载体／相等层级保持独立，保留
函数空间／积所需的真实大小界。显式所在宇宙参数避免自然变换的类型推断无谓地
合并所在载体及相等层级。导入模型不会自动选择 Monad、强度或 Applicative 实例。

Temporary checks instantiate the abstract conversion and its application
at both strict hom/equality universe orders, compare underlying functors by
identity natural isomorphisms, and check state models with both strict state
carrier/equality orders and a larger ambient carrier. Seven transparent
Boolean-state computations cover pure, mapping, two pairing orders, repeated
state transitions, application and an application-interface round trip.
Toggling state before reading yields a different returned Boolean from
reading before toggling, witnessing the specified order. All 148 temporary
assumption checks, including the previous Applicative slice, are closed
under the global context. No permanent tests or shared test aliases were
added. The ordinary Kleisli category is delivered in the next slice below;
the strong-Monad Arrow comparison is delivered below. Freyd and
Day/profunctor characterizations remain separate work.

临时检查在 Hom／相等宇宙的两种严格次序下实例化抽象转换及其应用，以恒等
自然同构比较底层函子，并在状态载体／相等的两种严格次序及更大的所在载体下
检查模型。七项布尔状态透明计算覆盖纯值、映射、两种配对顺序、重复状态转移、
应用及应用接口往返。先翻转再读取，与先读取再翻转返回不同布尔值，检验了指定
次序。包括前一 Applicative 切片在内，148 项临时公理检查均无额外假设。没有新增
永久测试或共享测试别名。普通 Kleisli 范畴在下方的下一切片交付；计算
Arrow 及其强 Monad 比较见下文；Freyd 及 Day／profunctor 刻画仍为后续工作。

The final phase passed `dune build @all @runtest @install` using the existing
`rocq-cats` switch (Rocq/Stdlib 9.2.0, Dune 3.23.1). Strict bilingual HTML
export generated 269 modules per language and checked links and anchors in
543 pages; the new explanations were inspected in both languages. Batch PDF
export remains with the integration session.

最终阶段在已有 `rocq-cats` switch（Rocq／Stdlib 9.2.0、Dune 3.23.1）下通过
`dune build @all @runtest @install`。严格双语 HTML 为每种语言导出 269 个模块，
检查 543 页的链接及锚点；新增说明已在两种语言中核查。批次 PDF 仍由集成会话
统一导出。

## Ordinary Kleisli category

## 普通 Kleisli 范畴

[KleisliCat](../theories/Cat/Monad/Kleisli.v) takes only the existing
`Monad C`. It keeps the objects of `C`, reuses `HomSet X (M Y)` with its
specified Type-valued equality, chooses the monad unit as identity and
composes by Kleisli extension. Respectfulness, both unit laws and
associativity reuse the existing extension theory. No strength, products,
terminal object, exponentials or commutativity are needed.

[KleisliCat](../theories/Cat/Monad/Kleisli.v) 只输入已有 `Monad C`，保留 `C`
的对象，复用 `HomSet X (M Y)` 及其指定 Type 值相等，以 Monad 单位为恒等，
用 Kleisli 扩张复合。保相等性、左右单位律及结合律复用已有扩张理论；不要求
强度、积、终对象、指数或交换性。

`KleisliPureF` sends ordinary arrows to pure computations and keeps objects
unchanged; it is not asserted faithful. `KleisliExtendF` sends objects to
their Monad images and computations to their extensions. Their composite
is compared with the original endofunctor by `KleisliCompositeIso`, whose
components are identities. This is a comparison of endofunctors, without
equating function or law records. This initial comparison concerns only
endofunctors; the full Monad recovery is delivered below.
The public `g ∘K[M] f` notation names the same composition as the category;
pure-input and pure-output equations recover ordinary substitution and
result mapping.

`KleisliPureF` 将通常箭头送为纯计算，对象不变，不断言它忠实。
`KleisliExtendF` 将对象送为 Monad 像，将计算送为其扩张。两者的复合通过
分量为恒等的 `KleisliCompositeIso` 与原自函子比较；这里只比较自函子，不等同
函数或定律记录。此初始比较只涉及自函子；完整 Monad 恢复见下文。
公开记号 `g ∘K[M] f` 就是此范畴
的复合；纯输入和纯输出方程分别恢复通常代入和结果映射。

Temporary checks cover both strict hom/equality universe orders with
arbitrary ordinary monads, inherited equality in both directions, rewriting
through composition, both functors and their natural isomorphism. Six
transparent state computations exercise sequencing, repeated transitions,
pure input/output and extension through the functor. All 34 assumption
checks for this slice are closed under the global context. The abstract
checks import only the Kleisli module and confirm strength interfaces are
unavailable. No permanent tests or model-specific category proofs were
added. Computational Arrow and its strength operations are delivered below;
Freyd remains later work.

临时检查对任意普通 Monad 覆盖 Hom／相等宇宙的两种严格次序、双向继承相等、
复合重写、两个函子及其自然同构。六项透明状态计算检验顺序组合、重复转移、
纯输入／输出及函子扩张；本切片 34 项公理检查均无额外假设。抽象检查仅导入
Kleisli 模块，并确认强度接口不可用。没有新增永久测试或模型专用的范畴证明。
计算 Arrow 及其强度运算见下文，Freyd 仍为后续工作。

This slice passed full-library build/tests/install with the same `rocq-cats`
switch. Strict bilingual HTML generated 270 modules per language and checked
545 pages; the new module's explanations and public constructions were
inspected in both languages. Batch PDF export remains with integration.

本切片使用同一 `rocq-cats` switch 通过全库构建、测试及安装；严格双语 HTML
为每种语言导出 270 个模块，检查 545 页，并核查两种语言中新模块的说明及公开
构造。批次 PDF 仍由集成会话统一导出。

## Kleisli adjunction and recovery of the Monad

## Kleisli 伴随及 Monad 的恢复

[KleisliAdjunction](../theories/Cat/Monad/KleisliAdjunction.v) reuses the
general `AdjunctionFromHom` construction with identity respectful maps:
the two hom-sets are the very same base hom-set. Their inverse equations
are reflexivity, source naturality is pure substitution, and target
naturality is Kleisli composition. Forward and inverse transposition
preserve the underlying computation. The unit is the original Monad unit;
the counit at `X` is the base identity on `M X`, viewed as a Kleisli arrow
from `M X` to `X`. Both triangle laws are inherited from the general
adjunction theory. Only an ordinary Monad is supplied.

[KleisliAdjunction](../theories/Cat/Monad/KleisliAdjunction.v) 以恒等保相等
映射复用一般 `AdjunctionFromHom` 构造：两侧 Hom 广集就是同一个基底 Hom
广集。互逆方程由自反性给出，来源自然性为纯值代入，目标自然性为 Kleisli
复合。正逆转置保留底层计算。单位为原 Monad 单位；`X` 处余单位为 `M X`
上的基底恒等，视为从 `M X` 到 `X` 的 Kleisli 箭头。两条三角律均继承自一般
伴随理论；输入只需普通 Monad。

`KleisliMonad` uses the existing `AdjunctionMonad`, without a second proof
of its Monad laws. Its unit agrees with the original unit by computation;
its multiplication agrees in designated Hom equality, using preservation
of identities by the original functor. The previous identity-component
functor isomorphism and its inverse preserve unit and multiplication.
`KleisliMonadTo` and `KleisliMonadFrom` package these as fixed-base Monad
morphisms; `KleisliMonadIso` is their actual isomorphism in the existing
`MonadCat C`. This compares complete Monad structures without equality of
functor functions, category records or law witnesses. It does not assert
an equivalence between all adjunctions and all Monads.

`KleisliMonad` 使用已有 `AdjunctionMonad`，不重新证明其 Monad 定律。单位通过
计算与原单位一致，乘法使用原函子保持恒等的定律，在指定 Hom 相等下与原乘法
一致。此前分量为恒等的函子同构及其逆均保持单位和乘法；`KleisliMonadTo` 与
`KleisliMonadFrom` 将其打包为固定基底 Monad 态射，`KleisliMonadIso` 是它们在
已有 `MonadCat C` 中的实际同构。这比较完整 Monad 结构，不要求函子函数、
范畴记录或定律见证相等，也不断言全部伴随与全部 Monad 之间的等价。

Temporary checks cover both strict hom/equality universe orders and a
case with objects strictly larger than both, the recovery isomorphism,
operation rewriting, preservation by both Monad morphisms and transpose
rewriting. Six transparent state computations cover recovered return,
mapping, multiplication, counit and both comparison maps. All 52 assumption
checks for this slice are closed under the global context. Abstract probes
import only this module and confirm that strength and product interfaces
are unavailable. No permanent tests or concrete model proofs were added;
computational Arrow is delivered below and Freyd remains separate work.

临时检查覆盖 Hom／相等宇宙的两种严格次序、对象严格大于两者的情形、恢复
同构、运算重写、双向 Monad 态射的保持性及转置重写。六项透明状态计算覆盖
恢复后的返回、映射、乘法、余单位及正反比较映射。本切片 52 项公理检查均无
额外假设；抽象检查仅导入本模块，并确认强度及积接口不可用。没有新增永久
测试或具体模型证明；计算 Arrow 见下文，Freyd 仍为后续工作。

This slice passed full-library build/tests/install with `rocq-cats`
(Rocq/Stdlib 9.2, Dune 3.23.1). Strict bilingual HTML generated 271 modules
per language and checked links and anchors in 547 pages; the new module's
explanations were inspected in both languages. Batch PDF export remains
with integration.

本切片使用 `rocq-cats`（Rocq／Stdlib 9.2、Dune 3.23.1）通过全库构建、测试
及安装；严格双语 HTML 为每种语言导出 271 个模块，检查 547 页的链接及锚点，
并核查两种语言中新模块的说明。批次 PDF 仍由集成会话统一导出。

## Arrow foundation over a monoidal base

## 幺半基底上的 Arrow 基础

[Arrow](../theories/Cat/Computational/Arrow/Core.v) now takes a named
monoidal base and a computation category, with a pure-arrow functor as
its unique underlying view. Its left-context action preserves pure maps
and composition, is natural in the ordinary context, and satisfies unit
and associator coherence. It assumes neither products nor symmetry nor
interchange of two effects. Computations live between images of the pure
functor; the existing `InducedCat` gives a presentation indexed by base
objects, and `ContextF` packages the action at a fixed context as a functor.

[Arrow](../theories/Cat/Computational/Arrow/Core.v) 输入具名幺半基底及计算范畴，
以纯箭头函子为唯一底层视图。左上下文作用保持纯映射及复合，在通常上下文中
自然，满足单位及结合子相干。不假定积、对称性或两个效应的交换律。计算位于
纯函子像之间；已有 `InducedCat` 给出以基底对象索引的呈现，`ContextF` 将固定
上下文的作用打包为函子。

[PureArrow](../theories/Cat/Computational/Arrow/Pure.v) uses ordinary left
tensoring. [KleisliArrow](../theories/Cat/Computational/Arrow/Kleisli.v)
uses the chosen tensorial strength of an ordinary strong Monad, retaining
its existing Kleisli category and pure functor. These are explicit models.
The construction reuses strength compatibility and coherence rather than
proving laws separately in each concrete model. The Haskell-style cartesian
operations and ordered Applicative comparison are delivered below.

[PureArrow](../theories/Cat/Computational/Arrow/Pure.v) 使用通常左张量；
[KleisliArrow](../theories/Cat/Computational/Arrow/Kleisli.v) 使用普通强 Monad
的选定张量强度，保留已有 Kleisli 范畴及纯函子。两者都是显式模型。构造复用
强度相容性及相干性，不为每个具体模型重复证明定律。Haskell 风格笛卡尔运算
及有序 Applicative 比较见下文。

The independent foundation passed full-library build/tests/install with
the existing `rocq-cats` switch. All 26 temporary assumption checks are
closed under the global context. Probes cover both strict hom/equality
orders, independent base/computation sizes and the fixed-context functor;
importing the foundation alone supplies no product interface. No permanent
tests were added.

独立基础在已有 `rocq-cats` switch 下通过全库构建、测试及安装。26 项临时公理
检查均无额外假设；覆盖 Hom／相等的两种严格次序、基底与计算范畴的独立大小
及固定上下文函子。仅导入此基础不提供积接口，没有新增永久测试。

## Cartesian Arrow operations and ordered comparison

## 笛卡尔 Arrow 运算及有序比较

[Cartesian Arrow operations](../theories/Cat/Computational/Arrow/Cartesian.v)
specialize the monoidal action to the named finite-product structure.
`second` is that existing action; `first` is derived by pure exchanges.
The pure identity/composition laws and the five classical `first` laws
(pure arrows, sequencing, projection, context naturality and associativity)
are proved, matching the seven basic laws in the official
[Control.Arrow documentation](https://hackage-content.haskell.org/package/base-4.20.0.0/docs/Control-Arrow.html#t:Arrow).
In particular, projection is derived from monoidal unit coherence and
naturality into the terminal context; it is not a new axiom. Ordered split
and fanout use context action and pure duplication; no joint bifunctoriality
or interchange of two effects is asserted. `Proper` supports rewriting all
these operations in the designated computation equality.

[笛卡尔 Arrow 运算](../theories/Cat/Computational/Arrow/Cartesian.v) 将幺半
作用特化到具名有限积结构；`second` 就是已有作用，`first` 通过纯交换导出。
纯恒等／复合定律及五条经典 `first` 定律（纯箭头、顺序组合、投影、上下文
自然性及结合律）均已证明，对应官方文档的七条基本定律。特别地，投影由幺半
单位相干及到终上下文的自然性导出，不是新公理。有序分开组合及扇出使用上下文
作用及纯复制，不断言联合双函子性或两个效应的交换；`Proper` 支持按指定计算
相等重写这些运算。

[The comparison](../theories/Cat/Computational/Arrow/Applicative.v) uses
one chosen strong Monad. It rewrites Kleisli `first` and `second` by
contextual binding, proves split equals the previous `monad_pair` after
the two input computations, and proves fanout equals Applicative pairing
in every shared ordinary context. Specializing to computation-valued inputs
recovers exactly the tensorator of `MonadA`; pure lifting uses the same
return. This is a comparison of these constructions, not a conversion of
arbitrary Arrows into Applicatives. Two reusable binding equations and the
existing sequencing simplifier now live in `Cat.Monad.Context`; the old
Applicative proof uses the same simplifier without changing its operations.
All proof-only opacity is local and restored.

[比较模块](../theories/Cat/Computational/Arrow/Applicative.v) 使用同一个选定
强 Monad，将 Kleisli 的 `first`／`second` 改写为上下文绑定，证明分开组合等于
此前的 `monad_pair` 在两个输入计算之后作用，并证明任意共同通常上下文中的
扇出等于 Applicative 配对。特化为计算值输入后，恰好恢复 `MonadA` 的 tensorator；
纯提升使用同一返回。这里只比较这些构造，不把任意 Arrow 转为 Applicative。
两条可复用绑定方程及已有顺序化简策略现归于 `Cat.Monad.Context`；旧 Applicative
证明使用同一策略，运算保持不变。全部证明专用不透明性均为局部且已恢复。

The explicit [StateArrow](../theories/Instance/Set/State.v) reuses
`StateStrongM` and the general Kleisli construction, with no model-specific
Arrow law proofs or global chosen-instance registration. Temporary checks
cover both strict base/computation hom-equality orders, both strict state
carrier/equality orders, all seven basic laws, operation rewriting and
comparison. Eight transparent state computations exercise pure, first,
second, split, fanout, reversed input order, repeated transitions and nested
context reassociation. The 68 cartesian/model assumption checks and 26
monoidal-foundation checks are all closed under the global context. All
148 earlier Applicative checks were rerun successfully after extracting the
shared simplifier. No permanent tests or shared test aliases were added.
Freyd, static Arrow, ArrowApply/Choice/Loop and Day/profunctor results remain
outside this slice; batch PDF export remains with integration.

显式 [StateArrow](../theories/Instance/Set/State.v) 复用 `StateStrongM` 及一般
Kleisli 构造，没有模型专用 Arrow 定律证明或全局选定实例注册。临时检查覆盖
基底／计算 Hom 相等的两种严格次序、状态载体／相等的两种严格次序、全部七条
基本定律、运算重写及比较。八项透明状态计算检验纯值、first、second、分开
组合、扇出、反向输入次序、重复转移及嵌套上下文重排。68 项笛卡尔／模型公理
检查与 26 项幺半基础检查均无额外假设；抽出共享化简策略后，原 148 项
Applicative 检查也全部重跑通过。没有新增永久测试或共享测试别名。Freyd、
静态 Arrow、ArrowApply／Choice／Loop 及 Day／profunctor 结果不在本切片范围内；
批次 PDF 仍由集成会话统一导出。

The final phase passed `dune build @all @runtest @install` with the existing
`rocq-cats` switch (Rocq/Stdlib 9.2, Dune 3.23.1). Strict bilingual HTML
export generated 276 modules per language and checked links and anchors in
557 pages; the new monoidal/cartesian/comparison explanations and State
model were inspected in both languages.

最终阶段在已有 `rocq-cats` switch（Rocq／Stdlib 9.2、Dune 3.23.1）下通过
`dune build @all @runtest @install`；严格双语 HTML 为每种语言生成 276 个模块，
检查 557 页的链接及锚点，并核查两种语言中新增的幺半／笛卡尔／比较说明及
状态模型。

## First implementation boundary

## 首个实现边界

1. Bundle a functor and its lax structure between two specified monoidal
   structures. Retain a unit map and a natural tensorator with
   associativity and both unit laws. Do not require invertibility, a
   strength, or a closed/cartesian base.
2. Prove the generic monoid transport once: `e' = F(e) ∘ φ₀` and
   `m' = F(m) ∘ φ₂`. Map homomorphisms by `fmap F` and package the functor
   between the existing monoid-object categories.
3. Check a genuinely noninvertible lax structure, independent hom/equality
   universe orders, and foundational assumptions. Keep temporary checks
   distinct from retained interface regressions.
4. Lawful Applicative, coherent operation comparison, tensorial strength and
   the ordered strong-Monad conversion, computational Arrow and its ordered
   pairing comparison above are implemented. Freyd, static-arrow and deeper
   representation results remain open in #35.

1. 打包指定幺半结构之间的函子及其 lax 结构：单位映射、自然 tensorator、
   结合律和两条单位律。不要求可逆、张量强度或闭／笛卡尔基底。
2. 通用地证明一次幺半群传输：`e' = F(e) ∘ φ₀`、`m' = F(m) ∘ φ₂`；
   用 `fmap F` 映射同态，并封装为已有幺半群对象范畴之间的函子。
3. 检查真正不可逆的 lax 结构、独立的 Hom／相等宇宙次序，以及基础公理。
   区分临时检查与保留的接口回归。
4. 上述带定律 Applicative、相干运算比较、张量强度、强 Monad 有序转换、计算
   Arrow 及其有序配对比较已实现。Freyd、静态 Arrow 及更深表示结果仍为 #35
   的待办。

The implemented interface is
[LaxMonoidalFunctor MC MD](../theories/Cat/Monoidal/Functor.v), bundling
the underlying functor through `LaxMonoidalF :> Functor C D`. Clients use
`L X` and `fmap L f`; comparison notation is `φ₀[L]` and `φ₂[L; X; Y]`
in `monoidal_scope`.
[ConstF_LaxMonoidalFunctor](../theories/Cat/Monoidal/Constant.v) supplies
a general constant example from any target monoid. Chosen identity and
constant structures are definitions that clients select explicitly.
[LaxMonoidF](../theories/Cat/Monoidal/Transport.v) maps the existing monoid
category by `fmap L`, retaining designated equality and Type-valued witnesses.
This induced functor remains a derived construction, rather than a second
coercion from the lax structure. The broader interface survey is recorded in
[BundledInterfaces.md](./BundledInterfaces.md).

已实现的接口为
[LaxMonoidalFunctor MC MD](../theories/Cat/Monoidal/Functor.v)，
用 `LaxMonoidalF :> Functor C D` 打包底层函子，客户端使用 `L X`、`fmap L f`。
`monoidal_scope` 中的比较记号为 `φ₀[L]`、`φ₂[L; X; Y]`。
[ConstF_LaxMonoidalFunctor](../theories/Cat/Monoidal/Constant.v) 从任意目标
幺半群给出通用常值实例。恒等及常值结构均为须由客户端显式选择的定义。
[LaxMonoidF](../theories/Cat/Monoidal/Transport.v) 用 `fmap L` 映射已有幺半群
对象范畴，保留指定相等及 Type 值见证。诱导函子仍为派生构造，不作为 lax
结构的第二条强制转换。全库接口调查记录在
[BundledInterfaces.md](./BundledInterfaces.md)。

Retained regressions check that the Boolean-xor constant functor's unit
and tensor comparisons are not invertible, that transported operations
compute, and that transport works in both directions between categories
with `e < h < p` hom/equality levels. See
[Computations.v](../tests/Computations.v) and
[Universes.v](../tests/Universes.v).

保留的回归检查布尔异或常函子的单位比较与 tensorator 均不可逆、传输运算可
直接计算，以及在满足 `e < h < p` 的 Hom／相等层级范畴间双向传输。见
[Computations.v](../tests/Computations.v) 及
[Universes.v](../tests/Universes.v)。

[w]: https://github.com/jwiegley/category-theory/tree/99869fd8d9117e900dea862d8612033848aa01dd
[w-app]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Theory/Coq/Applicative.v
[w-app-proofs]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Theory/Coq/Applicative/Proofs.v
[w-capp]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Functor/Applicative.v
[w-lax]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Functor/Structure/Monoidal.v
[w-pure]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Functor/Structure/Monoidal/Pure.v
[w-coq]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Instance/Coq.v
[w-strong]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Monad/Strong.v
[w-kprem]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Monad/Kleisli/Premonoidal.v
[w-freyd]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/Premonoidal/Freyd.v
[w-day]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Day.v
[w-coend]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Instance/Sets/Coend.v
[w-prof]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Theory/Profunctor.v
[w-prof-comp]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Profunctor/Compose.v
[w-prof-laws]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Profunctor/Laws.v
[w-cayley]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Cayley.v
[m]: https://github.com/leanprover-community/mathlib4/tree/9bac2d0692944a775113f7c130fd5e5b4608a854
[m-app]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/Control/Applicative.lean
[m-lax]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/Functor.lean
[m-mon]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/Mon.lean
[m-day]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/DayConvolution.lean
[m-day-closed]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/DayConvolution/Closed.lean
[l]: https://github.com/leanprover/lean4/tree/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a
[l-lawful]: https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/src/Init/Control/Lawful/Basic.lean
[a]: https://github.com/agda/agda-categories/tree/ade267a5a02688fb97ec9d6e03ab6192be94439e
[a-lax]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Functor/Monoidal.agda
[a-strong]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Monad/Strong.agda
[a-mon]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Object/Monoid.agda
[a-kl]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Category/Monoidal/Construction/Kleisli.agda
[u]: https://github.com/UniMath/UniMath/tree/7a4b03cce49449f45ce0d4285615165172f50546
[u-lax]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/Functors.v
[u-strong]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/StrongMonad.v
[u-mon]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/CategoriesOfMonoids.v
[u-kl]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monads/Kleisli.v
[u-mm]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/Examples/MonadsAsMonoidsElementary.v
[paper]: https://arxiv.org/abs/1406.4823v1

## Two-sided context and centrality prerequisite

## 双侧上下文与中心性前置基础

The user-approved serial slice starts from `751de86` on `monoidal-cat-view`.
The existing generic Arrow has a left-context action over a named monoidal
base; that alone does not specify a right-context action. This slice
extracts [BinoidalCat](../theories/Cat/Binoidal/Core.v): one object tensor
and two separately functorial arrow actions, without units, associators,
symmetry or effect interchange. Derived fixed-context functors share that
same object tensor. Public `binoidal_scope` notation writes the tensor as
`X ⊗ Y`, left context as `Z ⊲ f`, and right context as `f ⊳ Z`.

用户授权的串行批次从 `monoidal-cat-view` 上的 `751de86` 开始。现有一般
Arrow 在具名幺半基底上具有左上下文作用，但这本身尚未指定右上下文作用。
本批抽出 [BinoidalCat](../theories/Cat/Binoidal/Core.v)：唯一对象张量与两种
分别具有函子性的态射作用，不要求单位元、结合子、对称性或效应交换律。
导出的固定上下文函子共享同一对象张量。公开 `binoidal_scope` 中，张量写作
`X ⊗ Y`，左上下文写作 `Z ⊲ f`，右上下文写作 `f ⊳ Z`。

[Centrality](../theories/Cat/Binoidal/Center.v) is a Type-valued predicate
on an arrow: it supplies exchange with every partner, in either tensor
position. Specified-equal arrows share centrality, and central arrows are
closed under identity and composition. Ordered sequencing agrees with the
opposite execution order when either factor is central. There is no
principle asserting this for two arbitrary effects.

[中心性](../theories/Cat/Binoidal/Center.v) 是态射上的 Type 值谓词，在两个
张量位置都给出与任意另一态射交换的见证。指定相等的态射共享中心性，中心
态射在恒等与复合下封闭。任一因子为中心态射时，有序组合与相反执行次序
相等；没有断言两个任意效应都可如此交换。

[MonoidalBinoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Binoidal.v) explicitly adapts
an existing monoidal tensor, with all arrows central by bifunctoriality.
It is not another coercion or globally chosen parent of MonoidalCat.
[ArrowBinoidal](../theories/Cat/Computational/Arrow/Binoidal.v) reuses
`ComputationCat A`, the selected value products and existing `first`/`second`
operations. `ArrowPureF` is identity on the shared value-object type and
reuses the original pure-arrow action. Both old context-naturality laws
prove that every pure arrow is central. Generic ordered sequencing agrees
with the existing Arrow split. No concrete model laws are reproved.

[MonoidalBinoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Binoidal.v) 显式适配已有幺半张量，
由双函子性证明全部态射为中心态射；它不是 MonoidalCat 的另一强制转换或
全局选定父结构。
[ArrowBinoidal](../theories/Cat/Computational/Arrow/Binoidal.v) 复用
`ComputationCat A`、选定值积及已有 `first`／`second` 运算。`ArrowPureF`
在共享值对象类型上为恒等，并复用原纯态射作用。已有两种上下文自然性律证明
每个纯态射都是中心态射；一般有序组合与原 Arrow split 一致。不重复证明
具体模型的定律。

The adapter fixes the value-category product explicitly even though value
and computation objects have the same type. Right-context action currently
uses the existing cartesian exchange. The general binoidal foundation
requires no symmetry, but extending the one-sided generic Arrow to two
sides over a weaker base needs extra data or a coherent exchange structure.
At this checkpoint, full premonoidal structural isomorphisms and coherence,
symmetric structure, and the complete Freyd characterization were still
later tasks. The next slice below supplies the general premonoidal layer.
The pinned [Wiegley binoidal interface](https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/Binoidal.v)
was rechecked alongside the cached premonoidal/Freyd sources; the existing
prior-art and compatibility boundaries above still apply.

尽管值对象和计算对象具有同一类型，适配器仍显式固定值范畴的积选择。右上下文
作用目前使用已有笛卡尔交换。一般双侧张量基础不要求对称性，但在更弱基底上
将只有单侧作用的一般 Arrow 扩展为双侧，需要额外数据或相干交换结构。
在此前置阶段，完整预幺半结构同构与相干、对称结构及完整 Freyd 刻画仍为
后续任务。下一个批次补齐一般预幺半层。
固定版本的 [Wiegley 双侧张量接口](https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/Binoidal.v)
已与缓存的预幺半／Freyd 源码一起复核，上述既有先例与相容边界继续适用。

Validation used the existing `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 73 temporary `Print Assumptions` checks reported
`Closed under the global context`: both strict hom/equality universe
orders, independent value/computation hom equalities, centrality rewriting,
explicit model choices, both State carrier/equality orders and concrete
pure/context/sequence reductions were checked. The State example proves
that changing state before reading differs from reading before changing,
and that the changing computation is not central. These are temporary
checks, with no permanent test or shared test configuration changes.

验证使用已有 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1）。全库 `dune build @all @runtest @install` 通过。73 项临时
`Print Assumptions` 检查均报告 `Closed under the global context`，覆盖
Hom／相等的两种严格宇宙次序、值／计算 Hom 相等的独立大小、中心性重写、
显式模型选择、State 载体／相等的两种次序，以及具体纯映射／上下文／组合
归约。State 示例证明先改变状态再读取与先读取再改变不同，且改变状态的计算
不是中心态射。这些均为临时检查，没有新增永久测试或修改共享测试配置。

Strict bilingual HTML generated 287 modules per language and checked
links/anchors in 579 pages. All four new interface/adapter pages were
inspected in both languages. Batch PDF export and updating `typeprop`
remain with the integration session. The delivered foundation is ready
for independent integration before further premonoidal/Freyd work.

严格双语 HTML 每种语言生成 287 个模块，检查 579 页的链接／锚点；四个新增
接口／适配器页面均核对英中文。批次 PDF 导出及 `typeprop` 更新仍由集成会话
负责。本基础已可独立集成，无须等待后续预幺半／Freyd 工作。


## Premonoidal structure prerequisite

## 预幺半结构前置基础

This user-approved serial slice starts from `3fc3ffb` on `monoidal-cat-view`.
[PremonoidalCat](../theories/Cat/Premonoidal/Core.v) inherits one binoidal
structure through `PremonoidalB :> BinoidalCat C`, with the same projection
registered for instance search. It adds a chosen unit, central associator
and unitors, their separate naturality, and pentagon/triangle coherence.
Carrier, hom and equality sizes remain independent; all equality and
centrality witnesses remain Type-valued. No structural operations or
underlying category are selected a second time.

用户授权的本串行批次从 `monoidal-cat-view` 上的 `3fc3ffb` 开始。
[PremonoidalCat](../theories/Cat/Premonoidal/Core.v) 通过
`PremonoidalB :> BinoidalCat C` 继承唯一双侧张量结构，同一投影注册为继承
实例。新增选定单位对象、中心结合子与单位子、它们的分别自然性，以及五边形／
三角形相干。载体、Hom 与相等大小保持独立；所有相等及中心性见证保持为
Type 值。不再次选取结构运算或底层范畴。

The general [inverse-square lemma](../theories/Cat/Isomorphism.v) inverts
the vertical isomorphisms of any commuting square using specified hom
equality. [Centrality of an inverse](../theories/Cat/Binoidal/Center.v)
uses that lemma with the fixed-context functors. The
[premonoidal inverse laws](../theories/Cat/Premonoidal/Laws.v) derive all
three inverse centrality witnesses and all five inverse naturality
squares. Forward and inverse maps are projections of the same selected
isomorphisms; inverse centrality/naturality are not duplicate class fields.
Public `premonoidal_scope` notation exposes the unit and both directions
of each structural map; object tensor and contexts retain binoidal notation.

一般[逆方块引理](../theories/Cat/Isomorphism.v) 使用指定 Hom 相等，对任意
交换方块的竖直同构取逆。[逆的中心性](../theories/Cat/Binoidal/Center.v)
将该引理应用于固定上下文函子。
[预幺半逆向定律](../theories/Cat/Premonoidal/Laws.v) 导出全部三种逆中心性
见证及五个逆自然性方块。正逆映射都是同一选定同构的投影；逆中心性／自然性
不作为重复类字段保存。公开 `premonoidal_scope` 记号提供单位对象及每种
结构映射的两个方向；对象张量及上下文沿用双侧张量记号。

[MonoidalPremonoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Premonoidal.v) is an explicit
client of the new layer. It reuses `MonoidalBinoidal`, the original unit,
associator/unitors and their inverse components. Separate naturality
specializes existing joint naturality; existing coherence is reused.
The old `MonoidalCat` interface and all concrete model constructors remain
available in their existing form. Migrating its parent and deriving the
bifunctor from interchange is a later bounded task. Constructing the
computational Arrow premonoidal structure, symmetric/Freyd interfaces and
the full characterization also remain open. No concrete model laws are
reproved here.

[MonoidalPremonoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Premonoidal.v) 是新层的显式
客户端，复用 `MonoidalBinoidal`、原单位对象、结合子／单位子及其逆分量。
分别自然性特化已有联合自然性，相干性复用原定律。原 `MonoidalCat` 接口及
全部具体模型构造维持已有形式。迁移其父结构并由交换律导出双函子属于后续
有限任务。构造计算 Arrow 的预幺半结构、对称／Freyd 接口及完整刻画仍待
完成。本批没有重新证明具体模型定律。

Validation uses the existing `rocq-cats` switch: Rocq/Stdlib 9.2.0,
OCaml 5.3.0 and Dune 3.23.1. Full `dune build @all @runtest @install`
passed. All 63 new temporary `Print Assumptions` probes and all 73 repeated
binoidal/Arrow probes reported `Closed under the global context`.
The new probes check the inherited coercion/instance chain, both strict
hom/equality universe orders, multiple explicit structures on one category,
absence of globally selected models, transparent forward/inverse
associator/unitor reductions, and inverse centrality of a nonidentity
isomorphism. The prior State order counterexample and its noncentral
effect remain valid. These checks are temporary; no permanent tests or
shared test configuration were changed.

验证使用已有 `rocq-cats` switch：Rocq／Stdlib 9.2.0、OCaml 5.3.0 及
Dune 3.23.1。全库 `dune build @all @runtest @install` 通过。63 项新增
临时 `Print Assumptions` 探针及重跑的 73 项双侧张量／Arrow 探针均报告
`Closed under the global context`。新增探针检查继承转换／实例链、Hom 与
相等的两种严格宇宙次序、同范畴上的多个显式结构、没有全局选定模型、
正逆结合子／单位子的透明归约，以及非恒等同构的逆中心性。原 State 次序
反例及其非中心效应继续成立。这些检查均为临时检查，没有新增永久测试或
修改共享测试配置。

Strict bilingual HTML generated 290 modules per language and checked
links/anchors in 585 pages. All three new pages were inspected in both
languages, together with the added general-lemma anchors. The structural
inventory covers all 91 interfaces exactly once (64 classes, 27 records).
Batch PDF export and `typeprop` integration remain with the integration
session; this foundation can be integrated independently.

严格双语 HTML 每种语言生成 290 个模块，检查 585 页的链接／锚点。三个新增
页面均抽查英中文正文，同时检查新增一般引理的锚点。结构清单恰好覆盖全部
91 个接口各一次（64 个类、27 个记录）。批次 PDF 导出与 `typeprop` 集成
仍由集成会话负责；本基础可独立集成。


## Monoidal parent migration

## 幺半父结构迁移

This user-authorized serial slice starts from `0a41be9` on
`monoidal-cat-view`. [MonoidalCat](../theories/Cat/Monoidal/Core.v) now
inherits one `PremonoidalCat C` through `MonoidalP :>`, exported as the
inherited instance. A single interchange equation supplies centrality
for every arrow; the other centrality square is obtained by swapping
arguments. The stored tensor bifunctor and direct category bypass are
removed. The derived tensor functor sequences the inherited actions,
while unit, associator/unitors, inverse components and coherence come
from the same parent.

本用户授权的串行批次从 `monoidal-cat-view` 上的 `0a41be9` 开始。
[MonoidalCat](../theories/Cat/Monoidal/Core.v) 现在通过 `MonoidalP :>` 继承
唯一 `PremonoidalCat C`，并导出同一父实例。一条交换方程给出每条态射的
中心性；另一中心性方块通过交换参数得到。不再保存张量双函子，也不保留
直达范畴的旁路。导出张量函子顺序组合继承作用；单位、结合子／单位子、
逆分量及相干性均来自同一父结构。

Two proofs use weaker hypotheses than monoidal structure:
[central_sequence_comp](../theories/Cat/Binoidal/Center.v) needs centrality
only of the crossing arrow, and
[premonoidal_assoc_sequence_natural](../theories/Cat/Premonoidal/Laws.v)
uses only separate premonoidal naturality. The monoidal tensor functor
and joint associator naturality reuse these proofs. Derived natural
isomorphisms retain the original inverse components rather than storing
new choices.

两项证明使用比幺半结构更弱的前提：
[central_sequence_comp](../theories/Cat/Binoidal/Center.v) 只要求需要交换的
那条态射的中心性；
[premonoidal_assoc_sequence_natural](../theories/Cat/Premonoidal/Laws.v)
只使用预幺半的分别自然性。幺半张量函子及结合子的联合自然性复用这些证明。
导出自然同构保留原逆分量，不保存新的选择。

[BifunctorBinoidal](../theories/Cat/Binoidal/Bifunctor.v) extracts separate
actions from any tensor bifunctor. The
[BifunctorMonoidal](../theories/Cat/Monoidal/Bifunctor.v) assembly constructor
then reuses supplied natural structural isomorphisms and two coherence
proofs. It supplies a natural isomorphism between its derived tensor and
the original bifunctor, with identity components. The two concrete model
families (cartesian and bicategory endomorphism, hence endofunctors) use
this shared constructor; there is no staging data record or equality of
functor/law records. The transitional `MonoidalBinoidal` and
`MonoidalPremonoidal` adapters from earlier milestones are removed in
favor of the inherited projections.

[BifunctorBinoidal](../theories/Cat/Binoidal/Bifunctor.v) 从任意张量双函子
抽出分别作用；
[BifunctorMonoidal](../theories/Cat/Monoidal/Bifunctor.v) 装配器再复用给定
自然结构同构及两个相干证明，并通过恒等分量给出导出张量与原双函子的自然
同构。两个具体模型族（笛卡尔及双范畴自同态，包括自函子）复用此构造器，
没有分阶段数据记录或函子／定律记录的相等。先前批次中的过渡适配器
`MonoidalBinoidal`、`MonoidalPremonoidal` 已删除，由继承投影替代。

Cartesian and endomorphism comparison laws adapt weaker clients using
specified equality. [CartesianLifting](../theories/Cat/Monoidal/CartesianLifting.v)
transports generic lax lifting results without adding pure maps,
exponentials or strength. Applicative, Monad, strength and Arrow clients
use these comparisons; tensorator natural transformations have the same
derived tensor functor at their endpoints. Monad–monoid functors keep
the underlying arrow and transport its Type-valued preservation witness.
At this milestone computational Arrows had only their binoidal structure;
no interchange for arbitrary State effects was inferred. The following
batch supplies their premonoidal structure; symmetric/Freyd structure and
translations remain open.

笛卡尔及自同态比较定律使用指定相等适配较弱客户端。
[CartesianLifting](../theories/Cat/Monoidal/CartesianLifting.v) 运输一般
lax 提升结果，不增加纯值映射、指数或强度。Applicative、Monad、强度及
Arrow 客户端使用这些比较；tensorator 自然变换的两端使用同一导出张量函子。
Monad–幺半群函子保持底层态射，运输其 Type 值保持性见证。在该阶段，计算
Arrow 仍只具有已构造的双侧张量结构，不由此推出任意 State 效应的交换律。
下一批补充其预幺半结构；对称／Freyd 结构及其翻译仍待完成。


Validation used the existing `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed, including the unchanged interface, universe and computation tests.
All 212 temporary `Print Assumptions` checks were closed under the global
context: 76 new monoidal-parent checks and 136 adapted premonoidal/binoidal
checks. They cover both strict hom/equality universe orders, the full
inherited coercion/instance chain, reconstruction of existing monoidal
structures and tensor natural-isomorphism comparison, explicit model
selection, transparent tensor/structure/inverse reductions and the
unchanged State order counterexample. No permanent tests or shared test
configuration were changed. The existing `AGENTS.md` learning section now
records the comparison and tensorator-endpoint discipline.

验证使用已有 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1）。全库 `dune build @all @runtest @install` 通过，包括未修改
的接口、宇宙及计算测试。全部 212 项临时 `Print Assumptions` 检查均无额外
全局假设：新增幺半父层检查 76 项，适配后的预幺半／双侧张量检查 136 项。
覆盖 Hom／相等的两种严格宇宙次序、完整继承转换／实例链、已有幺半结构
重建与张量自然同构比较、显式模型选择、张量／结构／逆的透明归约，以及
原有 State 次序反例。没有新增永久测试或修改共享测试配置。已有
`AGENTS.md` 的经验部分补充了比较定律与 tensorator 端点选择规范。

Strict bilingual HTML generated 291 modules per language and checked
links/anchors in 587 pages. The monoidal core, all three new modules and
the added premonoidal sequence law were inspected in both languages.
The inventory still covers all 91 interfaces exactly once (64 classes,
27 records), with all 29 `Has*` classes retained. Batch PDF export and
`typeprop` integration remain with the integration session.

严格双语 HTML 每种语言生成 291 个模块，检查 587 页的链接／锚点。幺半核心、
全部三个新增模块及新增预幺半有序组合定律均抽查英中文。清单仍恰好覆盖全部
91 个接口各一次（64 个类、27 个记录），保留全部 29 个 `Has*` 类。批次 PDF
导出及 `typeprop` 集成仍由集成会话负责。

## Computational Arrow premonoidal structure

## 计算 Arrow 的预幺半结构

This user-authorized serial batch starts from `1b341ec` on
`monoidal-cat-view`. [ArrowPremonoidal](../theories/Cat/Computational/Arrow/Premonoidal.v)
constructs a `PremonoidalCat (ComputationCat A)` for a computational Arrow
over the cartesian monoidal structure supplied by named terminal and
product choices. Its parent is exactly the existing `ArrowBinoidal A`:
the object tensor, equality and both context operations are inherited,
without new choices or a direct ancestor bypass.

本用户授权的串行批次从 `monoidal-cat-view` 上的 `1b341ec` 开始。
[ArrowPremonoidal](../theories/Cat/Computational/Arrow/Premonoidal.v)
为具名终对象及积选择给出的笛卡尔幺半结构上的计算 Arrow，构造
`PremonoidalCat (ComputationCat A)`。父结构恰好为已有 `ArrowBinoidal A`：
对象张量、相等及两种上下文运算全部继承，不增加选择或直达祖先的旁路。

The associator and both unitors, including their inverse maps, are pure
images of the same selected value isomorphisms through `ArrowPureF A`.
The existing `functor_is_iso` theorem supplies the inverse equations;
`arrow_pure_central` supplies all three centrality witnesses. Unit
naturality reuses the two projection laws. The associator's left/right
naturality reuses `arrow_first_assoc` and `arrow_context_assoc`; the new
[arrow_middle_assoc](../theories/Cat/Computational/Arrow/Cartesian.v)
proves middle naturality from nested left contexts and ordinary context
exchange. It never exchanges two effectful computations. Pentagon and
triangle are the functorial images of existing value coherence, without
reproving product coherence or individual model laws. All inverse
centrality and naturality laws then follow from the general premonoidal
theory, with no duplicate structure fields.

结合子及两个单位子，包括其逆映射，均为同一选定值同构沿 `ArrowPureF A`
的纯像。已有 `functor_is_iso` 定理提供互逆方程，`arrow_pure_central`
提供三种中心性见证。单位子自然性复用两个投影律；结合子左右自然性复用
`arrow_first_assoc` 及 `arrow_context_assoc`。新增
[arrow_middle_assoc](../theories/Cat/Computational/Arrow/Cartesian.v)
从嵌套左上下文及通常上下文交换证明中间自然性，不交换两个带效应计算。
五边形及三角形来自已有值相干性的函子像，不重复证明积相干性或各个模型
的定律。全部逆向中心性及自然性随后由一般预幺半理论导出，不增加重复字段。

The construction is explicitly selected and requires neither exponentials
nor commutativity. It applies directly to the existing pure and strong
Monad/Kleisli Arrow models, including State. This batch does not supply a
general noncartesian right action, symmetric/Freyd interfaces or an
Arrow–Freyd equivalence; those are subsequent tasks. In particular,
the unchanged Boolean-state toggle/read example still distinguishes
execution order and supplies a noncentral computation in this very
premonoidal structure.

本构造必须显式选择，不要求指数对象或交换性，可直接应用于已有纯计算及强
Monad／Kleisli Arrow 模型，包括 State。本批没有为一般非笛卡尔情形提供
右作用，也没有构造对称／Freyd 接口或 Arrow–Freyd 等价；这些属于后续任务。
尤其是原有布尔状态切换／读取示例，在这个预幺半结构中仍能区分执行次序，
并提供非中心计算。

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 79 temporary `Print Assumptions` checks were closed under
the global context. These checks cover both strict hom/equality universe
orders, separately sized value/computation object and hom universes,
the exact inherited parent and its instance search, pure preservation of
both associator directions, both strict state carrier/equality orders,
transparent structural maps/inverses and the original observable-order
and noncentrality counterexamples. Concrete clients specify the computation
category explicitly where value and computation objects share a type;
object arguments alone do not determine the ambient hom-set.

验证使用未修改的 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1）。全库 `dune build @all @runtest @install` 通过，全部
79 项临时 `Print Assumptions` 检查均无额外全局假设。覆盖 Hom／相等的
两种严格宇宙次序、值与计算对象及 Hom 宇宙的分别定级、完全相同的继承父层
及实例搜索、结合子正逆两个方向的纯保持性、状态载体／相等的两种严格次序、
结构映射／逆的透明计算，以及原有可观察次序与非中心性反例。当值与计算对象
共享类型时，具体客户端显式指定计算范畴；仅凭对象参数不能确定所在 Hom 集。

Strict bilingual HTML generated 292 modules per language and checked
589 pages. The new module, middle-context lemma, both language texts and
public symbol anchors were inspected. The inventory still covers all
91 class/record interfaces exactly once (64 classes, 27 records), with
all 29 `Has*` classes retained. No permanent tests or shared test
configuration were added or changed. This task-branch foundation is ready
for independent integration; `typeprop` and batch PDF export remain with
the integration session.

严格双语 HTML 每种语言生成 292 个模块，检查 589 页。抽查新增模块、
中间上下文引理、两种语言正文及公开符号锚点。清单仍恰好覆盖全部 91 个类／
记录接口各一次（64 个类、27 个记录），保留全部 29 个 `Has*` 类。没有新增
永久测试或修改共享测试配置。本任务分支基础已可独立集成；`typeprop` 及
批次 PDF 导出仍由集成会话负责。

## Symmetric contexts and Freyd foundation

## 对称上下文与 Freyd 基础

This user-authorized serial batch starts from `4098284` on
`monoidal-cat-view`. The classical conditions were rechecked against
[Jacobs–Heunen–Hasuo, definitions 6.2–6.4](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/35C603B99F43CBD8109C97FA51BDAB23/S0956796809007308a.pdf/categorical_semantics_for_arrows.pdf)
and [Selinger, section 2.1](https://www.mscs.dal.ca/~selinger/papers/control.pdf).
The interface includes finite-product values, symmetric premonoidal
computations, a central identity-on-objects inclusion and strict
preservation. It does not use the weaker third-party effectful interface
as a substitute for these requirements.

本用户授权的串行批次从 `monoidal-cat-view` 上的 `4098284` 开始。经典
条件与 [Jacobs–Heunen–Hasuo 定义 6.2–6.4](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/35C603B99F43CBD8109C97FA51BDAB23/S0956796809007308a.pdf/categorical_semantics_for_arrows.pdf)
及 [Selinger 第 2.1 节](https://www.mscs.dal.ca/~selinger/papers/control.pdf)
重新核对。接口包括有限积值结构、对称预幺半计算结构、对象上恒等的中心
嵌入及严格保持性，没有以较弱的第三方 effectful 接口替代这些条件。

[SymmetricPremonoidalCat](../theories/Cat/Premonoidal/Symmetric.v)
inherits exactly one premonoidal parent. It stores central exchange,
involution, left-variable naturality, the hexagon and unit compatibility.
The symmetry isomorphism uses the opposite exchange as its transparent
inverse; right-variable naturality follows by inverting the first square.
A derived conjugation law recovers right action from left action.
[CartesianSymmetricPremonoidal](../theories/Cat/Premonoidal/Cartesian.v)
inherits the existing cartesian monoidal parent's premonoidal structure,
proving only the new exchange equations from products.

[SymmetricPremonoidalCat](../theories/Cat/Premonoidal/Symmetric.v) 恰好
继承一个预幺半父结构，保存中心交换、对合、左变量自然性、六边形及单位
相容性。对称同构以反序交换为透明逆；右变量自然性通过对第一个方块取逆
得到。导出的共轭律从左作用恢复右作用。
[CartesianSymmetricPremonoidal](../theories/Cat/Premonoidal/Cartesian.v)
继承已有笛卡尔幺半父层的预幺半结构，仅从积证明新增交换方程。

[ArrowSymmetricPremonoidal](../theories/Cat/Computational/Arrow/Symmetric.v)
retains exactly `ArrowPremonoidal A`. Exchange is pure product exchange,
central by `arrow_pure_central`. Its naturality follows from the existing
right-context definition and involutive pure exchange. Hexagon and unit
coherence are functorial images of the generic cartesian symmetry laws;
no separate Reader or State coherence proofs are added. Symmetry exchanges
context positions without exchanging the execution of two effects.

[ArrowSymmetricPremonoidal](../theories/Cat/Computational/Arrow/Symmetric.v)
保留完全相同的 `ArrowPremonoidal A`。交换为纯积交换，其中心性来自
`arrow_pure_central`；自然性来自已有右上下文定义及纯交换对合律。六边形
及单位相干性为一般笛卡尔对称定律的函子像，不增加 Reader 或 State 的
独立相干证明。对称性交换上下文位置，不交换两个效应的执行次序。

[FreydCat](../theories/Cat/Computational/Freyd/Core.v) bundles the pure
ambient functor with chosen cartesian values and symmetric premonoidal
computations. Its actual computation category is the existing induced
category indexed by value objects. `FreydPureF` therefore has identity
object map by construction; arbitrary unused ambient objects are not
claimed to belong to this Freyd category. The reusable
[InducedF](../theories/Cat/Induced.v) supplies this factorization and now
also supplies the existing `ArrowPureF`, keeping its arrow/object maps.
No equality of object-map functions or bijection of ambient object types
is required.

[FreydCat](../theories/Cat/Computational/Freyd/Core.v) 将纯环境函子与
选定笛卡尔值结构、对称预幺半计算结构打包。实际计算范畴为按值对象索引的
已有诱导范畴，因此 `FreydPureF` 的对象映射按构造为恒等；不主张任意未
使用的环境对象都属于这个 Freyd 范畴。可复用
[InducedF](../theories/Cat/Induced.v) 提供此分解，现在也提供已有
`ArrowPureF`，保留其态射／对象映射。无需对象映射函数的相等或环境对象
类型之间的双射。

Strict object preservation retains explicit tensor/unit equality
witnesses. The existing `eq_to_hom` operation supplies every boundary
transport. Context preservation, both unitors, both nested associator
boundaries and symmetry use those same witnesses coherently, and every
arrow equation uses specified Hom equality. There is no UIP, function
extensionality, proof irrelevance or identification of law records.
[ArrowFreyd](../theories/Cat/Computational/Arrow/Freyd.v) reuses the
same pure functor, finite-product choices and symmetric computation
parent. All its object equalities are reflexive, so boundary transports
compute to identities; preservation reuses the existing Arrow laws.

严格对象保持性保留显式张量／单位相等见证。已有 `eq_to_hom` 运算提供每个
边界运输。上下文保持性、两个单位子、结合子的两个嵌套边界及对称性相干地
使用同一批见证，所有态射方程均使用指定 Hom 相等。没有使用 UIP、函数
外延性、证明无关性或定律记录的相等。
[ArrowFreyd](../theories/Cat/Computational/Arrow/Freyd.v) 复用同一纯
函子、有限积选择及对称计算父层。其全部对象相等均自反，因此边界运输计算
为恒等；保持性复用已有 Arrow 定律。

This delivers the symmetric/Freyd interfaces and the forward
computational Arrow-to-Freyd construction. Reverse translation, explicit
round-trip comparisons and their precise categorical equivalence level
remain open. No full Arrow/Freyd correspondence, ordinary-arrow-category
change, closed Freyd/ArrowApply result or general noncartesian right
action is claimed. All model structures remain explicitly selected.

本批交付对称／Freyd 接口及计算 Arrow 到 Freyd 的正向构造。逆向翻译、
显式往返比较及其精确范畴等价层级仍待完成。不主张完整 Arrow／Freyd
对应，不修改通常箭头范畴，也不提供闭 Freyd／ArrowApply 结果或一般非
笛卡尔右作用。所有模型结构仍须显式选择。

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 169 temporary assumption checks were closed under the global
context: 90 new symmetric/Freyd checks and the 79 premonoidal checks rerun
after extracting `InducedF`. They cover both strict hom/equality universe
orders, separately sized value/computation objects and hom-sets, both
strict state carrier/equality orders, inherited coercions/instances,
identity-on-objects inclusion, exact shared structure choices, transparent
exchange/inverse/boundary computations, structural preservation and the
unchanged State order/noncentrality counterexamples. Imports do not select
a default symmetric or Freyd model. No permanent tests or shared test
configuration were changed.

验证使用未修改的 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1）。全库 `dune build @all @runtest @install` 通过；全部
169 项临时公理检查均无额外全局假设，其中新增对称／Freyd 检查 90 项，
提取 `InducedF` 后重跑预幺半检查 79 项。覆盖 Hom／相等的两种严格宇宙
次序、值／计算对象及 Hom 广集的分别定级、状态载体／相等的两种严格次序、
继承转换／实例、对象上恒等的嵌入、完全共享的结构选择、交换／逆／边界的
透明计算、结构保持性，以及原有 State 次序／非中心性反例。导入不选定
默认对称或 Freyd 模型。没有修改永久测试或共享测试配置。

Strict bilingual HTML generated 297 modules per language and checked
599 pages. All five new module texts, interface-field anchors and the
shared `InducedF` documentation were inspected in both languages. The
inventory covers all 93 interfaces exactly once (66 classes, 27 records),
retaining all 29 `Has*` classes. The existing `AGENTS.md` learning section
records object-indexed inclusions, explicit ambient-category inference and
consistent boundary witnesses. This foundation is ready for independent
integration before the reverse translation; `typeprop` and batch PDFs
remain with integration.

严格双语 HTML 每种语言生成 297 个模块，检查 599 页。英中文均抽查全部
五个新增模块正文、接口字段锚点及共享 `InducedF` 文档。清单恰好覆盖全部
93 个接口各一次（66 个类、27 个记录），保留全部 29 个 `Has*` 类。已有
`AGENTS.md` 经验部分记录对象索引嵌入、显式环境范畴推断及一致的边界见证。
本基础已可在逆向翻译前独立集成；`typeprop` 及批次 PDF 仍由集成方负责。

## Freyd reconstruction and round trips

## Freyd 重建及往返

This slice continues the symmetric/Freyd foundation on `monoidal-cat-view`
from `af3d0fe`. It delivers the reverse translation and explicit round-trip
comparisons deferred by that slice. Ordinary arrow categories, self
enrichment and concrete model definitions are unchanged.

本批从 `monoidal-cat-view` 的 `af3d0fe` 继续对称／Freyd 基础，交付前批
待完成的逆向翻译及显式往返比较。通常箭头范畴、自富集及具体模型定义保持
原样。

The reusable [functor transport](../theories/Cat/Functor/Transport.v)
changes object representatives along chosen isomorphisms and supplies a
natural isomorphism to the original functor. Its boundary-naturality lemma
uses the weakest sufficient assumptions: a natural incoming boundary and
an invertible outgoing one. General
[tensor transport](../theories/Cat/Binoidal/Transport.v) uses context
functors and centrality of transported identities. Premonoidal associators
and the left unitor now expose the natural transformations used by this
argument. Equality isomorphisms, commuting-square composition and the
natural-isomorphism comparison for induced factorization live with their
general category theories.

可复用的[函子运输](../theories/Cat/Functor/Transport.v)沿选定同构改变对象
代表，并提供到原函子的自然同构。其边界自然性引理只使用充分的最弱条件：
入边界自然，出边界可逆。一般[张量运输](../theories/Cat/Binoidal/Transport.v)
使用上下文函子及运输恒等的中心性。预幺半结合子及左单位子现在暴露此论证
需要的自然变换。相等同构、交换方块复合及诱导分解的自然同构比较均放在
相应一般范畴理论中。

[Freyd contexts](../theories/Cat/Computational/Freyd/Context.v) conjugate
the original left action by exactly the tensor boundaries supplied by the
Freyd structure. Fixed and nested boundaries form natural transformations
and natural isomorphisms. Naturality across these boundaries derives the
value-unit and value-associativity equations without identifying equality
witnesses. [FreydArrow](../theories/Cat/Computational/Freyd/Arrow.v)
therefore reconstructs the computational Arrow from the same selected
cartesian values and pure inclusion. Computational witnesses, conjugating
inverse maps and model reductions remain transparent.

[Freyd 上下文](../theories/Cat/Computational/Freyd/Context.v)恰好沿 Freyd
结构给定的张量边界对原左作用共轭。固定及嵌套边界组成自然变换和自然同构。
跨这些边界的自然性导出值单位及值结合方程，无需识别相等见证。因此
[FreydArrow](../theories/Cat/Computational/Freyd/Arrow.v)从同一组选定
笛卡尔值及纯嵌入重建计算 Arrow。计算见证、共轭逆映射及模型归约保持透明。

The [round-trip module](../theories/Cat/Computational/Freyd/RoundTrip.v)
compares Arrow pure maps and contexts in specified Hom equality and the
pure functors by natural isomorphism. On the Freyd side it supplies an
actual categorical equivalence in the existing `CatCat` interface between
the original and returned value-indexed computation categories. Its pure
inclusions are naturally isomorphic, and its comparison preserves left
and right actions, both unitors, associator and symmetry across the
original selected boundaries. The right-action comparison composes the
exchange and left-action boundary squares; it assumes no effect
interchange.

[往返模块](../theories/Cat/Computational/Freyd/RoundTrip.v)在指定 Hom
相等下比较 Arrow 的纯映射及上下文，以自然同构比较纯函子。Freyd 方向在
已有 `CatCat` 接口中，给出原有与返回的值索引计算范畴之间的实际范畴等价。
纯嵌入自然同构，比较跨原有选定边界保持左右作用、两个单位子、结合子及
对称性。右作用比较复合交换与左作用边界方块，不假设效应交换律。

These are comparisons of supplied structures at the actual computation
categories. They do not assert an equivalence with unused ambient objects,
native equality of functor/law records, an equivalence of 2-categories of
structured functors, or soundness/completeness for an Arrow syntax. Closed
Freyd/ArrowApply and the separate static-Arrow characterization remain
future work. No extra axiom, UIP, proof irrelevance or function
extensionality is introduced. Model choices remain explicit.

这些比较涉及实际计算范畴上的给定结构，不主张与未使用环境对象的等价、
函子／定律记录的原生相等、带结构函子二范畴的等价，或 Arrow 语法的可靠性／
完备性。闭 Freyd／ArrowApply 及独立的静态 Arrow 刻画仍属后续工作。没有
增加公理、UIP、证明无关性或函数外延性；模型选择仍须显式提供。

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 278 temporary `Print Assumptions` checks were closed under the
global context: the previous 169 checks, 51 general constructions/laws,
and 58 new universe/concrete probes. The new probes cover both strict
hom/equality universe orders, separately sized value/computation categories,
both strict state carrier/equality orders, returned pure/context operations,
inverse comparison components and both equivalence functors. Returned State
sequencing still computes different results in the two execution orders;
the original noncentrality and order counterexamples were rerun. No
permanent tests or shared test configuration were changed.

验证使用未修改的 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1）。全库 `dune build @all @runtest @install` 通过。全部
278 项临时 `Print Assumptions` 均无额外全局假设：此前 169 项检查、51 项
一般构造／定律及 58 项新增宇宙／具体探针。新增探针覆盖 Hom／相等的两种
严格宇宙次序、值／计算范畴分别定级、状态载体／相等的两种严格次序、返回的
纯映射／上下文运算、比较逆分量及两个等价函子。返回的 State 顺序组合仍按
两种执行次序算出不同结果；原有非中心性及次序反例也重新验证。没有修改
永久测试或共享测试配置。

Strict bilingual HTML generated 302 modules per language and checked
609 pages. Both languages were inspected for the five new modules and
five extended foundational modules, including public anchors. The
inventory covers all 93 interfaces once (66 classes, 27 records), with all
29 `Has*` classes retained. The existing `AGENTS.md` learnings record
explicit category arguments and transport of naturality across coherent
boundaries. This task branch is ready for integration; `typeprop` and
batch PDF exports remain with the integration session.

严格双语 HTML 每种语言生成 302 个模块，检查 609 页。英中文均抽查五个
新增模块、五个扩展基础模块的正文及公共锚点。清单恰好覆盖全部 93 个接口
各一次（66 个类、27 个记录），保留全部 29 个 `Has*` 类。已有 `AGENTS.md`
经验部分记录显式范畴参数及跨相干边界的自然性运输。本任务分支已可交付
集成；`typeprop` 及批次 PDF 导出仍由集成会话负责。

## Static Arrow construction

## 静态 Arrow 构造

This slice continues E of #35 from `b86fee1` on `monoidal-cat-view`.
[StaticCat and StaticArrow](../theories/Cat/Computational/Arrow/Static.v)
construct static computations from the existing Applicative on a category
with selected terminal object, products and exponentials. The hom-set from
one value object to another is the base hom-set of global elements of the
Applicative image of their internal function object. Its specified,
Type-valued equality is reused directly. Effects are combined before the
resulting function receives its value argument; the value argument cannot
select a different effectful computation.

本批从 `monoidal-cat-view` 的 `b86fee1` 继续 #35 的 E 阶段。
[StaticCat 与 StaticArrow](../theories/Cat/Computational/Arrow/Static.v)
从具有选定终对象、积及指数的范畴上的已有 Applicative 构造静态计算。两个
值对象间的 Hom 广集，是其内部函数对象的 Applicative 像的全局元素所组成
的基底 Hom 广集，直接复用指定 Type 值相等。效应在所得函数收到值参数之前
组合，值参数不能选取另一个带效应计算。

The construction first extracts two general components.
[Exponential context theory](../theories/Cat/Exponential/Context.v) names
ordinary functions, presents the existing internal composition in execution
order, and derives internal product-context diagrams by evaluation and
exponential extensionality. [Contextual binary lifting](../theories/Cat/Applicative/Lifting.v)
specializes the existing lax postcomposition, input naturality, pure-input
and associativity laws by pairing contextual inputs. Its incoming product
boundaries are pinned to the same chosen products. Temporary proof opacity
is restored before exposing clients; computational maps stay transparent.

构造先提取两个一般组件。[指数上下文理论](../theories/Cat/Exponential/Context.v)
命名通常函数，按执行次序呈现已有内部复合，并通过求值及指数外延性导出内部
积上下文图。[上下文二元提升](../theories/Cat/Applicative/Lifting.v)通过配对
上下文输入，特化已有 lax 后合成、输入自然性、纯输入及结合定律。输入积边界
固定为同一组选定积。证明中的临时不透明性在暴露客户端前恢复，计算映射保持
透明。

Static composition lifts internal sequencing with the first computation
before the second. Pure inclusion names the base arrow and applies pure;
context extension maps the ordinary internal context function through the
same Applicative. The full computational Arrow laws follow from these
general diagrams. No strength, Monad, commutative tensorator, well-pointedness
or native equality of functions or law records is assumed. The existing
Freyd construction and round-trip comparison consume this Arrow unchanged.
This delivers a structural static representation, not a completeness or
equivalence theorem for a typed static-arrow calculus. ArrowApply, the
static/dynamic syntax comparison and Day/strong-profunctor results remain
open.

静态复合提升内部顺序组合，先运行第一个计算，再运行第二个。纯嵌入先命名
基底态射再作用纯值；上下文扩展通过同一 Applicative 映射通常内部上下文
函数。完整计算 Arrow 定律来自这些一般图。不假设强度、Monad、交换
tensorator、良点性或函数／定律记录的原生相等。已有 Freyd 构造及往返比较
可直接使用该 Arrow。本批交付结构式静态表示，不主张带类型静态 Arrow
演算的完备性或等价。ArrowApply、静态／动态语法比较及 Day／强余函子结果
仍待完成。

The new strict-level probes exposed an existing restriction in
[Reader](../theories/Instance/Set/Reader.v): its helpers and upper packaging
had identified the environment's universes with ambient ones, despite the
underlying `ReaderF` keeping them independent. Separate helper parameters
and explicit levels on the tensorator, pure transformation, lax structure
and `ReaderA` repair that restriction. The reader operations and witnesses
are unchanged. Strict probes now check both environment carrier/equality
orders, with ambient carrier strictly above ambient equality, independently
of the static closed client. Concrete static Reader/State probes use the
existing closed setoid model's common ambient carrier/equality level;
no resizing or stronger closed-setoid model is claimed.

新的严格层级探针暴露了[Reader](../theories/Instance/Set/Reader.v) 的已有
限制：辅助函数与上层包装合并了环境和所在宇宙，尽管底层 `ReaderF` 保持
它们独立。分开辅助参数，并在 tensorator、纯自然变换、lax 结构及
`ReaderA` 中显式指定层级，修复这一限制。Reader 运算及见证保持原样。严格
探针现分别检查环境载体／相等的两种次序，并使所在载体严格高于所在相等，
独立于静态闭客户端。具体静态 Reader／State 探针使用已有闭广集模型共同的
所在载体／相等层级，不主张 resizing 或更强的闭广集模型。

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed after the Reader repair. All 251 temporary assumption checks were
closed under the global context: 91 static/general construction and client
checks, 12 Reader signature checks and 148 rerun Applicative/strong-Monad
checks. They cover both strict hom/equality orders, objects strictly larger
than both, separate environment and ambient levels, explicit model enabling,
pure/context/first computations, noncommuting State execution orders and
Freyd round-trip computations and comparison inverses. No permanent tests
or shared test configuration were changed.

验证使用未修改的 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1）。Reader 修复后，全库 `dune build @all @runtest @install`
通过。251 项临时公理检查均无额外全局假设：91 项静态／一般构造及客户端
检查、12 项 Reader 签名检查，以及重跑的 148 项 Applicative／强 Monad
检查。覆盖 Hom／相等的两种严格次序、对象严格高于两者、独立环境与所在
层级、显式模型启用、纯／上下文／first 计算、不交换的 State 执行次序，
以及 Freyd 往返计算和比较逆映射。没有修改永久测试或共享测试配置。

Strict bilingual HTML generated 305 modules per language and checked
615 pages. The three new modules and the updated Reader documentation
were inspected in both languages, including public anchors. The complete
inventory still covers 93 interfaces exactly once (66 classes, 27 records)
and all 29 `Has*` classes. The existing `AGENTS.md` learnings now record
chosen product boundaries for contextual lifting proofs. The branch is
ready for integration; `typeprop` and batch PDF export remain with the
integration session.

严格双语 HTML 每种语言生成 305 个模块，检查 615 页。英中文均抽查三个
新模块及 Reader 更新的正文和公共锚点。完整清单仍恰好覆盖 93 个接口各一次
（66 个类、27 个记录）及全部 29 个 `Has*` 类。已有 `AGENTS.md` 经验部分
现记录上下文提升证明的选定积边界。本分支已可交付集成；`typeprop` 及批次
PDF 仍由集成会话负责。


## Section openings after the integrated baseline

## 集成基线后的 Section 引言

The task branch was rebased onto integrated baseline
`fee98fcff6c656d4dae26425401db7a2bc403b9b`; the static construction is now
`a167f6c` (formerly `a454875`). The only conflict was in `AGENTS.md` and
retained both upstream Section requirements and the existing field/comment
spacing rule. All task-modified source Sections now have an adjacent
bilingual mathematical opening. Twenty missing openings were added, and
seven existing entrance descriptions were clarified. Removing comments
leaves every source token unchanged in this documentation batch.

任务分支已重基到集成基线 `fee98fcff6c656d4dae26425401db7a2bc403b9b`；
静态构造现为 `a167f6c`（原 `a454875`）。唯一冲突位于 `AGENTS.md`，保留
上游 Section 要求及原有字段／注释空行规则。本任务修改过的源码 Section
现均有相邻的双语数学引言，补齐二十处缺项，并澄清七处已有入口说明。本次
文档批次删除注释后，所有源码词元均与提交前相同。

With the unchanged `rocq-cats` switch, full `dune build @all @runtest
@install` passed. All 251 static/Reader/Applicative temporary assumption
checks were rerun successfully. Strict bilingual HTML generated 329 modules
per language, checked 663 pages, and all 54 changed English/Chinese comment
blocks were checked in their language's output. The declaration inventory
now includes the four upstream interfaces and covers all 97 declarations
once (68 classes, 29 records), retaining 29 `Has*` classes. No permanent
tests, shared environment or integration branch were changed. Batch PDF
exports remain with the integration session.

在未修改的 `rocq-cats` switch 中，全库 `dune build @all @runtest @install`
通过，251 项静态／Reader／Applicative 临时公理检查重跑通过。严格双语 HTML
每种语言生成 329 个模块，检查 663 页，54 个修改的英中注释块均核对已进入
对应语言的输出。声明清单补入上游四个接口，现恰好覆盖全部 97 项声明各
一次（68 个类、29 个记录），保留 29 个 `Has*` 类。没有修改永久测试、共享
环境或集成分支；批次 PDF 仍由集成会话导出。


## Static values and ordered Applicative operations

## 静态值与有序 Applicative 运算

Following the Section documentation commit `d3798ae`, this phase adds
[StaticValues](../theories/Cat/Computational/Arrow/StaticValues.v) on the
same integrated baseline `fee98fcff6c656d4dae26425401db7a2bc403b9b`.
Transparent evaluation and abstraction compare terminal-input static
computations with global Applicative values; the underlying maps also
commute with every external-context substitution. Both inverse laws,
respectfulness and equality reflection use only the original hom equality.
The comparison reuses the exponential-unit isomorphism, without equality
of function/law records or a well-pointedness assumption.

继 Section 文档提交 `d3798ae` 后，本阶段在同一集成基线
`fee98fcff6c656d4dae26425401db7a2bc403b9b` 上增加
[StaticValues](../theories/Cat/Computational/Arrow/StaticValues.v)。透明求值
与抽象比较终输入静态计算和全局 Applicative 值，其底层映射也与每个外部
上下文替换交换。两条互逆定律、尊重性及相等反映只使用原有 Hom 相等。比较
复用指数单位同构，不要求函数／定律记录相等或良点性。

Pure values, ordinary result mapping and ordered application are preserved
and reflected. Arbitrary binary lifting is represented by a static
composition which first abstracts the left value, then composes with the
function produced from the right value. This retains the left-before-right
effect order. Three ordinary diagrams were extracted to
[exponential context theory](../theories/Cat/Exponential/Context.v): terminal
evaluation of names and sequencing, and binary application. The binary
diagram needs no terminal object or effect structure. All lifting proofs
reuse the general shared-context Applicative laws.

纯值、通常结果映射及有序应用均得到保持与反映。任意二元提升可表示为静态
复合：先抽象左值，再与从右值产生的函数复合，保持从左到右的效应次序。
三个通常图提取到[指数上下文理论](../theories/Cat/Exponential/Context.v)：
命名与顺序组合的终求值，以及二元应用。二元图不要求终对象或效应结构。
所有提升证明复用一般共同上下文 Applicative 定律。

The unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0,
Dune 3.23.1) passed full `dune build @all @runtest @install`. All 91 new
temporary assumption checks are closed under the global context: 20 public
definitions/laws, 51 signatures instantiated with both strict hom/equality
orders and objects strictly above hom/equality, and 20 concrete definitions
and reductions. The concrete checks include explicit model enabling,
Reader computations, both State inverse reductions, pure/state retention,
and ordered binary State outputs `(false, true)` versus reversed
`(false, false)` from the same initial state. These supplement the 529
successful rebase checks (91 static, 278 Freyd, 148 Applicative/strong Monad,
12 Reader signatures); no permanent tests were added.

未修改的 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、Dune
3.23.1）通过全库 `dune build @all @runtest @install`。91 项新增临时公理
检查均无额外全局假设：20 项公共定义／定律、51 项签名分别实例化到 Hom／
相等的两种严格次序及对象严格高于两者的情形，以及 20 项具体定义和归约。
具体检查覆盖显式模型启用、Reader 计算、State 的两个互逆归约、纯值及状态
保持，以及同一初始状态下顺序二元 State 输出 `(false, true)`、反序输出
`(false, false)`。这些补充已通过的 529 项重基检查（91 项静态、278 项 Freyd、
148 项 Applicative／强 Monad、12 项 Reader 签名）；没有新增永久测试。

Strict bilingual HTML generated 330 modules per language and checked
665 pages. All 78 English/Chinese comment blocks and all public anchors
in the two affected modules were checked in their language's output.
The inventory covers all 97 interfaces exactly once (68 classes, 29 records)
and retains all 29 `Has*` classes. The latest fetched integration baseline
is still `fee98fc`; only the task branch is updated. Batch PDF export remains
with integration. A direct comparison with derived Arrow fanout, typed
syntax preservation/reflection, and static/dynamic representation conditions
remain future work; this phase proves operations on actual arrows rather
than a syntactic equational equivalence.

严格双语 HTML 每种语言生成 330 个模块，检查 665 页。两个受影响模块的
全部 78 个英中注释块及全部公共锚点均核对已进入对应语言输出。清单恰好覆盖
全部 97 个接口各一次（68 个类、29 个记录），保留全部 29 个 `Has*` 类。
最新获取的集成基线仍为 `fee98fc`，只更新任务分支，批次 PDF 仍由集成方导出。
与导出的 Arrow fanout 直接比较、带类型语法保持／反映、静态／动态表示条件
留作后续。本阶段证明实际态射上的运算，不主张语法方程等价。


## Static cartesian operation comparisons

## 静态笛卡尔运算比较

On task branch `monoidal-cat-view`, following `1f2450c` and based on the
unchanged integrated baseline `fee98fcff6c656d4dae26425401db7a2bc403b9b`,
[StaticCartesian](../theories/Cat/Computational/Arrow/StaticCartesian.v)
compares actual derived first, ordered split and fanout with Applicative
lifting. For every ordinary input object, fanout lifts the existing inverse
product-exponential comparison. Split precomposes the two internal
functions with their respective input projections. Right context is
conjugated from the original left context by pure exchange, without
selecting another action.

任务分支 `monoidal-cat-view` 在 `1f2450c` 之后，基于未变的集成基线
`fee98fcff6c656d4dae26425401db7a2bc403b9b`，增加
[StaticCartesian](../theories/Cat/Computational/Arrow/StaticCartesian.v)，
比较实际导出的 first、有序 split 和 fanout 与 Applicative 提升。对每个
通常输入对象，fanout 提升已有积指数比较的逆；split 按各自输入投影预合成
两个内部函数。右上下文通过纯交换共轭原左上下文得到，不另选第二个作用。

The ordinary diagrams are reusable in
[exponential context theory](../theories/Cat/Exponential/Context.v).
[Exponential laws](../theories/Cat/Exponential/Laws.v) now expose contextual
application of the product comparison and its coherence with terminal
argument evaluation. These reuse the existing inverse transpose formula,
not a second universal-property proof. Products and exponentials suffice
for the context diagrams; terminal evaluation additionally uses the chosen
terminal object. Applicative lifting uses the existing contextual laws.

通常图位于可复用的[指数上下文理论](../theories/Cat/Exponential/Context.v)。
[指数定律](../theories/Cat/Exponential/Laws.v)增加积比较的上下文应用及其与
终参数求值的相干，复用已有逆转置公式，不重复证明泛性质。上下文图只要求
积与指数，终参数求值另用选定终对象；Applicative 提升使用已有上下文定律。

At terminal input, the transparent value comparison preserves ordered
pairing and every binary lifting expressed as fanout followed by a pure
binary operation. Its inverse reflects those same operations. All
comparisons use HomEq and retain left-before-right effects, without
commutativity, strength or Monad assumptions. The work remains categorical
semantics; following the user's priority, typed syntax is deferred until
the semantic structures and their correspondence conditions are established.

在终输入处，透明值比较保持有序配对及由 fanout 后接纯二元运算表示的任意
二元提升，其逆反映同一批运算。所有比较使用 HomEq，保留从左到右的效应，
不假设交换性、强度或 Monad。本轮继续范畴语义；按用户确定的优先级，带
类型语法等语义结构及其对应条件建立后再讨论。

The unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0,
Dune 3.23.1) passed full `dune build @all @runtest @install`. All 284
temporary assumption checks were closed under the global context: 102 new
checks, 91 existing value-comparison checks and 91 static-Arrow/Freyd client
checks. The new batch covers all 13 public definitions/laws, 52 strict
signatures (both hom/equality orders with objects strictly below or above
both), four Reader/State environment-level signatures and 33 concrete
constructions/reductions. Concrete checks include actual first/split/fanout,
State execution-order differences, both value comparison directions,
Reader evaluation and a binary operation discarding its left result while
retaining that computation's observable state effect. No permanent tests
or shared test configuration changed.

未修改的 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、Dune
3.23.1）通过全库 `dune build @all @runtest @install`。284 项临时公理检查
均无额外全局假设：102 项新增检查、91 项已有值比较检查及 91 项静态 Arrow／
Freyd 客户端检查。新增批次覆盖全部 13 项公共定义／定律、52 项严格签名
（Hom／相等两种次序，且对象严格低于或高于两者）、四项 Reader／State
环境层级签名及 33 项具体构造／归约。具体检查包括实际 first／split／
fanout、State 执行次序差异、值比较的两个方向、Reader 求值，以及丢弃左
结果的二元运算仍保留其计算的可观察状态效应。没有修改永久测试或共享测试
配置。

Strict bilingual HTML generated 331 modules per language and checked
667 pages. All 104 bilingual comment blocks and 98 public anchors in the
three affected modules were checked against their generated language
outputs, including generated anchors for Unicode names. The inventory
still covers all 97 class/record declarations exactly once, including all
29 `Has*` classes. Only this task branch is updated; `typeprop`, the shared
toolchain and batch PDF export remain with integration. The remaining
semantic work concerns reconstruction and precise static/dynamic or
ArrowApply conditions, without treating syntax as the next required phase.

严格双语 HTML 每种语言生成 331 个模块，检查 667 页。三个受影响模块的
全部 104 个英中注释块及 98 个公共锚点均对照对应语言输出核验，包括 Unicode
名称的生成锚点。清单仍恰好覆盖全部 97 个类／记录声明各一次，包括全部
29 个 `Has*` 类。只更新本任务分支；`typeprop`、共享工具链及批次 PDF
仍由集成会话管理。剩余语义工作涉及重建及精确的静态／动态或 ArrowApply
条件，不将语法视为下一必经阶段。


## Revalidation on the advanced integration baseline

## 在前进后的集成基线上复验

The final handoff check found that local `typeprop` had advanced to
`89580d6ee75110d30fc4a82d6c60fb44f28aabc1`, while the fetched remote still
reported `fee98fc`. The task branch was rebased without conflicts onto that
local integrated baseline. The fanout mathematics is now `3c971d7`
(formerly `bc077f1`); all three affected theory modules are byte-identical
to their pre-rebase versions. This updates the preceding handoff baseline
without extending the mathematical scope or changing the integration branch.

最终交接检查发现本地 `typeprop` 已推进到
`89580d6ee75110d30fc4a82d6c60fb44f28aabc1`，获取的远端当时仍为 `fee98fc`。
任务分支已无冲突重基到这个本地集成基线。fanout 数学提交现为 `3c971d7`
（原 `bc077f1`），三个受影响理论模块与重基前逐字节一致。本条更新上一轮
交接基线，不扩大数学范围，也不修改集成分支。

On `89580d6`, full `dune build @all @runtest @install` and all 284 temporary
assumption checks were rerun successfully (102 new interfaces/clients,
91 value comparisons, 91 static-Arrow/Freyd checks). Strict bilingual HTML
now covers 336 modules per language and checks 677 pages, including the
five modules added by integration. The same 104 bilingual comment blocks
and 98 public anchors were checked again; the exact inventory remains
97 interfaces. The unchanged project switch and explicit model selection
were retained. Batch PDFs remain with integration; syntax remains deferred.

在 `89580d6` 上，全库 `dune build @all @runtest @install` 及全部 284 项
临时公理检查均重跑通过（102 项新增接口／客户端、91 项值比较、91 项静态
Arrow／Freyd 检查）。严格双语 HTML 现每种语言覆盖 336 个模块、检查 677 页，
包含集成新增的五个模块。同样的 104 个英中注释块及 98 个公共锚点再次核验，
精确清单仍为 97 个接口。保留未改动的项目 switch 及显式模型选择。批次 PDF
仍由集成方导出，语法仍暂缓。


## Global-computation foundations

## 全局计算基础

Following `4cd858a`, the #35 task independently adds the general ordered
pairing laws, the terminal-input Hom lax functor and constant respectful
maps. The existing Hom functor supplies functoriality, and `comp_square`
composes the three associativity naturality squares. Neither a monad nor
closedness nor interchange of two effects is required. The result lands
in setoids, keeping the computation category's native hom/equality levels;
it is not automatically an endofunctor on an arbitrary value category.

继 `4cd858a` 后，#35 任务独立添加一般有序配对定律、终输入 Hom lax 函子
及常值保相等映射。已有 Hom 函子提供函子性，`comp_square` 复合三个结合
自然性方块。不要求 Monad、闭性或两个效应交换。结果落在广集范畴，保留计算
范畴原生 Hom／相等层级，一般不会自动成为任意值范畴上的自函子。

Targeted Global/Constant builds passed in the unchanged `rocq-cats` switch.
All 22 temporary assumption checks are closed under the global context:
all 16 public declarations and six independent-universe probes. These
separate the two categories' hom/equality levels in both strict orders
and keep constant-map source and target levels distinct. There are 339
modules and the same 97 interfaces. No permanent test or shared toolchain
was changed. Setoid-base Applicative packaging and static reconstruction
are the dependent next slice of this same authorized task; syntax stays
paused until the semantic development is established.

在未改动的 `rocq-cats` switch 中，Global／Constant 定向构建通过。22 项
临时公理检查均无额外全局假设：全部 16 个公共声明及六项独立宇宙探针，
将两个范畴的 Hom／相等层级按两种严格次序分离，也分离常值映射的来源及
目标层级。现有 339 个模块、原有 97 个接口。没有修改永久测试或共享工具链。
广集基底的 Applicative 打包及静态重建是同一已授权任务的后续依赖切片；语法
等语义建立后再讨论。


## Arrow values and static Applicative recovery

## Arrow 值与静态 Applicative 回收

This slice continues on `monoidal-cat-view` from the validated integrated
baseline `89580d6ee75110d30fc4a82d6c60fb44f28aabc1`. The reusable
terminal-input Hom/lax foundation was delivered independently in
[078ba8f](https://github.com/Godalin/rocq-cats/commit/078ba8fe97f04fdc885579b3a44bd3a4af32e465).
[The setoid adapter](../theories/Instance/Set/Arrow.v) supplies `ArrowA`
using that same lax structure and pure constant arrows. Computation hom
carrier/equality levels match the ambient setoid levels; computation
objects retain an independent universe. No Monad, strength or exponentials
are required by this adapter. Imports enable no chosen model structure.

本切片在 `monoidal-cat-view` 上继续，已验证的集成基线为
`89580d6ee75110d30fc4a82d6c60fb44f28aabc1`。可复用的终输入 Hom／lax
基础已在 [078ba8f](https://github.com/Godalin/rocq-cats/commit/078ba8fe97f04fdc885579b3a44bd3a4af32e465)
独立交付。[广集适配器](../theories/Instance/Set/Arrow.v)复用同一 lax
结构，以纯常值箭头提供 `ArrowA`。计算 Hom 的载体／相等层级对应所在广集
层级，计算对象保留独立宇宙。适配器不要求 Monad、强度或指数，导入不启用
选定模型结构。

[Static recovery](../theories/Instance/Set/StaticArrow.v) works in the
existing closed setoid model at a common carrier/equality level. It reuses
two exponential-unit isomorphisms to compare the recovered and original
Applicatives by a transparent natural isomorphism. Both transformations
preserve pure values, ordered pairing and every ordinary binary lifting.
This establishes the Applicative-to-static-Arrow-to-Applicative round trip
on that model, without equating functor or law records. It does not
reconstruct arbitrary dynamic Arrows. General static/dynamic reconstruction
conditions and the ArrowApply/Monad relationship remain subsequent semantic
work; typed syntax stays deferred.

[静态回收](../theories/Instance/Set/StaticArrow.v)使用载体／相等处于同一
层级的已有闭广集模型，复用两个指数单位同构，以透明自然同构比较回收与原有
Applicative。两个变换均保持纯值、有序配对及每个通常二元提升。这给出该模型
上的 Applicative 经静态 Arrow 再回到 Applicative 的往返，不要求函子或定律
记录相等，也不重建任意动态 Arrow。一般静态／动态重建条件及 ArrowApply／
Monad 关系仍为后续语义工作；带类型语法继续暂缓。

Full-library `dune build @all @runtest @install` passed with the unchanged
`rocq-cats` switch: Rocq/Stdlib 9.2.0, OCaml 5.3.0 and Dune 3.23.1.
All 95 comprehensive temporary assumption checks were closed under the
global context: all 33 public declarations across the five new modules,
26 universe probes and 36 concrete constructions/reductions. The probes
separate the two abstract categories' hom/equality levels, vary the setoid
adapter's carrier/equality order and computation-object level, and separate
Reader/State environment sizes below the existing closed-model bound.
Concrete checks cover pure values, both inverse equations, pairing, binary
lifting, ordinary State Arrow values, left-before-right State effects and
Reader recovery. Model-import probes also check explicit structure enabling.
The earlier 22 foundation checks overlap this comprehensive batch and are
not counted as additional distinct checks.

在未改动的 `rocq-cats` switch（Rocq／Stdlib 9.2.0、OCaml 5.3.0、
Dune 3.23.1）中，全库 `dune build @all @runtest @install` 通过。95 项
综合临时公理检查均无额外全局假设：五个新模块的全部 33 个公共声明、26 项
宇宙探针及 36 项具体构造／归约。探针分离两个抽象范畴的 Hom／相等层级，
改变广集适配器的载体／相等次序及计算对象层级，并在已有闭模型界限下分离
Reader／State 环境大小。具体检查覆盖纯值、两条互逆方程、配对、二元提升、
通常 State Arrow 的值、从左到右的 State 效应及 Reader 回收。模型导入探针
也检查选定结构须显式启用。先前 22 项基础检查与本综合批次重叠，不重复计数。

Strict bilingual HTML generated 341 modules per language and checked local
links and anchors in all 687 pages. All 76 bilingual documentation blocks
and 66 public declaration anchors across the five new modules were checked
in the appropriate reading edition. The inventory remains 97 interfaces
(68 classes, 29 records), including 29 `Has*` classes. Abstract pointwise
inverse lemmas avoid normalizing large lifted computations; computational
maps remain transparent, and the existing `AGENTS.md` learning records this
proof technique. No permanent tests, shared test aliases, shared toolchain
or `typeprop` updates were introduced. Batch PDF export remains with the
integration session.

严格双语 HTML 每种语言生成 341 个模块，全部 687 页的本地链接及锚点检查
通过。五个新模块的全部 76 段双语文档及 66 个公共声明锚点均在对应阅读版
核对。清单仍为 97 个接口（68 个类、29 个记录），其中 29 个 `Has*` 类。
抽象的逐点互逆引理避免归约整个大型提升计算，计算映射保持透明；现有
`AGENTS.md` 学习条目记录此证明技巧。没有新增永久测试、共享测试别名、
共享工具链变更或 `typeprop` 更新；批次 PDF 仍由集成会话导出。


## Inferred universe instances in computational models

## 计算模型中由推断确定的宇宙实例

Following the user's readability request, the Reader tensorator, State
multiplication/strength transformations and setoid Arrow adapter omit
seven repeated universe instances. Each still fixes its necessary size
boundary once; functor composition, product functors and transformation
endpoints infer the other occurrences. General Monad, Applicative and
computational Arrow theory already uses inferred instances. The remaining
model annotations preserve independent environment, ambient carrier and
equality levels, or state the existing closed-model common-level bound.
No mathematical interface, operation or universe binder order is changed.

按用户的可读性要求，Reader tensorator、State 乘法／强度变换及广集 Arrow
适配器省略七处重复宇宙实例。每处仍固定一次必要的大小边界，其余出现由函子
复合、积函子及自然变换端点推断。一般 Monad、Applicative 和计算 Arrow
理论原已使用推断实例。模型中保留的标注保护环境、所在载体及相等层级的独立性，
或表达已有闭模型的共用层级界限。数学接口、运算及宇宙绑定次序均未改变。

The unchanged `rocq-cats` switch passed full-library
`dune build @all @runtest @install`. Twenty-eight temporary probes check all
Reader/State functor, natural transformation and chosen computational
structures with both strict environment carrier/equality orders below
independent ambient levels. The existing 95 Arrow-value/static-recovery
checks were rerun, including their four independent adapter-level orders
and transparent Reader/State computations. All 123 assumption reports are
closed under the global context. A separate temporary probe against the
committed Reader source confirms that the function-setoid size bound is
pre-existing, rather than introduced by this simplification. Strict
bilingual HTML again covers 341 modules per language and 687 checked pages.
No permanent test, interface, chosen instance, shared toolchain or
integration-branch update was added.

未改动的 `rocq-cats` switch 通过全库
`dune build @all @runtest @install`。28 项临时探针检查全部 Reader／State
函子、自然变换及选定计算结构：环境载体／相等按两种严格次序排列，并低于
独立的所在层级。另重跑既有 95 项 Arrow 值／静态回收检查，包括四种独立
适配器层级次序及透明 Reader／State 计算。全部 123 项公理报告均无额外全局
假设。针对已提交 Reader 源码的独立临时探针确认，函数广集的大小界限原已
存在，并非此次简化引入。严格双语 HTML 再次覆盖每种语言 341 个模块及
687 页链接检查。没有新增永久测试、接口、选定实例、共享工具链或集成分支
更新。


## Global-computation context foundation

## 全局计算上下文基础

The static-interpretation slice rebases `monoidal-cat-view` onto
`c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90`. The rebase has no conflicts;
full-library/test/install validation and the existing 123 temporary
universe/semantic checks passed with the unchanged `rocq-cats` switch.
The rebased task head before new mathematics is `c434d44`; original
`0683f04` is retained in the earlier historical delivery records.

静态解释切片将 `monoidal-cat-view` 重基到
`c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90`，没有冲突；在未改动的
`rocq-cats` switch 中，全库／测试／安装与既有 123 项临时宇宙／语义检查
通过。新增数学内容前的重基任务头为 `c434d44`，原 `0683f04` 保留在此前
历史交付记录中。

[GlobalContext](../theories/Cat/Computational/Arrow/GlobalContext.v)
attaches a terminal-input computation to an unchanged ordinary input.
Its substitution, ordered-pairing and nested-context laws require only
selected finite products and the existing Arrow laws. Effects are neither
duplicated nor interchanged. This independently reusable foundation adds
no interface or model choice and retains separate category sizes.
All ten public declarations and six strict independent-category probes
passed temporary assumption inspection (16 reports, all closed under the
global context). The targeted module build passed. No permanent test,
shared toolchain change or integration-branch update was introduced.

[GlobalContext](../theories/Cat/Computational/Arrow/GlobalContext.v)
将终输入计算附在不变的普通输入旁。其替换、有序配对及嵌套上下文律仅要求
选定有限积及已有 Arrow 定律，不复制或交换效应。此可独立复用基础不增加
接口或模型选择，并保留独立范畴大小。全部十个公共声明及六项严格独立范畴
探针通过临时公理检查（16 项报告，均无额外全局假设）；模块定向构建通过。
没有新增永久测试、共享工具链变更或集成分支更新。
