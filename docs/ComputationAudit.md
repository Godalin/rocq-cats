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

The explicitly selected [ReaderA](../theories/Instance/Set/Applicative.v)
uses respectful maps, constant functions and pointwise pairing. Postcomposition
reuses the foundational composition laws. Its environment equality level is
separate, and a small environment permits the ambient carrier universe to be
strictly larger than the equality universe. Temporary checks instantiate the
abstract interface and application at both strict hom/equality universe
orders and check transparent Reader pure/map/pair/application computation.

显式选择的 [ReaderA](../theories/Instance/Set/Applicative.v) 使用保相等映射、
常值函数及逐点配对，后合成复用基础复合定律。环境相等层级单独保留，小环境
允许所在广集载体宇宙严格大于相等宇宙。临时检查在 Hom／相等宇宙的两种严格
次序下实例化抽象接口及应用，并检查 Reader 纯值、映射、配对及应用的透明计算。

This is a sufficient lawful Applicative presentation, not a claim that an
arbitrary cartesian lax endofunctor determines a natural pure map. A reverse
construction from an independently axiomatized operation interface, tensorial
strength and its compatibility laws, Monad conversion and computational Arrow
remain separate milestones. The Reader model does not impose size bounds on
the abstract interface. No general coend or Day convolution construction is
introduced by this slice.

这是一种充分的带定律 Applicative 呈现，不主张任意笛卡尔 lax 自函子都确定
自然纯值映射。从独立运算公理接口反向构造、张量强度及其相容律、Monad 转换和
计算 Arrow 仍为独立里程碑。Reader 模型的大小界不施加给抽象接口。此切片不引入
一般余端或 Day 卷积构造。

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
4. The lawful Applicative slice above is implemented. Subsequent slices add
   the independent operation-presentation comparison, computational Arrow,
   coherent tensorial strength for the existing Monad and the direct
   conversion diagram. These remain open in #35.

1. 打包指定幺半结构之间的函子及其 lax 结构：单位映射、自然 tensorator、
   结合律和两条单位律。不要求可逆、张量强度或闭／笛卡尔基底。
2. 通用地证明一次幺半群传输：`e' = F(e) ∘ φ₀`、`m' = F(m) ∘ φ₂`；
   用 `fmap F` 映射同态，并封装为已有幺半群对象范畴之间的函子。
3. 检查真正不可逆的 lax 结构、独立的 Hom／相等宇宙次序，以及基础公理。
   区分临时检查与保留的接口回归。
4. 上述带定律 Applicative 切片已实现。后续再添加独立运算呈现的比较、计算
   Arrow、已有 Monad 的相干张量强度及直接转换图；这些仍为 #35 的待办。

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
