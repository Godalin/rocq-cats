# 从表示与 comprehension 恢复 CwF

本轮先完成一个精确的反向准则：**固定族值预层 T 时，在原生 Hom 表示
可包装的大小下，选定上下文扩张与选定配对预层表示可互相构造。**
独立大小下的候选级准则使用泛配对，并给出提升 Hom 表示，见第 2 节。
[ContextRepresentation](../theories/DTT/Context/Representation.v) 已实现该结果。
固定类型预层后，元素投影上的 comprehension 已可恢复显示结构及 CwF，见第 4 节。
从一般总范畴选取类型代码的部分仍另行设计，边界如下。

## 1. 现有 comprehension 提供什么

对 `P : Fct E C`，已有的
[Comprehension](../theories/Cat/Comprehension.v) 提供选定笛卡尔提升、
扩张函子、投影自然变换，以及笛卡尔态射的显示方块为拉回的泛性质。
它没有选择：

- 每个 Γ 上的类型广集及其指定相等；
- 类型相等在项上的相干、见证独立的转换；
- 按这些相等满足单位、复合和尊重性定律的类型／项替换；
- 终上下文。

全忠实 comprehension 函子刻画已有总范畴态射如何表示为显示交换方块。
它仍不替代上述类型相等及转换数据。尤其不能把任意垂直同构自动当作
类型相等：非恒等自同构在项上的作用可能不满足自相等转换为恒等的要求。
本库的严格相等仍是各广集指定的相等，不引入第二套严格性标准。

## 2. 已实现的必要充分准则：固定 T 后的表示

输入已有的 `T : Fct (C^op) FamCat`。它已经给出类型、项、指定相等、
相干转换和替换。对 `A : Ty T Γ`，已有的配对预层是：

```text
ContextPairF T A Δ = Σ (σ : Hom Δ Γ), Tm T Δ A[σ]Ty[T]
```

依赖和的相等保留 `H : σ ≈ σ'`，并在沿 H 转换后比较项。
重索引及其相干性复用 [ContextExtension](../theories/DTT/Context/Extension.v)。

新的选定结构为：

```coq
Class HasContextRepresentation :=
  { ContextRep {Γ : @Ob C} (A : Ty T Γ) : @Ob C
  ; context_representation {Γ : @Ob C} (A : Ty T Γ)
    : Hom(-, ContextRep A) ≅N ContextPairF T A
  }.
```

这里 C 和 T 是上下文中的命名参数。候选表示直接使用已有的自然同构，
选择对象及其表示才放进 `HasContextRepresentation T`，不另设数据暂存记录。

对任意候选 `R : Hom(-, E) ≅N ContextPairF T A`，定义：

```text
(p,q) := R_E(id_E)
pair(σ,t) := (R_Δ)⁻¹(σ,t)
```

自然性给出 `R_Δ(h) ≈S (p,q)[h]Pair[T,A]`。
`context_pair_data_iff` 将这个配对数据等式与原来的 `is_context_pair` 对接，
包括经替换复合和基底相等转换后的第二分量。
分量同构的两条逆律因此给出完整的扩张泛性质及唯一性。
`context_extension_of_representation` 保留上述中介态射为透明计算见证。

这部分现已复用 [Representable](../theories/Instance/Set/Representable.v)
中的一般理论。`u ⦂ Univ(F)` 要求任意 y 都唯一写成 `F(f)(u)`；
`represents_iff_universal_element` 与反变版本
`represents_op_iff_universal_element` 将它与自然同构表示互相构造。
`representation_op_generic` 给出上述 (p,q)，
`representation_op_at` 给出自然性公式，
`representation_op_universal` 给出完整的唯一中介性质。
CwF 层只通过 `context_pair_data_iff` 将它对接到含类型转换的配对条件，
不再单独重复证明通用元素的泛性质。

一般理论还给出 `representation_iso` / `representation_op_iso`：
两个表示对象有选定同构，且在保持通用元素的态射中唯一。
这不要求任意两个对象同构都相等，也不比较表示记录或逆见证的原生相等。
表示与通用元素之间的往返按自然变换相等及广集相等比较。

`⦂` 统一表示指定数据具有右侧的性质或结构。表示记号为
`X ⦂ Rep F`（协变）和 `X ⦂ Repᵒᵖ P`（反变）；
通用元素写为 `u ⦂ Univ(F)`，笛卡尔态射写为 `f ⦂ Cart(P)`。
这些是作用于原有定义的共享记号，均属于 `cat_scope`。

[Yoneda](../theories/Instance/Set/Yoneda.v) 的两条互逆定律独立于同构的
集合层级包装。自然变换集可能比 F 的值更大，故 `yoneda_lemma_iso`
现在使用基础 [LiftS](../theories/Set/Core.v)（记号 `↑S`）将两端装入足够大的
共同集合范畴。`lift_resp`（`f^↑S`）保留原映射的逐点计算。
提升分别包装载体与相等见证，投影 `lower` 可直接计算；只有向上的大小约束，
不使用 resizing，也不将原来的相等换成原生相等。

反向复用已有的 `context_extension_nat_iso`。两个选定构造为：

```text
ContextRepresentation_HasContextExtension
ContextExtension_HasContextRepresentation

context_extension_iff_representation T:
  HasContextExtension T ↔ HasContextRepresentation T
```

转换是普通定义，须显式启用。选定一侧不会通过类型类搜索自动选定另一侧。
加上独立选择的 `HasTerminal C`，`RepresentedCwF T` 组装已有的 `CwF C`；
抽象 CwF 核心无需改动，也无需再存储替换公理。

两个方向的往返按数学数据比较：

- 原扩张经表示恢复后，投影与原投影相等；泛变量沿这个投影相等转换后相等。
- 恢复的配对与原配对相等，且保留原配对的计算行为。
- 原表示经扩张恢复后，其正向自然变换与原自然变换逐分量相等。

不要求结构记录、证明字段或自然同构的逆见证原生相等。
这些结论中的类型、项和替换都来自同一个 T。

### Universal-pair criterion at independent sizes

[Context/Representation](../theories/DTT/Context/Representation.v) also exposes
the candidate-level `context_extension_iff_universal_element`: for a fixed
pair `u = (p,q)` at E, `is_context_extension T A E p q` is equivalent to
`u ⦂ Univ(ContextPairF T A)`. The two transparent conversions retain the
same mediating maps. `context_extension_universal_mediator` compares the
recovered mediator with the supplied one. The existing native-representation
recovery now reuses `context_extension_of_universal_element`.

This criterion avoids putting native Hom and pair setoids in a common
`SetCat`. Their sizes can differ: section carriers must contain both homs
and right-inverse witnesses, so hom equality may force them above the native
hom carrier. The existing `HasContextRepresentation` uses native Hom and
retains that packaging restriction; it is not a necessary criterion at these
larger term sizes. `context_extension_lifted_representation` instead reuses
`universal_element_lifted_representation` on the opposite category, providing
`E ⦂ Rep↑ ContextPairF T A` with upward bounds only. No resizing or equality
of functor records is assumed. Display recovery can use this general
universal-pair criterion and lifted representation, as implemented below.

### 独立大小下的泛配对准则

[Context/Representation](../theories/DTT/Context/Representation.v) 另给出候选
层级的 `context_extension_iff_universal_element`：固定 E 处的配对
`u = (p,q)` 后，`is_context_extension T A E p q` 恰等价于
`u ⦂ Univ(ContextPairF T A)`。两个透明转换保留同一个中介映射；
`context_extension_universal_mediator` 比较恢复的中介与给定中介。
原有原生表示恢复也改为复用 `context_extension_of_universal_element`。

这个准则不把原生 Hom 与配对广集装入同一个 `SetCat`，允许两者大小不同。
截面载体须同时包含态射及其右逆见证，故 Hom 相等见证可能迫使截面大于
原生 Hom 载体。现有 `HasContextRepresentation` 使用原生 Hom，仍受此
包装限制；对于这些较大的项载体，它不是必要准则。
`context_extension_lifted_representation` 改在反范畴中复用已有
`universal_element_lifted_representation`，以仅向上的大小约束给出
`E ⦂ Rep↑ ContextPairF T A`，不假定 resizing 或函子记录相等。
下述显示恢复使用这里的一般泛配对准则及提升表示。

## 3. 显示映射接口与截面项预层

[Display](../theories/DTT/Display/Core.v) 已将以下输入实现为单个
`HasDisplay C P` 类。它不要求 C 存在所有拉回，也不要求终对象或预先给定项。

首先选择类型预层 `TyF : Fct (C^op) SetCat`，并对每个 A 选择
显示映射 `p_A : E_A → Γ`。类型相等 `e : A ≈S B` 作用为指定的
垂直同构 `i_e : E_A → E_B`，保持投影，并满足见证独立、单位和复合律。
类型相等来自 TyF 的广集，而不是反过来由所有显示同构定义。

其次，对每个 σ 选择显示拉回方块，其顶边为：

```text
ℓ_σ,A : E_(A[σ]) → E_A
```

这些顶边还须与类型预层的相等及替换比较对齐。用 ι、κ、ε 表示
TyF 的单位、复合和尊重性等式，应有：

```text
ℓ_id,A ≈ i_ι
ℓ_σ,A ∘ ℓ_τ,A[σ] ≈ ℓ_(σ∘τ),A ∘ i_κ
ℓ_σ',A ∘ i_ε ≈ ℓ_σ,A                         (σ ≈ σ')
ℓ_σ,B ∘ i_(e[σ]) ≈ i_e ∘ ℓ_σ,A               (e : A ≈S B)
```

沿这些同构定义项转换，并以 `Tm Γ A := Sec(p_A)` 定义项。
项的替换由显示拉回的中介态射给出：两条锥腿为 `id_Δ` 和 `s ∘ σ`。
上述图保证这些项操作组成所需的族值预层 T。
这里的 `Sec(p_A)` 复用 [Section](../theories/Cat/Section.v)，相等只比较截面映射。

配对数据 `(σ,s)` 对应 `ℓ_σ,A ∘ s : Δ → E_A`。
反向对 h 取 `σ := p_A ∘ h`，再将锥 `(id_Δ,h)` 分解到沿 σ 的显示拉回，
得到 `Sec(p_(A[σ]))` 中的截面。拉回唯一性证明两个方向互逆及自然性。
这就为第 2 节的构造提供表示；泛变量也可由 `p_A` 沿自身拉回的对角截面取得。

若这些显示映射来自现有 comprehension K，还须说明类型代码如何选到
总范畴的对象、相等与替换如何选到其态射，以及所选替换箭头的笛卡尔性。
K 的泛性质随后可提供显示拉回。它不会自动提供代码分类及指定相等的作用。
后续实现若能从更小的输入推出上述相干图，就应把它们作为派生定理。
本阶段不为尚未使用的通用 split-fibration 接口预设额外字段。

### 已实现的接口及其 CwF 实例

`Display P A` 与 `display_proj P A` 选择显示对象和投影。
`display_conv P e` 选择类型相等的垂直作用，字段只要求它保持投影、
自相等作用为恒等，以及任意复合相等见证的作用等于复合的作用。
`display_conv_witness_independent`、`display_conv_inv` 和
`display_conv_iso` 从这些定律导出，不另存见证独立公理或逆映射。

`display_lift P σ A` 选择替换提升；`display_lift_universal` 使用已有的
`is_pullback` 保存完整泛性质。单位、复合、基底相等和类型相等的四张
相干图分别对应 `display_lift_id`、`display_lift_comp`、
`display_lift_equiv` 和 `display_lift_conv`。
`type_sub_id`、`type_sub_comp`、`type_sub_equiv` 直接取自类型预层的函子律。
共用记号为：

```text
A[σ]TyF[P]    e[σ]EqF[P]
Γ ▹D[P] A    e^D[P]    σ^D[P,A]
```

[Context/Display](../theories/DTT/Context/Display.v) 给出普通定义
`ContextExtension_HasDisplay`：对任意族值预层 T 和选定上下文扩张，
其类型预层为 `FamBaseF ∘F T`，显示对象、投影、转换与提升复用原有构造。
[Context/Pullback](../theories/DTT/Context/Pullback.v) 补充
`context_lift_conv`，证明类型相等与替换提升相容。
两种预层表达方式可能产生不同的相等见证，实例使用已有的见证独立性对齐，
不比较见证本身。该选定显示结构须显式启用，不注册为全局实例。

### 已实现的截面项及其替换

[一般截面操作](../theories/Cat/Section.v) 只使用任意范畴中的交换三角形
或给定拉回方块。`section_of_map_resp f H`（`f ▷Sec[H] s`）将截面 s
送到 f ∘ s，并证明尊重截面及底层映射的相等、恒等和复合定律。
H 是保持投影的见证；定律不比较它或右逆见证的原生相等。
`section_of_pullback_resp HP`（`s[HP]Sec`）分解锥 `(id, s ∘ σ)`，
保存中介态射和右逆见证。`section_of_pullback_β` 给出顶边方程，
`section_of_pullback_unique` 刻画这个截面的唯一性。
构造和 β 见证均透明，不要求 `HasPullback C`。

[Display/Section](../theories/DTT/Display/Section.v) 复用这些操作：

```text
DisplayTerms P Γ A := Sec(display_proj P A)
DisplayTyTm P Γ   := (P Γ, DisplayTerms P Γ)
DisplayTyTmF P    : Fct (C^op) FamCat

e ▸D[P] s      := e^D[P] ▷Sec[display_conv_proj e] s
s[σ]TmD[P]     := s[display_lift_universal σ A]Sec
```

类型 A 由截面的类型推断。`display_term_sub_β` 给出
`σ^D[P,A] ∘ s[σ]TmD[P].1 ≈ s.1 ∘ σ`。
`display_term_sub_conv`、`display_term_sub_id`、`display_term_sub_comp`
和 `display_term_sub_equiv` 分别由四张显示相干图及拉回唯一性推出。
这些定律组成 `display_sub_fam` 和最终的 `DisplayTyTmF P`，
不增加项转换或替换公理，也不预先假设上下文扩张。
其类型广集及类型替换保持为 P 的原有数据。
构造只需显式启用输入的 `HasDisplay C P`，不选择其他结构。

### Display recovery from universal pairs

[Display/Representation](../theories/DTT/Display/Representation.v) now recovers
context extensions from `HasDisplay C P`. Pairing sends `(σ,s)` to
`σ^D[P,A] ∘ s.1`; its inverse sends `h` to the base map `p_A ∘ h`
and the section factoring the cone `(id,h)` through that base map's chosen
display pullback. Equality of base maps converts sections, and pullback
uniqueness proves both inverse laws. The maps preserve the specified equality.

The reusable `section_of_pullback_factor`, its top-edge equation and
uniqueness live in [Section](../theories/Cat/Section.v). Existing section
substitution and its uniqueness theorem reuse this factorization. It requires
only the supplied pullback, retaining the chosen mediator and right-inverse
witness without equating cone or proof witnesses.

`display_generic_pair` factors identity. `display_pair_universal` gives its
unique mediator, the original display pairing. Lift composition and term
substitution prove compatibility with precomposition; comparison witnesses
are aligned by their action. `display_representation` reuses
`universal_element_lifted_representation` on the opposite category to provide
`E_A ⦂ Rep↑ ContextPairF (DisplayTyTmF P) A`. It does not require the native
Hom packaging of `HasContextRepresentation`.

`Display_HasContextExtension` reuses the integrated
`context_extension_of_universal_element`. The recovered projection is equal
to the supplied display projection (`display_context_proj`), and its pairing
computes to the supplied lift composed with the section (`display_context_pair`).
With an independently supplied `HasTerminal C`, `DisplayCwF P` assembles the
CwF. These are ordinary definitions; import enables no chosen model.

### 从泛配对恢复显示结构

[Display/Representation](../theories/DTT/Display/Representation.v) 现已从
`HasDisplay C P` 恢复上下文扩张。配对把 `(σ,s)` 送到
`σ^D[P,A] ∘ s.1`；反向把 h 送到基映射 `p_A ∘ h`，再由沿该基映射
的选定显示拉回分解锥 `(id,h)`，取得截面。基映射相等转换截面，拉回唯一性
证明两侧逆律；两个映射均保持指定相等。

一般的 `section_of_pullback_factor`、上边方程及唯一性放在
[Section](../theories/Cat/Section.v)。原有截面替换及其唯一性定理也复用此分解。
它只需给定的拉回，保留选定中介及右逆见证，不比较锥或证明见证本身。

`display_generic_pair` 分解恒等；`display_pair_universal` 给出其唯一中介，
即原显示配对。提升复合律及项替换证明预合成相容性，比较见证通过其作用对齐。
`display_representation` 在反范畴中复用
`universal_element_lifted_representation`，给出
`E_A ⦂ Rep↑ ContextPairF (DisplayTyTmF P) A`，不要求
`HasContextRepresentation` 的原生 Hom 包装。

`Display_HasContextExtension` 复用已集成的
`context_extension_of_universal_element`。恢复的投影等于给定显示投影
（`display_context_proj`），配对计算为原提升与截面的复合
（`display_context_pair`）。独立提供 `HasTerminal C` 后，`DisplayCwF P`
组装 CwF。这些均为普通定义，导入不会自动启用选定模型。

这完成了给定相干显示结构后的恢复。下一步仍须明确具体 comprehension
如何提供指定类型预层、相等作用与相干提升数据，并比较所得数学数据。
此处不声称任意 comprehension 无条件给出 CwF；第 2 节的必要充分准则
仍以固定类型与项预层 T 为前提。

## 4. Comprehension over chosen type elements / 指定类型元素上的理解结构

[Elements](../theories/Instance/Set/Elements.v) constructs `ElementsCat P`
for a fixed `P : Fct (C^op) SetCat`. Objects are pairs `(Γ,A)`; an arrow
from `(Γ,A)` to `(Δ,B)` retains `σ : Hom Γ Δ` and `A ≈S fmap P σ B`.
Arrow equality compares the base arrows, keeping the Type-valued element
witnesses as data. Every arrow is cartesian for `ElementsBaseF P`: its
element equality supplies the factor's equality, while the prescribed base
factor determines its hom-equality class. Canonical restriction therefore
provides chosen cartesian lifts, with no new global model selection.

A functor `T : Fct (ElementsCat P) C`, a natural projection
`π : T ⇒ ElementsBaseF P`, and `is_comprehension π` suffice as input.
`ElementsComprehension` supplies the canonical lifts to assemble the existing
comprehension interface. No independently chosen cleavage is required.
[Display/Comprehension](../theories/DTT/Display/Comprehension.v) then defines
`Comprehension_HasDisplay P K`: display objects and projections come from K;
conversion and substitution lifts are the images of vertical equality arrows
and canonical element restrictions. Functor identity, composition and
respectfulness derive all conversion/lift coherence laws. The given
comprehension property supplies the display pullbacks. With an independent
`HasTerminal C`, `ComprehensionCwF P K` reuses the existing display recovery.

Conversely, `DisplayElementsComprehension` extends a supplied display
structure along every element arrow: first convert its source type, then
apply the display lift. The existing pullback-transport theorem supplies the
comprehension property along the conversion isomorphism. The display round
trip preserves projection, conversion and lifts in the specified hom equality.
The comprehension round trip has a transparent natural isomorphism
`comprehension_display_iso` between its total-space functor and the original
`ExtF K`; `comprehension_display_projection` preserves the projection.
No equality of functor records, proof fields or chosen cleavages is asserted.
`display_iff_elements_comprehension` records mutual constructibility with P
fixed, rather than a category equivalence for arbitrary comprehension.

This criterion explicitly assumes the type-element presentation. Its vertical
endomorphisms have identity base and hence are equal to identity in the
specified hom equality; an arbitrary total category need not have this
property. For comprehension on a general `E → C`, the next step must supply
an interpretation of the chosen type elements in E, with coherent base
comparison and cartesian preservation. Such interpretation and any stronger
comparison hypotheses are not inferred from fullness or from arbitrary
vertical isomorphisms.

[Elements](../theories/Instance/Set/Elements.v) 为固定的类型预层构造
`ElementsCat P`。对象为 `(Γ,A)`；从 `(Γ,A)` 到 `(Δ,B)` 的态射保留
`σ : Hom Γ Δ` 及 `A ≈S fmap P σ B`。态射相等只比较基底映射，Type 值元素
见证仍作为数据保留。每条态射对 `ElementsBaseF P` 均为笛卡尔的：元素相等
提供分解的相等见证，给定基底分解确定其 Hom 相等类。因此标准限制提供选定
笛卡尔提升，不新增全局模型选择。

全空间函子 T、自然投影 `π : T ⇒ ElementsBaseF P` 及其
`is_comprehension π` 已足够作为输入；`ElementsComprehension` 使用标准提升
组装既有接口，不另假设选定 cleavage。`Comprehension_HasDisplay P K` 取 K
的全空间对象及投影，把垂直相等箭头及标准元素限制映为转换和替换提升。
函子的恒等、复合及尊重性导出全部相干律；给定理解泛性质提供显示拉回。
另选 `HasTerminal C` 后，`ComprehensionCwF P K` 复用已有显示恢复。

反向的 `DisplayElementsComprehension` 把元素箭头送到先转换、再提升的复合，
并复用拉回沿转换同构的运输定理。显示结构往返在指定 Hom 相等下保持投影、
转换和提升；理解结构往返的全空间函子通过透明自然同构比较，并保持投影。
不要求函子记录、证明字段或选定 cleavage 相等。固定 P 的互构准则不声称
任意理解结构之间的范畴等价。

此准则明确假设类型元素表述。其垂直自态射的基底为恒等，因而在指定 Hom
相等下等于恒等；任意总范畴不必具有此性质。对一般 `E → C` 上的理解结构，
下一步仍须给出类型元素在 E 中的解释、相干基底比较及笛卡尔保持。解释及更强
比较所需的假设，不能由满性或任意垂直同构自动取得。

## 5. Restriction across a natural base comparison / 跨自然基底比较的限制

The general prerequisite lives in
[Comprehension](../theories/Cat/Comprehension.v). Given projections
`P : Fct E B`, `Q : Fct D B`, an interpretation `S : Fct D E`, a natural
isomorphism `β : (P ∘F S) ≅N Q`, and `π : T ⇒ P`, it forms
`ComprehensionRestrictionN S β π := β.1 ∘Nv (π ∘Nr S)`.
Whiskering and vertical composition supply naturality; no object or functor
record equality is needed.

`comprehension_restrict_universal` assumes `is_comprehension π` and explicitly
requires `S` to send each Q-cartesian arrow to a P-cartesian arrow. The source
property supplies a pullback; naturality of β identifies its base boundary.
[Pullback](../theories/Cat/Pullback.v) transports this square using the existing
`pullback_base_iso` and the new `pullback_postcompose_mono`. Postcomposition
needs only a monic outgoing boundary; changing the other base object needs
an invertible incoming boundary. `pullback_base_boundary` packages both steps.
The cone transport and `iso_mono` cancellation remain transparent even when
the original mediator computes from a Type-valued cone witness.

`RestrictedComprehension` adds exactly a supplied `HasCartLift Q`. Source
chosen lifts, fullness and essential surjectivity are unnecessary. This is
an independent general prerequisite: it does not construct a type presheaf
or an interpretation from arbitrary comprehension. Specializing to
`D := ElementsCat A`, `Q := ElementsBaseF A` still requires the interpretation,
base comparison and cartesian preservation; element theory then supplies the
target lifts. The specialized display/CwF construction is a subsequent step.

一般前置位于 [Comprehension](../theories/Cat/Comprehension.v)。给定投影
`P : Fct E B`、`Q : Fct D B`、解释 `S : Fct D E`、自然同构
`β : (P ∘F S) ≅N Q` 及 `π : T ⇒ P`，以须化和垂直复合构造新的自然投影，
不要求对象或函子记录相等。`comprehension_restrict_universal` 使用源候选
理解泛性质，并显式要求 S 将 Q-笛卡尔箭头送到 P-笛卡尔箭头。

源泛性质提供拉回，β 的自然性提供基底边界方程；复用既有基底同构运输及新的
后合成单态射定理得到目标方形。出边界只需为单态射，另一基底对象的改变需要
可逆入边界；`pullback_base_boundary` 组织两步。锥见证运输与 `iso_mono`
消去均保持透明，即使原中介会读取 Type 值锥见证也可计算。

`RestrictedComprehension` 只再使用给定的 `HasCartLift Q`，不需要源选定提升、
满性或本质满，也不会自动启用模型。这是独立的一般前置，不从任意理解结构
生成类型预层或解释。后续专门化到类型元素时，仍需给定解释、自然基底比较及
笛卡尔保持；元素理论可提供目标提升，显示结构与 CwF 的专门构造留待下一阶段。

## 6. 宇宙与验证

表示准则不合并上下文 hom、类型、项及其相等见证的层级。
现有 [Universes.v](../tests/Universes.v) 新增四项检查，覆盖两种大小排列下的
双向结构转换及 `RepresentedCwF`。
以全部截面作为项时，截面载体要容纳态射及其右逆见证；
不能无条件把它放回更小的预设项层级，也不引入 resizing。
截面构造现已显式分离载体层级 s 与范畴定律的辅助层级 l：
只需 hom 层级和相等见证层级均不高于 s，不要求 l 不高于 s。
若 hom 与相等见证分别处于 h、p，截面相等仍处于 p；
两种大小排列分别容许 `Sec(p_A) : SetC@{p p}` 和 `SetC@{h p}`。
`DisplayTerms` 和最终组装的函子保留这一区分。

本轮在 Rocq 9.0.1 / Dune 3.21.0 下完成完整构建。
表示准则首次实现时，18 项临时构造／模型假设检查均无额外公理。
布尔 Code/El 实例检查恢复后的投影、变量、配对及非平凡类型转换可直接计算，
并用一个逐点取反项的非平凡自然自同构改变表示：恢复的泛变量和配对确实随之改变，
确认反向构造使用了传入的表示。还检查两方向的选定结构需显式启用。
这些实例及假设输出保留在仓库外；没有新增永久布尔测试模块。
显示映射接口的后续验证也复用同一原则：在已有宇宙检查中增加四项，
覆盖两种大小排列下的选定显示结构及派生同构。21 项新的临时假设检查
均无额外公理；布尔实例中，两种相等见证的非平凡转换、逆映射、替换提升
和拉回中介都可直接计算。临时检查还确认选定结构不会被自动启用，
且小类型预层可配合两种较大的上下文 hom／相等层级。

一般可表性整理增加六项永久宇宙检查：协变和反变的通用元素准则、
表示对象同构，以及两种 hom／相等大小排列下的 Yoneda 同构。
56 项临时假设检查覆盖一般理论及 CwF 专用构造，均无额外公理，
并重跑原有的布尔模型和非平凡表示，确认泛变量、中介及双向映射仍能直接计算。
还检查对象宇宙大于 hom／相等宇宙，以及提升后的载体／相等层级分别较大的情形。
一个带布尔相等见证的临时单对象模型直接归约 `representation_at` 返回的见证；
为此，Yoneda 的求值互逆律使用透明的自然性和尊重性组合，避免不透明证明阻断计算。
具体提交的多版本 CI 状态记录在 [#13](https://github.com/Godalin/rocq-cats/issues/13)。

截面项预层这一轮在已有宇宙检查中增加四项，覆盖最终函子的两种
hom／相等大小排列，并要求项载体可小于范畴定律的辅助层级。
临时检查还覆盖小类型预层配合较大的上下文 hom、相等及对象层级，
并确认输入的显示结构须显式启用。
布尔 Code/El 显示模型验证两种相等见证的非平凡转换、逆转换、
连续替换，以及组装后的 CwF 项接口操作均能直接归约。
通用截面操作的计算、共享记号的作用域及连续使用也在临时检查中验证。
33 项新的临时 `Print Assumptions` 检查均无额外公理。
这些计算实例和假设输出不加入永久测试；完整构建使用
Rocq 9.0.1 / Dune 3.21.0，CI 状态另在 issue 中记录。

泛配对准则的独立大小回归另增加八项永久检查：固定小类型预层、项载体及
项相等层级，在 `h < p < l < o` 和 Hom／相等层级对调两种排列下检查
准则、提升表示及中介往返。项载体严格小于范畴定律的辅助上界。
临时检查还固定彼此独立、均高于上下文 Hom 的类型及项载体／相等层级。
布尔 Code/El 模型的九项直接计算覆盖原中介、恢复中介、非平凡类型转换、
两种 Type 值相等见证、提升表示正逆映射及原生表示恢复。
十项临时假设审计均无额外公理；这些模型与输出不加入永久测试。
定向检查使用 Rocq 9.2、Stdlib 9.2.0 和 Dune 3.23.1。

Display recovery adds eight fixed universe checks for universal pairs, lifted
representations, context extensions and the completed CwF's term setoids.
They keep `Set < h < p < l < o`, swap hom/equality levels, and retain term
carriers below the category-law bound. Temporary checks also use independent,
larger type carrier/equality levels. Fourteen Boolean computations cover
factorization, pairing, projection, generic terms, nontrivial conversion,
substitution, the lifted representation and the completed model. A separate
single-object category uses Boolean hom-equality witnesses: three direct
reductions retain the chosen right-inverse and top-edge witnesses without
comparing cone witnesses. All 21 temporary assumption reports are closed;
chosen context extensions and CwFs still require explicit enabling. These
temporary models and outputs stay outside the library. The checks use the
project switch with Rocq 9.2, Stdlib 9.2.0 and Dune 3.23.1.

显示恢复另增八项固定宇宙检查，覆盖泛配对、提升表示、上下文扩张及最终 CwF
的项广集；保持 `Set < h < p < l < o`，对调 Hom／相等层级，项载体仍严格
低于范畴定律上界。临时检查还使用独立且更大的类型载体／相等层级。
十四项布尔直接计算覆盖分解、配对、投影、泛项、非平凡转换、替换、提升表示
及最终模型。另一单对象范畴使用布尔 Hom 相等见证，三项直接归约保留选定
右逆及上边见证，不比较锥见证。二十一项临时假设报告全部闭合，选定上下文
扩张及 CwF 仍须显式启用。临时模型和输出不加入库，验证使用项目 switch
中的 Rocq 9.2、Stdlib 9.2.0 和 Dune 3.23.1。

Type-element comprehension adds twelve fixed universe regressions. With
`Set < h < p < l < a < b < o`, the type presheaves use carrier/equality
levels `(a,b)` and `(b,a)`. Element hom carriers contain the type-equality
witnesses, while their hom equality remains at the base equality level;
the recovered CwF terms still have levels `(p,p)` and `(p,h)`. The criterion,
canonical lifts and total-space natural isomorphism pass at these levels.
Temporary Boolean models check eighteen native reflexivity computations and
one specified-equality law, including distinct stored element witnesses,
nontrivial conversion, term substitution, recovered pairing/generic terms,
the completed model and both comparison directions. All 33 new public
declarations and three concrete chosen-model reports are closed. Explicit
choice probes reject automatic display/CwF selection. These models and
assumption outputs remain outside the repository.

类型元素上的理解结构另增十二项固定宇宙回归：在
`Set < h < p < l < a < b < o` 下，类型预层分别使用 `(a,b)` 与 `(b,a)`
载体／相等层级。元素 Hom 载体容纳类型相等见证，Hom 相等仍处于基底相等
层级；恢复 CwF 的项仍为 `(p,p)` 与 `(p,h)`。互构准则、标准提升及全空间
自然同构在这些层级通过。临时布尔模型验证十八项原生反身计算及一项指定相等
定律，包括不同的已存元素见证、非平凡转换、项替换、恢复的配对与泛项、最终
模型及双向比较。33 个新公开声明及三个具体选定模型的假设报告均闭合；显式
选择探针确认不会自动启用显示结构或 CwF。临时模型和假设输出不加入仓库。
