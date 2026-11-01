# 从表示与 comprehension 恢复 CwF

本轮先完成一个精确的反向准则：**固定族值预层 T 时，选定上下文扩张与
选定配对预层表示可互相构造。**
[ContextRepresentation](../theories/DTT/Context/Representation.v) 已实现该结果。
从一般 comprehension 提取 T 的部分另行设计，边界如下。

## 1. 现有 comprehension 提供什么

对 `P : Functor E C`，已有的
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

输入已有的 `T : Functor (C^op) FamCat`。它已经给出类型、项、指定相等、
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

## 3. 下一阶段：从显示映射得到这样的 T 和表示

一个可以落实的充分输入如下。它不要求 C 存在所有拉回。

首先选择类型预层 `TyF : Functor (C^op) SetCat`，并对每个 A 选择
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

这个显示映射方案是下一阶段的充分条件设计，尚未实现。
已证明的必要充分性是第 2 节固定 T 后的表示准则。

## 4. 宇宙与验证

表示准则不合并上下文 hom、类型、项及其相等见证的层级。
现有 [Universes.v](../tests/Universes.v) 新增四项检查，覆盖两种大小排列下的
双向结构转换及 `RepresentedCwF`。
未来以全部截面作为项时，截面载体要容纳态射及其右逆见证；
不能无条件把它放回更小的预设项层级，也不引入 resizing。

本轮在 Rocq 9.0.1 / Dune 3.21.0 下完成完整构建。
18 项临时构造／模型假设检查均无额外公理。
布尔 Code/El 实例检查恢复后的投影、变量、配对及非平凡类型转换可直接计算，
并用一个逐点取反项的非平凡自然自同构改变表示：恢复的泛变量和配对确实随之改变，
确认反向构造使用了传入的表示。还检查两方向的选定结构需显式启用。
这些实例及假设输出保留在仓库外；没有新增永久布尔测试模块。
具体提交的多版本 CI 状态记录在 [#13](https://github.com/Godalin/rocq-cats/issues/13)。
