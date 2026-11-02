# 极限、Hom 同构与伴随

## 图式与锥

[Diagram](../theories/Cat/Diagram.v) 复用函子和自然变换：

```text
D : Functor J C
ConstF J X : Functor J C
Δ[J,C] : Functor C (Fct J C)
κ : X ⇒Δ D := ConstF J X ⇒ D
κ ∘Cone f : Y ⇒Δ D       （f : Hom Y X）
```

`⇒Δ` 的双箭头表示自然变换，`Δ` 表示将左侧顶点视为常图式。
锥的交换性就是自然变换的自然性，不另存一套交换图。
锥范畴 `ConeCat D` 的对象包含顶点和锥；态射包含顶点映射及交换性见证，
相等只比较指定的底层态射相等。见证保留在 Type 中，不比较见证本身。
`MapCone F κ` 将函子作用于锥的各条腿。

[图与自由范畴](./Graphs.md) 提供形状的生成设施：由顶点及生成边构造自由范畴，
再将边赋值延拓成图式。二元积对应两点离散形状，拉回对应余跨度形状；
它们与既有专用泛性质及选定结构的双向对应分别位于
[Limit.Product](../theories/Cat/Limit/Product.v) 和
[Limit.Pullback](../theories/Cat/Limit/Pullback.v)。

[Limit.Terminal](../theories/Cat/Limit/Terminal.v) 和
[Limit.Equalizer](../theories/Cat/Limit/Equalizer.v) 补齐空图式和平行箭头的对应：

| 形状 | 专用泛性质 | 选定结构的双向构造 |
| --- | --- | --- |
| 空范畴 | 终对象 | `TerminalLimits` / `EmptyLimitsTerminal` |
| 两点离散范畴 | 二元积 | `ProductLimits` / `PairLimitsProduct` |
| 平行箭头 | 等化子 | `EqualizerLimits` / `ParallelLimitsEqualizer` |
| 余跨度 | 拉回 | `PullbackLimits` / `CospanLimitsPullback` |

这些对应适用于该形状的任意图式，不只适用于指定构造器产生的图式。
`EmptyCone` 构造空图式上的锥；`ParallelConeOver` 从一条等化两条生成箭头的
态射构造锥，另一条腿由复合决定。

## 等化子接口

[Equalizer](../theories/Cat/Equalizer.v) 区分候选性质与选定结构：

```text
e ⦂ Eq(f,g) := is_equalizer f g E e
HasEqualizer C
Eq[f,g]             选定等化子对象
ιeq[f,g]            到 f、g 的公共定义域的态射
eq⟨q,H⟩             由 H : f ∘ q ≈ g ∘ q 得到的唯一中介
```

候选泛性质同时包含交换性和 Type 值的唯一中介。
`equalizer_β`、`equalizer_η`、`equalizer_proper` 与 `equalizer_comp`
由泛性质导出，比较中介时不比较交换性见证。
`equalizer_hom_ext` 给出等化子箭头的消去性质；
对象唯一性 `equalizer_unique` 在极限对应模块中复用 `limit_unique`。
选定结构转换均须显式启用，不通过导入注册全局模型结构。

## 有限极限的两套基础数据

[Limit.Finite](../theories/Cat/Limit/Finite.v) 提供三项显式构造：

- `PullbackProduct`：终对象和拉回给出二元积，即沿 `X → 1 ← Y` 拉回。
- `ProductEqualizerPullback`：二元积和等化子给出拉回；对
  `f : X → Z`、`g : Y → Z`，取 `f ∘ π1` 与 `g ∘ π2` 在 `X × Y` 中的等化子。
- `ProductPullbackEqualizer`：二元积和拉回给出等化子，即将
  `⟨f,g⟩ : X → Y × Y` 与对角箭头 `⟨id,id⟩ : Y → Y × Y` 拉回。

`PullbackEqualizer` 先使用派生的积，再执行第三项构造，因而只要求终对象和拉回。
候选证明 `product_equalizer_pullback` 与 `pullback_equalizer` 接受候选泛性质，
不要求将相应的等化子或拉回注册为全局选定结构。
积的构造复用已有 `pullback_product`；该证明现在透明，以便提取中介并直接计算。

`finite_limit_bases` 将这些构造组织为 Type 值的双向转换：

```text
(HasTerminal C ∧ HasPullback C)
  ↔ (HasTerminal C ∧ HasProduct C ∧ HasEqualizer C)
```

两个方向保留给定终对象；不要求往返后的结构记录相等。
这一步比较两套基础数据，尚未定义一般有限形状的接口，
也尚未形式化由这些数据构造任意有限图式极限的定理。

## 泛性质与选定结构

[Limit](../theories/Cat/Limit.v) 区分候选与选定极限：

```text
κ ⦂ Lim(D) := is_limit κ
HasLimit C D
HasLimitsOfShape C J
```

`is_limit κ` 要求每个锥 μ 都具有唯一的中介态射 h，使
`κ ∘Cone h ≈N μ`。唯一性使用 C 指定的 hom 相等。
`HasLimit C D` 选择顶点 `lim D`、锥 `πlim[D]` 和这项泛性质。
中介 `lim⟨ μ ⟩` 从泛性质提取，不重复存储。

`limit_β`、`limit_η`、中介对锥相等及预合成的相容性均由泛性质证明。
`limit_iff_terminal` 将极限锥刻画为锥范畴的终对象；
`limit_unique` 复用终对象唯一性，再沿 `ConeApexF` 得到顶点同构。
为使该同构的正逆映射能够计算，已有 `terminal_unique` 的证明改为透明的
`Defined`；其陈述与证明内容不变。

## 极限函子和对角伴随

选择 `HasLimitsOfShape C J` 后，对自然变换 `α : D ⇒ E` 定义：

```text
limit_map α := lim⟨ α ∘Nv πlim[D] ⟩
LimitF : Functor (Fct J C) C
```

respectfulness、恒等律、复合律从唯一性导出。
不再要求调用者选择相干的 limit maps 或证明另一套函子律。

[Limit.Adjunction](../theories/Cat/Limit/Adjunction.v) 将上述泛性质组织为：

```text
Hom_Fct(Δ X, D) ≅S Hom_C(X, lim D)
LimitAdjunction : Δ[J,C] ⊣ LimitF
```

正向映射取中介，逆向映射将极限锥沿态射预合成。
两个变量的自然性分别是中介对预合成、图式自然变换的相容性。
伴随的两侧 Hom 函子复用一般 `HomF` 的函子律；
逆对应的自然性、单位、余单位和三角恒等式由伴随理论导出。

反过来，任意 `Δ[J,C] ⊣ R` 的余单位分量提供极限锥，给出构造性的双向对应：

```text
HasLimitsOfShape C J
  ↔ ∃ R : Functor (Fct J C) C, Δ[J,C] ⊣ R
```

这是存在性与选定结构之间的 Type 值双向构造，不要求两次构造后记录原生相等。
具体的选定结构只通过显式定义启用，不由导入自动注册。

## 右伴随保持极限

[Limit.Preservation](../theories/Cat/Limit/Preservation.v) 对任意 `A : F ⊣ G`
证明 `right_adjoint_preserves_limit`：若 κ 是 D 中某个图式的极限，
`MapCone G κ` 就是像图式在 C 中的极限。

证明将输入锥的每条腿沿 Hom 同构反向转置，使用原极限的泛性质，
再正向转置中介。锥的自然性、分解与唯一性均复用一般伴随和极限定律。
它只要求给定图式已有极限，不要求两个范畴具有所有该形状的极限。

形状对应模块据此导出 `right_adjoint_preserves_terminal`、
`right_adjoint_preserves_product`、`right_adjoint_preserves_equalizer` 和
`right_adjoint_preserves_pullback`。这些结论以候选泛性质为输入，
无需在两侧选择新的终对象、积、等化子或拉回。

## 大小与验证边界

图式形状 J 的对象、态射和相等见证可以有自己的宇宙。
锥、锥态射及定律的宇宙可以相应提高；C 的原生 hom 载体和相等见证仍独立。
Hom 自然同构使用共同广集宇宙的显式提升，不使用 resizing。

[宇宙回归](../tests/Universes.v) 同时检查两种 hom／相等见证大小排列，
以及对象宇宙大于两者的图式形状。具体模型的可用极限与大小界须逐一建立，
这里没有断言任意范畴具有极限，也未将任意 Type 值交换见证降到 Prop。

本轮构建与临时假设／计算检查结果记录到相关 issue。
永久新增测试限于宇宙接口回归，临时广集模型与假设输出不加入理论源文件。
