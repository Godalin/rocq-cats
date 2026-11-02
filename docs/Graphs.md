# 图、自由范畴与极限形状

## 图的基础层

[Graph.Core](../theories/Graph/Core.v) 与基础集合目录同级，只依赖集合基础：

```text
Graph:
  Vertex : Type
  EdgeSet : Vertex → Vertex → SetC

x →[G] y       边载体
x →*[G] y      路径载体
```

顶点与范畴的对象一样使用 Type；不额外指定顶点等价及其运输。
边使用广集，边相等及等价律直接来自 `EdgeSet`。
图不选择恒等边或边复合。

[Graph.Morphism](../theories/Graph/Morphism.v) 的 `G →G H` 保存顶点函数和
边的 respectful maps，提供恒等图映射与复合 `∘G`。
这里没有通过比较顶点函数或证明字段的原生相等建立图映射范畴。

## 路径与自由范畴

[Graph.Path](../theories/Graph/Path.v) 用三个构造表示形式路径：

```text
εG x         空路径
ιG e         一条生成边
g ∘P f       路径连接
```

路径保留括号。`≈P` 是由边相等、单位律、结合律及相容的等价闭包生成的
Type 值关系。路径代表无需规范化，也无需比较端点运输的见证。
这些关系正好为 [FreeCat](../theories/Cat/Free.v) 提供 hom 广集及范畴律。

`UnderlyingGraph C` 只忘掉范畴的恒等与复合结构。
给定图解释 `D : G →G UnderlyingGraph C`，`FreeF D` 把空路径解释为恒等、
生成边解释为指定态射、连接解释为复合。
respectfulness 对路径相等的生成规则归纳证明。

`free_extend_β` 表达延拓在生成边上的行为；`RestrictGraph F` 从任意函子取出
生成边解释，`free_extend_η` 证明重新延拓后的路径解释按 hom 指定相等恢复。
`free_extend_nat_iso` 将恢复比较组织为自然同构，不使用函子记录的相等。

`FreeN` 进一步将生成边上的自然性推广到所有路径。
[FreeCone](../theories/Cat/Diagram/Free.v) 复用该构造：给每个顶点一条锥腿，
只需证明每条生成边的交换方程，就得到真正的自然变换锥。

## 具体形状与极限

[Diagram.Shape](../theories/Cat/Diagram/Shape.v) 提供：

| 构造 | 生成图 | 图式与锥 |
| --- | --- | --- |
| 离散图式 | 任意顶点类型，没有生成边 | `DiscreteF`、`DiscreteCone` |
| 二元积 | 两个顶点，没有生成边 | `⟨X, Y⟩D`、`⟨p, q⟩Cone` |
| 拉回 | 两条边指向共同顶点 | `⟨f →← g⟩D`、`CospanCone` |

`PairShape` 是两点离散图的自由范畴；`CospanShape` 是
[CospanGraph](../theories/Graph/Shape.v) 的自由范畴。
锥在所有路径上的交换性均由通用生成边定理提供。

[Limit.Product](../theories/Cat/Limit/Product.v) 证明任意两点离散图式的
极限泛性质等价于两条锥腿的积泛性质。
`ProductLimits` 从选定积得到该形状的全部选定极限，
`PairLimitsProduct` 从该形状的选定极限恢复选定积。

[Limit.Pullback](../theories/Cat/Limit/Pullback.v) 对任意余跨度图式建立同样的
双向对应，提供 `PullbackLimits` 和 `CospanLimitsPullback`。
第三条锥腿由任一侧复合决定；证明只比较态射，不比较交换性见证。

这些选定结构只通过显式定义启用，不由导入全局注册。
它们可直接传给 `LimitAdjunction`，得到相应形状的对角函子右伴随。
右伴随保持积、拉回则直接由一般极限保持定理和上述泛性质对应导出，
不重新证明模型专属的中介唯一性。

## 大小与验证

[有限生成图](../theories/Graph/Finite.v) 通过邻接计数选择有限顶点与有限边标签。
[生成边极限构造](../theories/Cat/Limit/Graph.v) 只对顶点和生成边取积，
不枚举所有路径；[有限版本](../theories/Cat/Limit/Graph/Finite.v) 从终对象、
二元积和等化子得到这些自由图式的选定极限。
其中总边索引的依赖和通过一般的
[嵌套积构造](../theories/Cat/Product/Sigma.v) 处理。

图的顶点、边载体、边相等见证宇宙相互独立。
路径载体需要容纳中间顶点及边；当前路径相等的生成见证也包含这些数据。
其推导大小分别为 `max(Set,o,e)` 和 `max(Set,o,e,p)`。
这没有给图本身施加 `e ≤ p` 或 `p ≤ e`。
自由范畴的 hom 载体可另行提高，而不强制其相等见证随之提高。

[宇宙回归](../tests/Universes.v) 检查边大小的两种排列、大顶点图、
提高载体但不提高相等见证，以及向两种 hom 大小排列的范畴解释路径。
还检查积和拉回的两组对角伴随在两种目标 hom 大小排列下均能构造。

本地完整构建使用 Rocq 9.0.1、OCaml 5.3.0、Nix Dune 3.23.1。
临时检查另覆盖非平凡边代表的相等、路径解释的计算、积／拉回中介的计算、
选定结构往返后的计算，以及相等见证的解释计算；31 项新基础构造及其对角伴随的
`Print Assumptions` 均报告无额外假设。
这些实例及假设输出不加入常驻理论源文件；本地结果不等同于多版本 CI。

自由图式不自动施加额外交换关系。[常用小范畴](./SmallCategories.md)
另以通用预序范畴提供交换方形、有限链及步行同构，并补充箭头、跨度和平行箭头。
等化子与空图极限已具备专用接口；带额外路径关系的图呈示仍待后续构造。
