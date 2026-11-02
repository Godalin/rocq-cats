# 常用小范畴与图式

统一导入 [Cat.Shape](../theories/Cat/Shape.v) 可使用形状范畴；
导入 [Cat.Diagram.Shape](../theories/Cat/Diagram/Shape.v) 还可使用常用图式与记号。
已有二元积、余跨度图式及其极限对应保持可用。

图式按数学主题分组，也可以单独导入：

- [Cat.Diagram.Discrete](../theories/Cat/Diagram/Discrete.v)：离散、空、单点和二元图式。
- [Cat.Diagram.Span](../theories/Cat/Diagram/Span.v)：跨度、余跨度及其锥。
- [Cat.Diagram.Arrow](../theories/Cat/Diagram/Arrow.v)：单箭头、平行箭头和同构图式。
- [Cat.Diagram.Square](../theories/Cat/Diagram/Square.v)：交换方形图式。

## 目录与构造

| 范畴 | 对象与生成态射 | 用途 |
| --- | --- | --- |
| `EmptyShape` | 无对象 | 空图式，其极限是终对象 |
| `PointShape` | 一个对象，只生成恒等路径 | 单对象取值 |
| `DiscreteCat V` | 任意顶点类型，无生成边 | 以 V 为指标的积 |
| `PairShape` | 两个离散对象 | 二元积 |
| `ArrowShape` | `false → true` | 单个态射 |
| `SpanShape` | 共同顶点向两个端点发出箭头 | 跨度，推出的形状 |
| `CospanShape` | 两个端点指向共同顶点 | 余跨度，拉回的形状 |
| `ParallelShape` | 两条不同的 `false → true` 箭头 | 等化子的形状 |
| `SquareShape` | 四个对象，方形的两条复合路径相等 | 交换方形 |
| `IsoShape` | 两个对象及互逆箭头 | 选定同构 |
| `[Ord n]` | n+1 个对象，从 0 到 n，按顺序有箭头 | 有限可复合链 |
| `CodiscreteCat V` | 任意两个对象之间恰有一个箭头代表 | 余离散群胚 |

`OrdinalOb n` 是用有限和构造的 n 个位置；`ordinal_first` 与
`ordinal_next` 构造位置，`ordinal_rank` 计算从零开始的编号。
`DiscreteCat (OrdinalOb n)` 给出 n 个离散对象。
`ordinal_from_first` 提供有限链中从第一个对象出发的箭头。

另有 [NatOrderCat](../theories/Instance/Nat/Order.v)，是按通常顺序排列的
自然数范畴。其 `NatLe` 是递归计算为 unit 或 Empty_set 的 Type 值关系，
不把可用于计算的关系见证换成 Prop-only 接口。

## 两类构造基础

离散、余跨度和平行箭头形状复用 [自由范畴](../theories/Cat/Free.v)。
`LabelledArrowGraph S` 将广集 S 放在两个顶点之间；平行箭头取布尔标签的
原生相等作为指定相等，因而两个标签不会自动相等。
跨度由已有余跨度取反得到。

[PreorderCat](../theories/Cat/Preorder.v) 把 Type 值预序见证作为态射，
将同端点见证的指定相等定义为 unit。它没有要求见证的原生相等或证明无关性。
`PreorderF` 把保持关系的映射变成函子。
两点布尔预序给出箭头范畴，`ArrowShape ×C ArrowShape` 给出真正交换的方形；
余离散构造给出步行同构。有限链则从自然数预序沿位置编号拉回。

自由方形只提供两条路径，本身不会让它们交换；这里的 `SquareShape`
明确包含这项指定相等。类似地，`IsoShape` 的两条箭头确实互逆，
并非仅有一对方向相反的自由生成边。

## 图式接口

对任意目标范畴 C，可构造：

```text
EmptyDiagram C
PointDiagram X
⟨f⟩D                   单箭头
⟨f ←→ g⟩D              跨度
⟨f →← g⟩D              余跨度
⟨f ⇉ g⟩D               平行箭头
⟨f, g; h, k | H⟩□      H : h ∘ f ≈ k ∘ g
⟨i⟩≅D                  i : X ≅[C] Y
```

方形顶点按 `(纵向位置, 横向位置)` 排列：
`(false,false)` 是左上，`(false,true)` 是右上，
`(true,false)` 是左下，`(true,true)` 是右下。
四条边分别解释为 f、g、h、k；其行为有独立的 hom 相等引理。

`ArrowN` 从一个交换方形得到两个箭头图式之间的自然变换。
[函子去柯里化](../theories/Cat/Functor/Uncurry.v) 将
`F : Functor A (Fct B C)` 变成 `F^uncF : Functor (A ×C B) C`；
`α^uncN` 同时去柯里化自然变换，且保留自然同构。
`SquareDiagram` 直接复用这项通用理论，将 H 作为 `ArrowN` 的自然性，
再去柯里化，不为方形另写一套长复合证明。

`ArrowCone` 和 `ParallelCone` 构造常用锥；平行图式的锥满足
`parallel_cone_comm`，可用于后续等化子接口。
箭头与平行图式对输入态射的指定相等是 respectful 的，输出比较为自然同构。

## 验证与范围

[宇宙回归](../tests/Universes.v) 同时检查两种目标范畴 hom 载体／相等见证
大小排列，覆盖箭头、跨度、平行箭头、交换方形和同构图式。
通用预序范畴还检查大态射载体与小 hom 相等见证的组合。

Rocq 9.0.1、OCaml 5.3.0、Nix Dune 3.23.1 下完整
`dune build @all @runtest @install` 通过。
40 项临时 `Print Assumptions` 均无额外假设。
临时实例检查图式的边解释计算、方形对角线计算、非平凡同构的正逆计算、
有限序数的编号与方向，以及平行生成箭头的可区分性。
这些实例和假设输出没有加入常驻测试。

这些范畴均可直接作为一般极限的索引；当前专用的泛性质对应仍是二元积和拉回。
本轮不增加等化子或推出结构，也不声称任意目标范畴具有这些形状的极限。
任意带关系的图呈示和一般小范畴的分类不属于这份常用形状目录。
