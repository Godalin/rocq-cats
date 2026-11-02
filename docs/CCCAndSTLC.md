# CCC 与简单类型 λ 演算的指称语义

本笔记对应 [#20](https://github.com/Godalin/rocq-cats/issues/20)，
语法、语法范畴和自由 CCC 的实现归 [#9](https://github.com/Godalin/rocq-cats/issues/9)。
目标是逐步证明 STLC 的 βη 等式在所有 CCC 模型中可靠且完备。
当前增量补齐指数对象的基本计算律和通用伴随理论；
下文的完整语法解释与完备性仍是设计。

## 1. 已有基础与本次增量

[CCC](../theories/Cat/CCC.v) 已组合选定的终对象、二元积和指数对象。
这些结构都从 Type 值泛性质提取中介态射。
态射相等是 `HomSet` 指定的 `HomEq`，无需比较函数或证明字段的 Rocq 相等。

[Product](../theories/Cat/Product.v) 已有 `product_β1`、`product_β2`、
`product_η` 以及配对的复合律 `product_comp_r`、`product_comp_l`。
[Terminal](../theories/Cat/Terminal.v) 已有终对象箭头唯一性 `term_η`
和替换相容性 `term_comp_l`。本次补充 `cross_proper`、`cross_id`、`cross_comp`，
使 `f × g` 的相等、单位与复合行为可直接使用。

[Exponential](../theories/Cat/Exponential.v) 本次提供：

```text
uncurry g := eval ∘ (g × id)
exponential_β: uncurry (curry f) ≈ f
exponential_η: curry (uncurry g) ≈ g

exponential_curry_comp_r:
  curry (f ∘ (σ × id)) ≈ curry f ∘ σ

exponential_map k := curry (k ∘ eval)
exponential_curry_comp_l:
  curry (k ∘ f) ≈ exponential_map k ∘ curry f
```

`curry`、`uncurry`、`exponential_map` 均尊重指定相等；
`exponential_map` 还满足单位与复合律。
这些结果只需要选定的积与指数对象，无需终对象或完整 CCC。

[ExponentialHom](../theories/Instance/Set/ExponentialHom.v) 将这两个尊重映射
及 βη 打包为任意源范畴 C 的广集同构：

```text
exponential_hom_iso:
  HomSet (Z × X) Y ≅[SetCat] HomSet Z (Y ^ X)
```

此处 `SetCat` 只用于表达 hom 广集之间的同构，不选择 C 为集合模型，
也不启用 `SetCat_CCC`。上面的两条 `curry_comp` 定律分别给出 Z 的逆变
和 Y 的协变自然性方程；`exponential_hom_nat_iso` 通过通用伴随理论
将它们打包为双函子之间的自然同构，必要时显式提升到共同的广集宇宙。
X 在这个伴随问题中固定；让 X 也变化的指数双函子是另一个可复用增量。

## 2. 从类型、上下文和项得到态射

建议 #9 的第一阶段选择一组基类型 B，暂不加入常量：

```text
A ::= base b | 1 | A × A | A → A
```

这是语法实现的建议，尚未定义第二套语法。以后加入类型为 A 的闭常量 c 时，
签名解释额外选择 `I(c) : Hom 1 ⟦A⟧`；在上下文中以 `I(c) ∘ !` 解释。

给定任意 `C : Cat`、显式的 `CCC C` 及基类型解释 `I : B → Ob C`：

| 语法 | 解释 |
| --- | --- |
| 基类型 b | I(b) |
| 单位类型 1 | 选定终对象 1 |
| 积类型 A × B | ⟦A⟧ × ⟦B⟧ |
| 函数类型 A → B | ⟦B⟧ ^ ⟦A⟧ |
| 空上下文 · | 1 |
| 上下文 Γ, A | ⟦Γ⟧ × ⟦A⟧ |
| 判断 Γ ⊢ t : A | 态射 ⟦t⟧ : Hom ⟦Γ⟧ ⟦A⟧ |

上下文递归按上表括号化。`1 × A ≅ A` 是同构，不把它当作对象的原生相等。
最新变量解释为 `π2`，旧变量的解释沿 `π1` 复合。
单位项解释为 `!`，配对解释为 `⟨⟦t⟧, ⟦u⟧⟩`，投影解释为沿 `π1`/`π2` 复合。

函数项的解释由指数泛性质决定：

```text
⟦λ t⟧   := curry ⟦t⟧
⟦f a⟧   := app ⟦f⟧ ⟦a⟧
app f a := eval ∘ ⟨f, a⟩
```

例如 `λx. x` 的闭项解释为 `curry π2 : Hom 1 (⟦A⟧ ^ ⟦A⟧)`。
应用 `f` 和参数 `a` 都使用同一个环境；配对将环境提供给两者，
`eval` 再执行函数。这不要求 C 的对象具有可取出的“元素”。

## 3. 替换是语义证明的主线

同时替换 `σ : Δ ⇒ Γ` 应解释成 `Hom ⟦Δ⟧ ⟦Γ⟧`，
将每个变量的解释配成上下文的嵌套积。空替换解释为 `!`，
替换扩张解释为配对；恒等与复合最终由终对象和积的唯一性保证。
关键定理是：

```text
⟦t[σ]⟧ ≈ ⟦t⟧ ∘ ⟦σ⟧
```

绑定变量下的提升 `σ⁺ : Δ,A ⇒ Γ,A` 解释为 `⟦σ⟧ × id`。
因此 λ 分支所需的等式恰好是 `exponential_curry_comp_r`。
应用分支由已有的新定理 `exponential_app_comp` 给出：

```text
app f a ∘ σ ≈ app (f ∘ σ) (a ∘ σ)
```

先建立变量、重命名、同时替换及其组合，再证明一般替换引理，
可以避免在每条 βη 规则中重新处理变量绑定。
建议使用内在类型化的 de Bruijn 表示；需要特别固定提升、弱化以及替换穿过 λ 的约定。

## 4. βη 可靠性如何归约到泛性质

函数 β 对应本次的 `exponential_app_β`：

```text
app (curry f) a ≈ f ∘ ⟨id, a⟩
```

右侧正是把最新变量替换为 a、其余环境保持不变的解释。
函数 η 的范畴形式由 `exponential_app_η` 给出：

```text
curry (app (f ∘ π1) π2) ≈ f
```

这里 `f ∘ π1` 是将 f 弱化到扩张上下文。积 βη 使用 `product_β1`、
`product_β2`、`product_η`；单位 η 使用 `term_η`。
所有构造的合同性用 `Proper` 证明，等式的对称、传递用指定关系的等价律。

语法 βη 应包含等价闭包、合同性、单位/积/函数 βη，并对同时替换稳定。
可显式把替换稳定性列作生成规则，也可从基础规则证明；#9 应固定一种呈现。
这些语法定理及上述解释尚未实现，不能把范畴 βη 本身称为完整的 STLC 可靠性证明。

## 5. 通用伴随与后续的自由 CCC

[Adjunction](../theories/Cat/Adjunction.v) 以一个 `Class` 保存两侧 Hom
函子之间的自然同构：

```text
A : F ⊣ G
adjunction_hom A : LeftHomF F ≅N RightHomF G
```

这两个函子在 [Hom](../theories/Instance/Set/Hom.v) 中由已有 `HomF`、
函子乘积与复合构造，函子律直接复用。它们的值分别是提升后的
`HomSet (F X) Y` 与 `HomSet X (G Y)`。
原始字段只保存自然同构，不额外保存转置、单位、余单位或三角恒等式。

`adjunct A f`（记号 `f^♯[A]`）从正向分量提取，
`unadjunct A g`（记号 `g^♭[A]`）从分量逆提取。
它们尊重 hom 指定的相等，满足互逆的 `adjunction_β` / `adjunction_η`。
正向自然性从原始自然变换得到，逆向自然性复用 `NatIso_inv`；
不要求分别证明两组自然性。

单位、余单位是转置的恒等态射：`η X := id^♯[A]`、`ε Y := id^♭[A]`。
它们的自然性、两条三角恒等式和唯一分解性质全部导出：

```text
η : IdF => G ∘F F
ε : F ∘F G => IdF
ε(F X) ∘ fmap F (η X) ≈ id
fmap G (ε Y) ∘ η(G Y) ≈ id
```

`adjunct_unit` / `unadjunct_counit` 进一步导出熟悉的公式
`f^♯[A] ≈ fmap G f ∘ η X`、`g^♭[A] ≈ ε Y ∘ fmap F g`。
这些结论对任意两个范畴成立，不将源范畴特化为集合范畴或 CCC。

`AdjunctionFromHom` 是构造这个自然同构的便利接口：接受两个互逆的
尊重映射，以及正向映射在源对象和目标对象上的自然性。
任意逐点同构并不自动自然；这部分证据必须提供一次。
如果已有自然同构，则直接填入 `adjunction_hom`，不用通过这个便利接口重证。
`adjunct_from_hom` / `unadjunct_from_hom` 说明所得转置与原映射逐点相等。
`IdAdjunction` 和 `CompAdjunction` 分别给出恒等伴随与伴随复合；
复合复用 hom 对应的构造，不重复证明单位／余单位的长复合等式。

[Set.Adjunction](../theories/Instance/Set/Adjunction.v) 允许将已有伴随的
同构重新放入合适的共同广集宇宙：

```text
adjunction_hom_nat_iso:
  LeftHomF F ≅N RightHomF G

LeftHomF F (X,Y)  = ↑S HomSet (F X) Y
RightHomF G (X,Y) = ↑S HomSet X (G Y)
```

两边是 `C^op ×C D` 上的函子。共同目标 `SetCat` 的载体宇宙分别容纳
C、D 的 hom 载体，相等见证宇宙分别容纳两边的相等见证；
不要求两个源 hom 具有相同大小，也不要求载体与相等见证大小相同。
提升由 `LiftT` 包装和投影计算，不使用 resizing。

固定 X 后，`ProductRF X`（记号 `(-× X)`）与 `ExponentialF X`
（记号 `(-^ X)`）的态射作用分别为 `σ × id` 和 `exponential_map`。
`ProductF` 还给出两个参数同时变化的积双函子。
`ProductExponentialAdjunction X` 将 `curry` / `uncurry` 实例化为通用伴随：

```text
(-) × X ⊣ (-)^X
```

`exponential_adjunct` / `exponential_unadjunct` 将通用转置与原有
`curry` / `uncurry` 对齐。这里仅需要积与指数对象，无需终对象；
具体广集模型及其选定 CCC 仍须显式启用。

自由 CCC 则需要 #9 的语法范畴。可以取类型为对象，
从 A 到 B 的态射为单变量上下文 `x:A ⊢ t:B`，以 βη 为指定相等，
以替换为复合。也可以取上下文和同时替换；应选一种并显式比较它们。
不必构造原生商类型：把项作为载体、βη 推导作为 Type 值关系即可。

对每个模型的递归解释可直接采用其选定结构。
但整个自由泛性质仍需规定保持结构的函子、基类型上的比较、以及相容的自然同构。
一般比较应是适当意义下的本质唯一性，不要求函子数据或证明字段原生相等。
这也不能只由“每个项都能解释”推出。

## 6. 完备性与验证边界

最终要证明的等价是：

```text
Γ ⊢ t ≡βη u : A
  ↔ 对所有合适大小的 CCC C 及签名解释 I，⟦t⟧C,I ≈ ⟦u⟧C,I
```

正向是可靠性。反向将 C 取为语法 CCC，并证明其规范解释与原项的 βη 类一致。
关键是语法模型的态射相等恰好是选定的 βη，不能意外加入更强的相等。
这个反向论证不以强正规化或可判定相等为前提；自由映射性质需另行证明。
只在 `SetCat` 模型中相等不能直接使用此论证，因为量化中必须包含语法模型。

形式陈述时采用宇宙多态的一族定理，明确模型大小界并容纳语法 CCC；
不假设能在一个小宇宙内收集所有 CCC，也不通过 resizing 合并大小。
态射载体、相等见证以及定律辅助宇宙保持独立。

常驻回归见 [Universes](../tests/Universes.v)：指数转置、伴随与自然 hom 同构
在两种载体／相等见证宇宙排列下均可实例化；通用伴随还连接 hom 大小排列
相反的两个范畴，并允许共同目标广集的两个宇宙按任一方向严格分离。
这项检查也覆盖广集映射提升时输入映射的 `Proper` 辅助宇宙独立于目标载体宇宙。

本地验证使用 `rocq-env` 的 Rocq 9.0.1、OCaml 5.3.0，以及项目 Nix shell
提供的 Dune 3.23.1。`dune build @all @runtest @install` 通过。
78 项临时 `Print Assumptions`（原有指数／积 21 项、伴随及提升 27 项、
Hom 定义与极限增量 30 项）
均报告无额外假设。

临时广集实例以布尔对为载体、只比较第一分量，且每个相等保留额外布尔见证。
检查了不同但等价的映射代表、转置及其逆的直接计算、提升后自然同构的
正逆映射计算、伴随复合的转置计算、βη 与三角恒等式，
以及具体 CCC 与伴随需显式启用。转置记号也检查了连续书写。
极限增量另检查了单对象图式中的中介计算、右伴随保持极限所得中介的计算，
以及从锥范畴终对象唯一性提取的极限比较同构的正逆映射计算。
这些临时实例与公理输出保留在仓库外，未加入常驻测试。
本地结果不代表多版本 CI；提交与 CI 状态另在 #20 同步。
