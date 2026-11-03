# CCC 与简单类型 λ 演算的指称语义

本笔记对应 [#20](https://github.com/Godalin/rocq-cats/issues/20)，
语法、语法范畴和自由 CCC 的实现归 [#9](https://github.com/Godalin/rocq-cats/issues/9)。
目标是逐步证明 STLC 的 βη 等式在所有 CCC 模型中可靠且完备。
当前已补齐指数对象的基本计算律、通用伴随理论及指数双函子；
也已实现一套内在类型化的 STLC 原始语法、重命名／同时替换代数、替换稳定的
Type 值 βη 相等，以及具备终对象、二元积和指数对象的上下文语法 CCC。
上下文也已通过可计算的打包／拆包同构表示为单变量积类型上下文。
任意 CCC 中的语义解释、可靠性、完备性及自由泛性质仍是后续工作。

## 1. 已有基础与本次增量

[CCC](../theories/Cat/CCC.v) 已组合选定的终对象、二元积和指数对象。
这些结构都从 Type 值泛性质提取中介态射。
态射相等是 `HomSet` 指定的 `HomEq`，无需比较函数或证明字段的 Rocq 相等。

[Product](../theories/Cat/Product/Core.v) 已有 `product_β1`、`product_β2`、
`product_η` 以及配对的复合律 `product_comp_r`、`product_comp_l`。
[Terminal](../theories/Cat/Terminal.v) 已有终对象箭头唯一性 `term_η`
和替换相容性 `term_comp_l`。本次补充 `cross_proper`、`cross_id`、`cross_comp`，
使 `f × g` 的相等、单位与复合行为可直接使用。

[Exponential](../theories/Cat/Exponential/Core.v) 本次提供：

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
X 在这个伴随问题中固定；让 X 也变化的指数双函子见下一节。

### 指数的同构运输与双函子

[Exponential.Transport](../theories/Cat/Exponential/Transport.v) 先提供两个一般
泛性质运输定理：`exponential_eval_equiv` 沿指定相等更换求值箭头，
`exponential_transport` 则对参数反变、对结果协变地沿同构运输。给定
`i : X' ≅ X`、`j : Y ≅ Y'` 和原求值 `ev : Hom (E × X) Y`，新求值为
`j.1 ∘ ev ∘ (id × i.1)`，表示对象仍为 E。中介从原泛性质提取；输入变换写成
显式配对，避免通用积映射的封装阻挡具体模型的直接计算。
同构取逆 `iso_symm` 也保持透明，使端点变换的正反向箭头可直接计算。


[Exponential.Functor](../theories/Cat/Exponential/Functor.v) 从同一个指数泛性质
导出参数反变、结果协变的作用。给定 `u : Hom X' X`、`v : Hom Y Y'`：

```text
v ^ u : Hom (Y ^ X) (Y' ^ X')
v ^ u := ƛ (v ∘ eval ∘ (id × u))

exponential_dimap_eval:
  eval ∘ ((v ^ u) × id) ≈ v ∘ eval ∘ (id × u)

exponential_dimap_comp:
  (v' ∘ v) ^ (u ∘ u') ≈ (v' ^ u') ∘ (v ^ u)
```

对象与态射上的 `^` 分别位于 `ob_scope` 和 `hom_scope`，都右结合。
在广集模型中，`v ^ u` 将保相等映射 g 送到 `v ∘ g ∘ u`；在一般范畴中，
上面的求值方程刻画同一构造。respectfulness、单位律和复合律均由已有
柯里化、积的函子性及指数 βη 导出，不新增结构字段或假设。

`exponential_curry_dimap`、`exponential_uncurry_dimap` 和
`exponential_app_dimap` 分别给出柯里化、反柯里化及应用的相容性：

```text
ƛ (v ∘ f ∘ (id × u)) ≈ (v ^ u) ∘ ƛ f
uncurry ((v ^ u) ∘ g) ≈ v ∘ uncurry g ∘ (id × u)
app ((v ^ u) ∘ g) a ≈ v ∘ app g (u ∘ a)
```

只需选定积与指数，不要求终对象或完整 CCC。已有的上下文预合成律处理上下文
参数的变化，本节处理函数参数类型与结果类型的变化。

```text
ExponentialBiF          : Functor (C^op ×C C) C
ExponentialBiF (X, Y)   = Y ^ X
(-^-)                  表示 ExponentialBiF
ExponentialContraF Y   : Functor (C^op) C
(Y ^-)                 表示 ExponentialContraF Y
```

反变截面直接使用通用的 `π1F`。固定参数对象得到的 `π2F (-^-) X`
与原有的 `(-^ X)` 通过 `exponential_fixed_nat_iso X` 比较，分量均为恒等态射；
这不要求函子记录或定律字段原生相等。原有 `ExponentialF` 与积－指数伴随接口保留。

## 2. 从类型、上下文和项得到态射

#9 的第一阶段已选择任意基类型标签 B，暂不加入项常量。
[STLC.Syntax](../theories/STLC/Syntax.v) 实现：

```text
A ::= base b | 1 | A × A | A → A
```

这是 #9 和 #20 共用的一套原始语法。`Ty B` 包含上述类型，`Ctx B` 为后接列表，
`Var Γ A` 为带类型 de Bruijn 变量，`Tm Γ A` 为内在类型化项。
空上下文记为 `∅`，扩张记为 `Γ ▻ A`；最新变量为 `𝟘`，旧变量嵌入为 `↑v x`。
项记号为 `# x`、`⋆`、`⟨t,u⟩`、`π₁ t`、`π₂ t`、`ƛ t`、`f · a`，
分别位于专用的类型、上下文、变量和项作用域。

`NewVar A U` 是只在声明类型处生成的最新变量标记。`Var` 沿上下文递归为
“旧变量或新标记”的和；提升直接消去这个和，不需要依赖相等证明的消去技巧。
变量位置是小型数据，基类型标签 B 可以位于任意宇宙；项的大小由签名决定。

这里原始构造器语法以 Rocq `eq` 作为其具体结构相等，与自然数等具体数据的选择
一致；它不承担 STLC 的 βη 相等。[STLC.Equivalence](../theories/STLC/Equivalence.v)
另定义 Type 值 βη 关系，供语法范畴比较态射。原始替换与 βη 替换相等均逐点
比较，不要求函数相等。

以后加入类型为 A 的闭常量 c 时，
签名解释额外选择 `I(c) : Hom 1 ⟦A⟧`；在上下文中以 `I(c) ∘ !` 解释。

给定任意 `C : Cat`、显式的 `CCC C` 及基类型解释 `I : B → Ob C`，
后续语义解释按下表定义；本轮还没有实现这些解释函数：

| 语法 | 解释 |
| --- | --- |
| 基类型 b | I(b) |
| 单位类型 1 | 选定终对象 1 |
| 积类型 A × B | ⟦A⟧ × ⟦B⟧ |
| 函数类型 A → B | ⟦B⟧ ^ ⟦A⟧ |
| 空上下文 ∅ | 1 |
| 上下文 Γ ▻ A | ⟦Γ⟧ × ⟦A⟧ |
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

[STLC.Renaming](../theories/STLC/Renaming.v) 和
[STLC.Substitution](../theories/STLC/Substitution.v) 已建立：

```text
Ren Δ Γ = ∀ A, Var Γ A → Var Δ A
Sub Δ Γ = ∀ A, Var Γ A → Tm Δ A

t⟨ρ⟩          重命名
t[σ]           同时替换
t[u/]          只将最新变量替换为 u
ρ^↑Ren         将重命名提升到绑定变量之下
σ^↑Sub         将替换提升到绑定变量之下
σ ▻Sub u       为最新变量追加项赋值
```

这里 `Sub Δ Γ` 与上下文态射 Δ → Γ 同向，但变量赋值从 Γ 指向 Δ。
复合方向与范畴记号一致：`σ ∘Sub τ` 对每个 `σ A x` 继续作用 τ。
已有的 `RenEq`／`SubEq` 比较原始赋值的逐点结构相等。

已证明重命名与替换的单位、复合、respectfulness、绑定提升相容性，
以及重命名／替换的混合律、弱化相容性和替换扩张 β/η：

```text
t⟨idRen⟩ = t                 t[idSub] = t
t⟨ρ⟩⟨τ⟩ = t⟨ρ ∘Ren τ⟩       t[σ][τ] = t[σ ∘Sub τ]
t[RenSub ρ] = t⟨ρ⟩
(σ ▻Sub u) A var_zero = u
```

提升替换时，旧赋值先弱化到扩张上下文，最新变量保持为变量项。
在单层或多层抽象之下代入开放项时，不会将项中的自由变量捕获为新绑定的变量。
空上下文赋值及其逐点唯一性也已给出。这些都是可复用的语法定律，保留在理论模块。

同时替换 `σ : Sub Δ Γ` 后续应解释成 `Hom ⟦Δ⟧ ⟦Γ⟧`，
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

变量、重命名、同时替换及其组合，以及 βη 相等的替换稳定性均已完成。
语义部分下一步定义解释并证明一般语义替换引理，避免在每条 βη 规则中
重新处理变量绑定。

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

### 已实现的语法等式接口

[STLC.Equivalence](../theories/STLC/Equivalence.v) 的 `TmEq`，记为 `t ≈βη u`，
由反身、对称、传递、各项构造器同余，以及单位 η、积 β₁/β₂/η、函数 β/η
生成。它是有限推导的 Type 值关系，没有商类型，也不比较推导见证。

替换稳定性不是额外生成规则：`tm_eq_rename` 与 `tm_eq_subst` 从生成规则归纳
证明。函数 β 分支复用原始单变量代入交换律 `rename_single`／`subst_single`；
函数 η 分支复用弱化相容性。这样以后对 βη 推导的归纳只需处理基本等式规则。

`SubTmEq`（`σ ≈SubTm τ`）逐点比较 βη 相等的赋值；原始 `SubEq` 仍表示逐点
结构相等。`subst_tm_ext` 证明逐点更换为 βη 相等的赋值保持替换结果；
`subst_tm_proper` 将它与项本身的替换稳定性合并。绑定提升、替换复合、扩张和
单变量代入均保持这套相等，各项构造器也具有对应的 `Proper` 实例。

[STLC.Set](../theories/STLC/Set.v) 将项和同时替换分别封装为 `TmS Γ A`、
`SubS Δ Γ`。`tm_rename_resp`、`tm_subst_resp` 和 `tm_subst_assignment_resp`
分别打包重命名、固定替换的项作用，以及固定项的赋值作用。载体仍是原始项／
替换；映射按原有递归定义计算，不执行 βη 正规化。

签名和项载体位于 b，相等推导可位于任意 e ≥ b；特别允许 b < e。
这里 b ≤ e 是这项具体构造的大小要求：Type 值传递规则保留一个中间项。
广集基础没有因此增加全局大小约束。相等见证与定律证明使用的辅助宇宙也不必
等于项载体宇宙。`TmS`、`SubS` 及上述保相等映射均保留这个选择。

这些语法定理已实现，但解释及可靠性定理尚未实现；不能把已有范畴 βη 定律
本身称为完整的 STLC 可靠性证明。

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
η : IdF ⇒ G ∘F F
ε : F ∘F G ⇒ IdF
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

### 已实现的上下文语法范畴

[STLC.Category](../theories/STLC/Category.v) 选择上下文及同时替换作为语法范畴
`CtxCat B` 的对象与态射：

```text
Ob                  = Ctx B
HomSet Δ Γ          = SubS Δ Γ
id                  = idSub
σ ∘ τ               = σ ∘Sub τ
σ ≈ τ               = σ ≈SubTm τ
```

因此 Hom 相等恰好是已定义的逐点 βη 相等，未加入更强的关系。复合的
respectfulness 来自 `sub_comp_tm_proper`，单位与结合律来自原始替换定律，
再逐点嵌入 βη 相等。`CtxCat_HasTerminal` 选择空上下文，唯一态射为 `sub_empty`。

[STLC.Context](../theories/STLC/Context.v) 定义上下文连接 `Γ ++Ctx Δ`、两侧变量
嵌入 `ren_append_l`／`ren_append_r`，以及赋值配对 `⟨σ,τ⟩Sub`。配对沿第二个
上下文递归扩张；沿两侧嵌入限制后分别恢复 σ、τ，任意赋值也由这两个限制恢复。
这些分解律使用原始逐点结构相等，不比较函数。配对同时保持原始相等和 βη 相等。

[STLC.Product](../theories/STLC/Product.v) 用这些操作证明完整的积泛性质
`ctx_append_product`，再打包为 `CtxCat_HasProduct`：

```text
Γ × Δ              = Γ ++Ctx Δ
π1                 = RenSub (ren_append_l Γ Δ)
π2                 = RenSub (ren_append_r Γ Δ)
⟨σ,τ⟩              = ⟨σ,τ⟩Sub
Γ × (∅ ▻ A)        = Γ ▻ A
```

最后一行是具体上下文数据的直接计算；泛性质中的唯一性仍使用 βη 相等。
中介从透明泛性质提取，保持赋值查找的直接计算。两个选定结构均须显式启用，
不会因导入而全局注册。有限积由已有的
[Cat.Product.Finite](../theories/Cat/Product/Finite.v) 通用构造直接获得，
无需在语法模型中重复证明。

范畴可在 `b < e < l` 下实例化：b 为上下文／替换载体层级，e 为 βη 见证层级，
l 为范畴定律辅助层级。构造支持 `b ≤ e ≤ l`，不把这三个层级强制合并。

### 上下文的积类型表示

[STLC.Packing](../theories/STLC/Packing.v) 将上下文编码为积类型 `CtxTy Γ`，
记为 `⟦Γ⟧Ty`：

```text
⟦∅⟧Ty       = ⊤
⟦Γ ▻ A⟧Ty   = ⟦Γ⟧Ty × A
```

先在任意源上下文 Δ 上构造一组可复用转换：

```text
⌜σ⌝          : Tm Δ ⟦Γ⟧Ty       （σ : Sub Δ Γ）
⌞t⌟[Γ]       : Sub Δ Γ           （t : Tm Δ ⟦Γ⟧Ty）

ctx_pack_β:  ⌞⌜σ⌝⌟[Γ] ≈SubTm σ
ctx_pack_η:  ⌜⌞t⌟[Γ]⌝ ≈βη t
```

`ctx_pack` 将赋值递归配成嵌套积，`ctx_unpack` 沿积投影逐次恢复赋值。
β 使用积 β 方程及已有替换扩张 η；η 使用单位 η 和积 η。它们保持指定的
βη 相等，并打包为 `ctx_pack_resp`／`ctx_unpack_resp` 两个保相等映射。
项仍然是原始语法，投影和配对按构造器计算，η 方程由 βη 推导给出。

替换相容性先在原始语法层证明：

```text
ctx_pack_subst:    ⌜σ⌝[τ] = ⌜σ ∘Sub τ⌝
ctx_unpack_subst:  (⌞t⌟[Γ]) ∘Sub σ ≈Sub ⌞t[σ]⌟[Γ]
```

第二条逐点比较赋值，没有要求函数相等。于是打包恒等赋值、拆包单个变量即可
得到两条替换 `ctx_pack_sub Γ`／`ctx_unpack_sub Γ`；它们的互逆律复用上述
通用转换及替换相容性，不为这个特例另证一套投影计算。

`ctx_pack_iso Γ` 最终给出已有范畴同构接口中的

```text
Γ ≅[CtxCat B] (∅ ▻ ⟦Γ⟧Ty).
```

同构的正反向替换保持透明，取出后可直接计算变量赋值；其宇宙也允许
`b < e < l`。这为后续通过函数类型构造任意上下文之间的指数对象提供桥梁。

### 语法指数对象与 CCC

[STLC.Exponential](../theories/STLC/Exponential.v) 先证明单变量上下文的指数
泛性质：参数为 `∅ ▻ A`，结果为 `∅ ▻ U`，表示对象为 `∅ ▻ (A ⇒ U)`。
`singleton_eval` 应用函数变量于参数变量，`singleton_curry`（`ƛSub f`）抽象
f 的最新输入。函数 β 及原始替换律 `rename_lift_single` 给出求值方程，
函数 η 给出转置唯一性，形成完整的 `singleton_exponential`。

对任意上下文，`CtxExp Δ Γ`（`Δ ^Ctx Γ`）定义为

```text
Δ ^Ctx Γ = ∅ ▻ (⟦Γ⟧Ty ⇒ ⟦Δ⟧Ty).
```

`ctx_eval Γ Δ` 打包参数块、执行单变量求值、再拆包结果。其数据使用透明的
替换复合与赋值配对。`ctx_exponential` 利用上下文打包同构及上述一般运输定理
得到完整泛性质，没有为任意上下文重复证明函数 βη 或唯一性。

`CtxCat_HasExponential` 将这些数据组装为相对于既有连接积的选定指数结构。
[STLC.CCC](../theories/STLC/CCC.v) 再以 `CtxCat_CCC` 组合选定终对象、积和指数。
它们都须显式启用；导入不会全局选择模型结构。求值和从泛性质提取的转置均可
直接计算，包含空上下文与多变量上下文；整体结构仍允许 `b < e < l`。

至此语法 CCC 已构造；任意 CCC 中的解释、语义替换与可靠性也已实现如下。
[STLC.TypeCategory](../theories/STLC/TypeCategory.v) 另构造类型呈现 `TyCat B`：
对象是简单类型，Hom 是单变量上下文间的替换，指定相等仍为逐点 βη。
范畴数据复用一般的 [InducedCat](../theories/Cat/Induced.v)；选定终对象、积与
指数分别是语法单位、积与函数类型。`singleton_product` 对任意源上下文证明
积类型的泛性质；函数类型沿 `type_pair_iso` 的积比较继承已有的
`singleton_exponential`，没有重复证明函数 η。

[STLC.Quotation](../theories/STLC/Quotation.v) 的 `syntax_eval` 按字面类型的
CCC 运算求值。`syntax_eval_quote` 证明结果恰好是原项替换环境中的各个项；
绑定情形显式处理积编码与弱化。`syntax_eval_retract` 因而在恒等环境中恢复每条
单变量箭头。这是规范模型还原的核心，不把递归类型解释与恒等函数判为原生相等。
类型呈现的完整 CCC 也在 `b < e < l` 下保留一项永久接口回归。
两种呈现之间的显式范畴等价及模型比较会另外组装。

对每个模型的递归解释可直接采用其选定结构。
但整个自由泛性质仍需规定保持结构的函子、基类型上的比较、以及相容的自然同构。
一般比较应是适当意义下的本质唯一性，不要求函子数据或证明字段原生相等。
这也不能只由“每个项都能解释”推出。

### 任意 CCC 中的解释与可靠性

[STLC.Semantics](../theories/STLC/Semantics.v) 为任意选定 CCC 及基类型解释
`I : B → Ob C` 定义 `TyI`、`CtxI` 与 `tm_interp`。类型按终对象、积和指数递归
解释，上下文从终对象开始迭代取积。共享记号为 `⟦A⟧Ty[I]`、`⟦Γ⟧Ctx[I]`、
`⟦t⟧Tm[I]`，位于 `stlc_sem_scope`。

证明先对任意源对象 X 上的环境 `Env I X Γ` 进行。`tm_eval_comp`、
`tm_eval_rename` 与 `tm_eval_subst` 分别处理预合成、重命名和同时替换，
绑定情形使用积投影与指数转置的自然性。`tm_eval_sound` 按 βη 推导归纳，
其函数 β/η 分别复用一般的 `exponential_app_β`／`exponential_app_η`。

[STLC.Interpretation](../theories/STLC/Interpretation.v) 用 `env_tuple` 表示环境，
以 β/η 给出投影与元组的互逆行为。于是 `sub_interp` 把同时替换解释为上下文
之间的态射，`tm_interp_subst` 证明语法替换恰好表示预合成，`InterpretF` 将其
组装为 `CtxCat B → C` 的函子。源 βη 见证可以严格高于语法载体，目标 Hom
载体与相等见证的大小也无固定顺序；永久回归只保留这两种排列的函子接口。

`tm_interp_sound` 证明每个 βη 推导在所有这些模型中成立。不使用函数原生
相等，不附加选择、证明无关性或外延公理。规范解释还原、完备性及保持结构的
自由泛性质仍需另证，不能由可靠性或解释函子的存在直接推出。

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
指数双函子、反变截面与固定参数的自然同构也在两种 Hom／相等见证宇宙排列下
检查，永久回归仅补充这六项接口检查。

本地验证使用 `rocq-env` 的 Rocq 9.0.1、OCaml 5.3.0，以及项目 Nix shell
提供的 Dune 3.23.1。`dune build @all @runtest @install` 通过。
78 项临时 `Print Assumptions`（原有指数／积 21 项、伴随及提升 27 项、
Hom 定义与极限增量 30 项）
均报告无额外假设。
本次双函子的 13 个构造与证明另经临时 `Print Assumptions` 检查，
也均无额外假设，输出未加入编译源码。
STLC 原始语法另检查了 18 项关键定律与构造，包括绑定提升、混合替换、复合及
扩张 η，均无额外假设。原始语法永久回归包含两项任意签名宇宙下的重命名／替换接口，
防止变量标记的多余宇宙参数限制任意项的实例化。
βη 增量另检查了 29 项定义与证明，覆盖生成关系、两类等价关系、重命名／替换
稳定性、`Proper` 实例、广集封装及三条原始代入交换律，均无额外假设。
新增的五项永久宇宙接口检查要求 b < e，覆盖项／替换广集及三种保相等映射，
防止宇宙推断意外压缩相等见证层级。
上下文范畴增量另对 13 项构造与证明作临时 `Print Assumptions` 检查，均无额外
假设。再增加三项永久接口回归，要求 `b < e < l`，覆盖范畴及选定终对象／积，
防止直接填入 `Proper` 证明时把相等见证层级与定律层级意外合并。
上下文打包增量另有 14 项临时公理检查，覆盖两类转换、βη、替换相容性、
保相等映射及上下文同构，均无额外假设。永久测试只追加一项打包同构的
`b < e < l` 接口检查。
语法 CCC 增量另对 14 项定义与证明作临时公理检查，包括一般同构／求值相等
运输、积因子交换、原始替换辅助律、透明同构取逆及语法指数构造，均无额外
假设。永久测试只追加一项完整语法 CCC 的 `b < e < l` 接口回归。

临时广集实例以布尔对为载体、只比较第一分量，且每个相等保留额外布尔见证。
检查了不同但等价的映射代表、转置及其逆的直接计算、提升后自然同构的
正逆映射计算、伴随复合的转置计算、βη 与三角恒等式，
以及具体 CCC 与伴随需显式启用。转置记号也检查了连续书写。
极限增量另检查了单对象图式中的中介计算、右伴随保持极限所得中介的计算，
以及从锥范畴终对象唯一性提取的极限比较同构的正逆映射计算。
双函子增量继续使用具有额外布尔相等见证的广集，验证参数、结果变换及不同但
等价的映射代表，双函子与反变截面的态射计算、柯里化／反柯里化／应用的计算、
固定参数比较同构的正逆映射，以及指数记号的作用域、复合和右结合。
语法增量临时检查了开放项在单层与双层绑定下的捕获避免、同时交换、连续替换、
弱化、最新／旧变量的赋值计算、越界变量的拒绝，以及与范畴／DTT 模块共同导入
时的记号兼容性。
βη 增量临时检查了所有基本 βη 方程、β/η 在重命名及替换后的稳定性、
βη 相等但结构不等的项及替换、绑定下逐点更换赋值、项与赋值同时改变的
respectfulness、保相等映射的变量查找计算，以及同层宇宙实例。
另以推导见证上的布尔观察区分反身推导与其对称推导，检查 Type 值数据可消去；
这不为见证额外定义相等，也不声称所有等式证明都可完整归约。
上下文范畴增量临时检查了指定 Hom 相等恰为逐点 βη 相等、恒等／复合与两侧
投影／配对的变量查找计算、空因子及嵌套连接、配对的 βη respectfulness 和
唯一性，以及扩张为单变量积的计算。还检查了选定结构须显式启用、通用有限积
接口的复用及同层宇宙实例。
上下文打包增量临时检查了空上下文和双变量上下文的积类型、嵌套配对与逐次
投影的直接计算，βη 相等赋值的保相等转换，两个往返及替换相容性。同构中
取出的正反向替换也检查了直接计算；同层宇宙及两种保相等映射的高见证宇宙
接口另经临时实例化检查。还验证了单变量例子中 η 两端结构不同，以确认
往返确实使用了指定的 βη 相等。
语法 CCC 增量临时检查了指数对象、求值及转置的直接计算，单变量、空参数、
空结果和多变量上下文，求值／转置的 βη 互逆律及转置 respectfulness，
以及模型结构须显式启用。一般指数运输在 Hom 载体与相等见证大小的两种
严格排列下均已实例化；同层语法 CCC 也已检查。
具体广集运输另使用布尔对、仅比较第一分量且保留额外布尔相等见证，验证了
互逆箭头的不同原始代表、同构取逆箭头的直接计算，以及运输后中介的直接
计算。这里的 βη 检查是语法模型及一般指数定律的实例，不是尚未实现的
任意 CCC 语义可靠性定理。
这些临时实例与公理输出保留在仓库外，未加入常驻测试。
本地结果不代表多版本 CI；提交进度与剩余数学工作另在 #20 同步。
