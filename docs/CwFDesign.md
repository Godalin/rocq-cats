# CwF 接口设计与抽象核心

设计已接受，[抽象核心](../theories/DTT/CwF.v) 已实现，并使用 #19 提取的广集基础。
当前已实现抽象核心和 [Code/El 模型](../theories/Instance/Set/CwF.v)，
不含类型构造子；Σ、Π 等构造留待后续。

## 1. 基础约定与目标接口

**本库的集合默认就是广集，严格相等就是该集合指定的相等关系。**
因此接口直接命名为 **CwF**，不增加 Setoid 前缀，也不因底层使用广集而
另设一套“更严格”的接口。

上下文组成已有的 `Cat`，类型和同一类型的项分别组成集合。
相等关系由各集合指定：例如 [NatS](../theories/Instance/Set/Nat.v) 选择 Rocq 的
原生命题相等 `eq`，而 [FunS](../theories/Set/Morphism.v) 选择逐点相等。
`eq` 是可选的具体关系之一，不因它是内建关系就赋予它另一层“更严格”的地位。

各处严格相等的具体关系是：

| 对象 | 指定的相等 |
| --- | --- |
| 替换 σ、σ' | 上下文范畴的 `HomEq`，记作 `σ ≈ σ'` |
| 类型 A、B | 类型集合的相等，本文记作 `A ≈Ty B` |
| 同一类型的项 t、u | 项集合的相等，本文记作 `t ≈Tm u` |

实现中类型和项已经各自组成 `SetC`，统一复用 `≈S`，不另定义两套相等记号。
上下文的态射也直接组成 `HomSet Δ Γ : SetC`。因此替换、类型和项的相等
都来自同一个 [Set.Core](../theories/Set/Core.v)；`≈` 与 `≈S` 只是不同接口的记号，
不是两个强弱不同的相等层级。

CwF 的单位、复合、β/η 等定律都在这些关系中成立。
若某个模型选择 `eq`，相应定律就使用 `eq`；接口统一依赖指定关系及其相干性。
跨相等类型的项通过指定传输对齐后比较。
类型同构仍保留其正逆映射，是另外的结构。

## 2. 指定的类型相等与相干传输

关系 `A ≈Ty B` 是模型**指定的类型相等**，必须带相干的项转换。
任意的纤维同构仍是同构，不自动成为类型相等。

原因可以直接用布尔类型看出：恒等和取反都是 Bool 的自同构。
如果把两者都作为 `Bool ≈Ty Bool` 的见证，并让项转换按该同构作用，
那么“相等见证独立”会要求 `true ≈ false`。离散布尔广集不满足这个要求。

因此不能直接设置：

```text
Ty Γ := 所有 FamS Γ
A ≈Ty B := A 与 B 的任意纤维同构
Tm Γ A := SectionS A
```

并同时保留现有 `FamS` 的转换相干性。这里的冲突是转换的作用，
并非要求底层见证只有一个，也不是要引入 UIP。

现有 [FamSCat](../theories/Instance/Set/Fam/Fixed.v) 保留任意类型态射和同构。
给类型指定相等时，还须保证它在项上的作用满足相干传输律。
这不改变用自然同构比较函子的规范，也不限制保留类型自同构作为额外的语义结构。

## 3. 用族值函子组织类型、项和替换

核心数据采用：

```text
T : Functor (C^op) FamCat
```

这里的 [FamCat](../theories/Instance/Set/Fam/Cat.v) 已有广集索引、相干的纤维族、
尊重等价的态射，以及带传输的态射等价，正好可以复用。

| 派生概念 | 从 T 得到的内容 |
| --- | --- |
| `Ty Γ : SetC` | `famC_base (T Γ)` |
| `Tm Γ : FamS (Ty Γ)` | `famC_fam (T Γ)` |
| `Tm Γ A : SetC` | 上一行在类型 A 处的纤维 |
| `A[σ]Ty[T]` | `fmap T σ` 的基底映射作用于 A |
| `t[σ]Tm[T]` | 同一个族态射在 A 处的纤维映射作用于 t |
| `e[σ]Eq[T]` | 类型替换映射的尊重性作用于类型相等 e |
| `e ▸[T] t`，其中 `e : A ≈Ty B` | `Tm Γ` 沿 e 的传输 |

其中 `σ : Hom Δ Γ` 在 `C^op` 中作为 Γ 到 Δ 的态射使用。
`Ty`、`Tm`、替换、转换都是从 T 派生的操作，不再重复存储一套字段和定律。

抽象接口复用现有的集合、相干族及族态射 API。
基础集合与尊重映射由 `Cat.Core` 导出的 `Set.Morphism` 提供，不再直接导入
`Instance.Set.Core`。仍复用 `Instance.Set.Fam.Core` 和 `Instance.Set.Fam.Cat`
组织类型与项；这里的族范畴是元层结构，不要求上下文范畴 C 等于 `SetCat`。
公开记号显式标注 T，因为不能仅凭函子在某个对象处的取值唯一推断函子。
下文数学公式省略这些标签。

## 4. 转换与严格替换律

以下等式的两边都已处在同一项广集中，使用 `≈Tm` 比较。

由 `Tm Γ : FamS (Ty Γ)` 得到：

```text
e : A ≈Ty A                 ⇒ e ▸ t ≈Tm t
e : A ≈Ty B, d : B ≈Ty D    ⇒ (e ;; d) ▸ t ≈Tm d ▸ (e ▸ t)
e,d : A ≈Ty B               ⇒ e ▸ t ≈Tm d ▸ t
```

第一条对每个类型相等的自见证成立；这是选择类型相等时的实质要求。
这些定律只比较传输结果，保留见证本身为 Type 值数据。

从 T 的函子律提取：

```text
ι_A       : A[id]Ty ≈Ty A
κ_A,σ,τ   : A[σ]Ty[τ]Ty ≈Ty A[σ ∘ τ]Ty
ε_A,H     : A[σ]Ty ≈Ty A[σ']Ty       （H : σ ≈ σ'）
```

项替换律必须写为：

```text
ι_A ▸ t[id]Tm                         ≈Tm t
κ_A,σ,τ ▸ t[σ]Tm[τ]Tm                 ≈Tm t[σ ∘ τ]Tm
ε_A,H ▸ t[σ]Tm                        ≈Tm t[σ']Tm
```

替换也保持同类型的项相等，并与类型转换相容：
对 `e : A ≈Ty B`，两种顺序“先转换再替换”与“先替换再沿 e[σ] 转换”等价。
这是族态射的自然性，不另加公理。

T 的函子律使用 [FamFEq](../theories/Instance/Set/Fam/Cat.v)。
其中保留的基底等价正好提供上述 ι、κ、ε。若函子复合律给出相反方向，
使用该等价的对称见证。传输的见证独立性保证不同复合路径给出相同的转换作用，
无需要求这些见证原生相等。
由于这些见证会用于计算转换，新模型中供提取的函子律也应保持透明，
用 `Defined` 完成。

上面的 ι、κ、ε 都是**指定类型相等的见证**，对应严格的类型替换律；
项替换律在转换后使用指定的项相等。写出转换是为了保证两边具有相同的类型，
并没有把严格替换律降为“只存在某个同构”。

A 阶段的重索引比较是语义族之间的指定同构。实例化 CwF 时可以用它们对齐解码族，
但仍须证明类型集合中指定的相等及上面的项替换律。

## 5. 上下文扩张：先给候选泛性质，再选择结构

给定 Γ 和 A，候选数据为：

```text
E : Ob C
p : Hom E Γ
q : Tm E A[p]Ty
```

谓词 `is_context_extension T A E p q`（Γ 隐式）要求：
对每个 Δ、`σ : Hom Δ Γ` 和 `t : Tm Δ A[σ]Ty`，
存在保留计算内容的 `h : Hom Δ E`，满足：

```text
β1 : p ∘ h ≈ σ

(κ_A,p,h ;; ε_A,β1) ▸ q[h]Tm ≈Tm t
```

第二行先将 `q[h]` 从 `(A[p])[h]` 转到 `A[p ∘ h]`，
再沿 β1 转到 `A[σ]`。不能直接写跨类型的 `q[h] ≈Tm t`。

这样的 h 按 `HomEq` 唯一；唯一性量化所有满足条件的 h 和所有 β1 见证。
可使用已有 `is_unique` 表述，保持存在见证为 Type 值。

`HasContextExtension T` 再选择 `Ext T A`（Γ 隐式）、p、q 及上述泛性质。
公开扩张记号是 `Γ ▹[T] A`，配对记号是 `⟨σ; t⟩[T, A]`。
配对从泛性质提取，不另存一个可能不一致的配对字段。
派生 β₁、经转换的 β₂ 和 η：

```text
h ≈ ⟨p ∘ h; κ_A,p,h ▸ q[h]Tm⟩
```

另一个等价的描述是表示广集：

```text
HomSet_C(Δ, Γ ▹ A) ≅S Σ (σ : Hom Δ Γ), Tm Δ A[σ]Ty
```

右侧的两个元素 (σ,t)、(σ',t') 等价，当且仅当保留某个
`H : σ ≈ σ'`，并满足 `ε_A,H ▸ t ≈Tm t'`。
右侧重索引定义为 `(σ,t)[τ] := (σ ∘ τ, κ_A,σ,τ ▸ t[τ])`；
它的函子律及表示的自然性作为派生定理证明，不作为额外的选择字段。

这些构造已在 [ContextExtension](../theories/DTT/Context/Extension.v) 实现：

- `SubstitutionTerms T A Δ` 通过 `σ ↦ A[σ]` 拉回项族；
  `ContextPairS T A Δ` 是这个族的依赖和，复用已有的带传输相等。
- `context_pair_sub_resp T A τ` 提供重索引，记作 `x[τ]Pair[T, A]`。
  它尊重配对数据与 τ 的指定相等，并满足单位、复合律，形成预层 `ContextPairF T A`。
  这部分不要求已选择上下文扩张。
- `context_extension_iso T A Δ` 给出上述广集同构：正向由投影和泛变量提取数据，
  逆向由泛性质提取配对，互逆由 β/η 证明。
- `context_extension_nat_iso T A` 将这些同构组织成
  `Hom(-, Γ ▹[T] A) ≅N ContextPairF T A`。
  正向自然变换 `context_extensionN` 的分量作用是
  `h ↦ (p,q)[h]Pair[T,A]`；自然性就是配对数据的替换复合律。
  逆自然变换 `context_pairN` 则给出配对的自然性：

```text
context_pair_comp:
  ⟨σ;t⟩ ∘ τ ≈ ⟨σ ∘ τ; κ_A,σ,τ ▸ t[τ]⟩
```

表示定理只要求 `HasContextExtension T`，不要求终对象或额外 CwF 公理。

类型相等诱导扩张上下文的指定同构，保持投影及经转换的变量。
[ContextConversion](../theories/DTT/Context/Conversion.v) 已实现这部分派生构造。
对 `e : A ≈S B`，定义透明态射：

```text
e^Ext[T] := ⟨p_A; e[p_A]Eq[T] ▸[T] q_A⟩[T,B]
```

- `context_conv_proj` 给出 `p_B ∘ e^Ext[T] ≈ p_A`。
- `context_conv_var` 将 `q_B[e^Ext[T]]` 沿复合与投影相等转换后，
  与 `e[p_A]Eq[T] ▸[T] q_A` 比较。
- `context_conv_pair` 给出配对相容性：
  `e^Ext[T] ∘ ⟨σ;t⟩[T,A] ≈ ⟨σ; e[σ]Eq[T] ▸[T] t⟩[T,B]`。
- 相同端点的相等见证诱导相等的态射；每个自相等见证诱导恒等态射。
  对 `e : A ≈S B`、`d : B ≈S D` 及任意 `r : A ≈S D`，
  有 `r^Ext[T] ≈ d^Ext[T] ∘ e^Ext[T]`。
- `context_conv_iso T e` 保留正向态射及沿对称见证得到的逆态射。
  两个方向的复合为恒等，由上述单位和复合律推出。

这些律只比较态射的指定相等，不比较相等见证本身，也不要求范畴对象原生相等。
类型仍使用指定的严格相等；扩张对象之间则提供保持投影与变量的同构。
证明仅要求 `HasContextExtension T`，继续复用已有配对泛性质和表示定理的配对复合律。

### 替换提升与显示投影的拉回

[ContextPullback](../theories/DTT/Context/Pullback.v) 定义替换提升：

```text
σ^+[T,A] : Δ ▹[T] A[σ]Ty[T] → Γ ▹[T] A
σ^+[T,A] := ⟨σ ∘ p_A[σ]; κ_A,σ,p_A[σ] ▸ q_A[σ]⟩[T,A]
```

`context_lift_proj` 和 `context_lift_var` 给出投影与泛变量的定律，
`context_lift_pair` 说明提升将配对送到复合替换及经转换的项。
沿前面定义的扩张同构对齐源对象后，有：

```text
σ ≈ σ' ⇒ σ^+[T,A] ≈ σ'^+[T,A] ∘ (ε_A,H)^Ext[T]
id^+[T,A] ≈ (ι_A)^Ext[T]
σ^+[T,A] ∘ τ^+[T,A[σ]] ≈ (σ ∘ τ)^+[T,A] ∘ (κ_A,σ,τ)^Ext[T]
```

`context_lift_pullback T σ A` 证明完整的拉回泛性质：

```text
is_pullback σ p_A (Δ ▹[T] A[σ]Ty[T]) p_A[σ] σ^+[T,A]
```

对 `u : Θ → Δ`、`v : Θ → Γ.A` 及 `H : σ ∘ u ≈ p_A ∘ v`，
中介态射将 `q_A[v]` 沿 H 的反向比较转到 `A[σ ∘ u]`，
再沿 κ 的逆向转换转到 `(A[σ])[u]`，最后与 u 配对。
`context_lift_factor` 从透明的泛性质见证提取该态射，提供两个投影律、
唯一性、对两条锥腿相等的尊重性，以及对 H 的见证独立性。
唯一性复用配对与类型转换的单射性；这些性质均由已有相干性和表示同构导出。

本构造只需要 `HasContextExtension T`，没有增加 `HasPullback C` 假设，
也没有为 C 注册所有拉回的选定结构。这里只构造显示投影沿任意替换的拉回。

### 显示映射形式的类型总范畴与 comprehension

[DTT/Comprehension](../theories/DTT/Comprehension.v) 使用以下明确的态射表示：

```text
ContextType T := Σ Γ, Ty T Γ
ContextMap T (Γ,A) (Δ,B) :=
  σ : Hom Γ Δ
  h : Hom (Γ ▹[T] A) (Δ ▹[T] B)
  p_B ∘ h ≈ σ ∘ p_A
```

态射相等逐项比较 σ 和 h，不比较交换证明。复合为两条映射分别复合，
记作 `g ∘Ctx[T] f`，形成 `ContextTypeCat T`。
这里允许任意满足交换条件的扩张映射，包括不可逆映射。
原来的类型严格相等仍由 `Ty T Γ` 指定，不从这些态射或同构反向定义。

`CwFBaseF T` 取基底 Γ 和 σ，`CwFExtF T` 取扩张 Γ.A 和 h，
`CwFProjectionN T` 由各个 p_A 组成。
对 Y=(Δ,B) 和 σ:Γ→Δ，`Y[σ]Ctx[T]` 表示 `(Γ,B[σ])`，
`context_type_reindex T Y σ` 的两条映射是 σ 和 `σ^+[T,B]`。

`context_map_pullback_cartesian` 从显示方块的拉回泛性质构造笛卡尔分解。
上一节的显示拉回使上述重索引态射成为笛卡尔态射。
反向证明将任意笛卡尔态射与这个选定提升比较，得到总范畴中的同构，
再通过扩张函子及拉回的同构不变性转移泛性质。因此有完整判别：

```text
context_map_cartesian_iff_pullback:
  f ⦂ cartesian(CwFBaseF T)
  ↔ is_pullback σ p_B (Γ ▹[T] A) p_A h
```

`CwFComprehension T` 将选择的提升、扩张函子、投影自然变换和该泛性质
组装为已有的 `Comprehension (CwFBaseF T)`。
`CwFBaseF_HasCartesianLift T` 及结构包中的提升都需显式启用；
基底对象的识别由构造的第一投影直接给出反身识别。
构造仅要求 `HasContextExtension T`，不需要终对象或所有拉回。

这一步固定了从 CwF 得到 comprehension 的一个具体呈现。
[Arrow](../theories/Cat/Arrow.v) 定义任意范畴的箭头范畴 `Arr C`：
对象为态射，态射为交换方块，相等比较方块的两条边。
`ArrowDomF C` 和 `ArrowCodF C` 分别取定义域和陪域。
通用构造 `NatArrowF α` 将自然变换组织为到箭头范畴的函子。
因此，每个已有 comprehension 都有 `ComprehensionF K := NatArrowF (projectionN K)`；
其两条边分别来自扩张函子和基底函子。

`CwFComprehensionF T` 是上述构造在 `CwFComprehension T` 的实例。
`context_map_from_arrow T` 从方块的两条边及交换见证透明地恢复总范畴态射，
`cwf_comprehension_fully_faithful T` 据此证明全忠实性。
这依赖当前总范畴使用所有显示交换方块作为态射的约定；
不是对任意 `Comprehension K` 新增全忠实性假设，也不自动证明其他呈现的全忠实性。
反向构造 CwF，以及与其他态射约定或 split 结构的比较仍需分别证明。

### 陪域函子的笛卡尔态射

[ArrowFibration](../theories/Cat/ArrowFibration.v) 将前述显示方块判别推广到任意箭头：

```text
arrow_cartesian_iff_pullback f:
  f ⦂ cartesian(ArrowCodF C)
  ↔ is_pullback (arrow_bottom f) (arrow_map B)
      (arrow_dom A) (arrow_map A) (arrow_top f)
```

这不要求 C 已有所有拉回。正向证明将任意锥编码为从 `IdentityArrow Q`
出发的方块，再由笛卡尔分解提取唯一的顶边；反向直接使用拉回中介态射。
中介态射和两方向的泛性质见证均保持透明。

给定 `HasPullback C`，`ArrowReindexOb B σ`（记作 `B[σ]Arr`）
以 `Pb σ (arrow_map B)` 为定义域、以 σ 的定义域为陪域。
`arrow_reindex B σ` 的两条边为 `pb2` 和 σ。
`ArrowCodF_HasCartesianLift` 将其组织成选定笛卡尔提升。

反向的 `ArrowCodF_HasPullback` 接受任意选定陪域提升。
若提升对象为 L，其携带的基底对象识别为 `e : arrow_cod L = X`，
恢复的第一投影是 `eq_to_hom e ∘ arrow_map L`，第二投影是提升的顶边。
通用引理 `pullback_base_iso` 沿这个识别诱导的同构转移拉回泛性质，
不比较 e 与其他识别见证，也不要求 e 为反身见证。

`pullbacks_iff_arrow_cartesian_lifts C` 打包这两个构造，表明两种选定结构可互相构造；
它不要求选择的对象或证明字段相等，也不额外要求重索引严格分裂。
两个方向都作为普通定义提供，需显式启用，不由导入模块自动注册实例。

### 项与投影截面

[Section](../theories/Cat/Section.v) 将已有的 `Sec(p)` 广集推广到任意范畴：
元素为 `s : Hom Γ E` 及 `p ∘ s ≈ id`，相等仅比较 s。
原来的集合族截面模块复用并导出这个定义，保留原有 `Sec(p)` 记号。

[ContextSection](../theories/DTT/Context/Section.v) 从上下文扩张泛性质导出：

```text
context_term_section_iso T A:
  Tm T Γ A ≅[SetCat] Sec(context_proj T A)
```

正向映射 `t^Sec[T,A]` 将 t 沿 `ty_sub_id` 的逆向转换到 `A[id]` 后与 id 配对。
逆向映射 `s^Tm[T,A]` 取 `q_A[s]`，依次沿替换复合、截面的右逆见证及
替换单位比较转换回 A。截面的基底代表只需满足指定相等，不能假定原生相等。
两个操作都是尊重指定相等的透明映射，其 β/η 律不比较右逆证明。

它们还满足配对及替换相容性：

```text
term_section_pair:
  (t^Sec[T,A]).1 ∘ σ ≈ ⟨σ; t[σ]Tm[T]⟩[T,A]

term_section_sub:
  σ^+[T,A] ∘ (t[σ]Tm[T]^Sec[T,A[σ]Ty[T]]).1
  ≈ (t^Sec[T,A]).1 ∘ σ
```

这些结果只要求 `HasContextExtension T`，不要求终对象。
任意 comprehension 的反向项接口仍需单独陈述假设；本定理处理已有的 CwF 项族。

## 6. 最外层 Class 的形状

已实现的签名如下：

```coq
Class CwF (C : Cat) :=
  { hasTerminal :: HasTerminal C
  ; TyTmF : Functor (C^op) FamCat
  ; hasContextExtension :: HasContextExtension TyTmF
  }.
```

组合结构字段沿用 [CCC](../theories/Cat/CCC.v) 和
[ETCS](../theories/ETCS/Core.v) 的 `has* :: Has*` 写法。
客户端先显式启用具体 CwF 模型，再由这个结构包推导终对象和上下文扩张结构；
导入模块本身不启用任何具体模型。`TyTmF` 是普通数据字段，显式投影所选的 CwF。
派生定义单独放置，不另设 `CwFData`。

CCC、ETCS 与 CwF 都以命名的范畴参数声明附加结构，
不重复选择已经由参数给定的底层范畴。

核心结构包括：
`is_context_pair`、`is_context_extension`、`HasContextExtension`、`CwF`，
以及从这些结构提取的 Ty、Tm、转换、替换、扩张、投影、变量和配对。
后续类型构造子作为独立接口添加。

## 7. 第一个模型：由类型代码族得到模型

取已有形式的数据：

```text
Code : SetC
El : FamS Code
```

这只是一个指定的广集及其解码族；暂不要求它包含所有广集，
也不要求 Σ/Π 闭包、类型内部宇宙或 univalence。

令上下文范畴为 `SetCat`，定义：

```text
Ty Γ       := Γ →S Code
A ≈Ty B    := ∀ γ, A γ ≈S B γ

Tm Γ A     := SectionS El[A]S
(e ▸ t) γ  := transpS El (e γ) (t γ)

A[σ]Ty     := A ∘r σ
t[σ]Tm     := (γ ↦ t (σ γ))

Γ ▹ A      := SigS Γ El[A]S
p          := sig_base_resp El[A]S
q (γ,a)    := a
⟨σ;t⟩ γ    := (σ γ; t γ)
```

项及变量的尊重性证明使用传输相干性。
实现复用 [FamSection](../theories/Instance/Set/Fam/Section.v) 的截面重索引、
泛变量及配对泛性质，沿解码复合比较对齐 `El[A][σ]` 与 `El[A ∘ σ]`。
为此，[FamSectionMap](../theories/Instance/Set/Fam/SectionMap.v) 增加了通用操作
`section_fam_map_resp`，将固定基底族态射作用于截面，记作 `φ ▷Fam s`。

[模型文件](../theories/Instance/Set/CwF.v) 提供：

- `CodeTerms El Γ`：类型代码函数上的相干项族。
- `CodeFamily El Γ`、`code_sub El σ`、`CodeTyTmF El`：类型、项与替换构成的族值函子。
- `code_pair_resp El A σ t`：复用截面配对，计算为 `δ ↦ (σ δ; t δ)`。
- `CodeExtensions El`：扩张、投影、泛变量及完整泛性质。
- `SetCwF El`：结合终上下文后的完整 CwF 模型。

具体模型需显式启用，例如先定义 `Definition model := SetCwF El`，
再声明 `Local Existing Instance model`。随后继承终对象和扩张结构，
可直接使用抽象层的替换、配对及 β/η 定律。

在这个模型里，严格类型相等就是代码函数的逐点相等；
严格项相等就是截面的逐点相等。已有 El 的相干传输提供类型转换，
A 阶段的重索引比较用于对齐解码族。

Code/El 是首个实例的选择，**不是 CwF 接口要求所有模型都采用代码**。
这个实例覆盖 Code/El 所分类的类型族。若要以全部 `FamS Γ` 为类型，
仍需为这个类型集合设计指定相等及相干的项传输；只把任意族同构设为相等，
再按各个同构转换项，会遇到第 2 节的冲突。

模型的上下文与解码纤维使用同一组载体层级 u、关系层级 p，
从而对上下文扩张封闭；u 与 p 支持两种严格大小排列。
代码集合的载体与相等见证可独立取更大的层级。
代码替换通过基础层的尊重映射复合实现，Code 无需成为所选上下文范畴的对象。
抽象接口不把这个模型的解码纤维大小约定写成普遍公理。

## 8. 宇宙与文件安排

上下文对象、态射、态射等价、类型代码、类型等价、项、项等价的大小分别检查；
结构律可用辅助宇宙。不能因为 T 的目标是 FamCat 就把这些层级设为相同。
项由截面构成，类型由尊重等价的函数构成，它们的实际大小包含相应的尊重性字段，
不能简单沿用解码纤维的大小。

只在推断会丢失必要通用性的定义处显式命名宇宙；调用处保持推断。
实现时检查不等层级的实例，并对基础定理运行 `Print Assumptions`。
恢复后的临时检查直接要求 `Ty T Γ : SetC@{a c}`、
`Tm T Γ A : SetC@{b d}` 及相反的大小排列，
不依赖 `FamCat` 自动生成的辅助宇宙参数顺序。

文件安排：

- [DTT/CwF.v](../theories/DTT/CwF.v)：已实现的 CwF 抽象接口和派生结构律。
- [DTT/Context/Extension.v](../theories/DTT/Context/Extension.v)：配对数据预层、表示广集同构及自然性。
- [DTT/Context/Representation.v](../theories/DTT/Context/Representation.v)：从选定表示反向恢复上下文扩张及 CwF，并比较双向往返。
- [DTT/Context/Conversion.v](../theories/DTT/Context/Conversion.v)：沿类型相等的扩张同构及其相干性。
- [DTT/Context/Pullback.v](../theories/DTT/Context/Pullback.v)：替换提升、相干性及显示投影的拉回泛性质。
- [DTT/Comprehension.v](../theories/DTT/Comprehension.v)：显示映射形式的类型总范畴及对应的 comprehension 结构。
- [DTT/Context/Section.v](../theories/DTT/Context/Section.v)：项与显示投影截面的广集同构及替换相容性。
- [Instance/Set/CwF.v](../theories/Instance/Set/CwF.v)：Code/El 模型。
- 必要的截面映射等可复用数学放回已有族/截面模块，不另建实验框架。

## 9. 范围与验证现状

第一阶段目标是无类型构造子的 CwF 核心及一个 Code/El 模型，
以转换、替换、上下文扩张和 β/η 为验收点。目前已完成：

- 从 T 提取类型、项、转换、替换及其单位、复合、尊重相等定律。
- 用 `is_context_pair` 保留基映射相等见证，再定义完整的扩张泛性质。
- 从选择的扩张提取透明的配对与 β₁，证明经转换的 β₂、η 和唯一性。
- 证明 β₂ 对任意基映射相等见证成立，并证明配对尊重项和基映射相等。
- 构造完整的 Code/El 模型，并复用抽象接口的 β/η 和唯一性定律。
- 构造配对数据的广集与预层，证明上下文扩张的表示同构及其自然性，导出配对复合律。
- 沿指定类型相等构造保持投影与变量的扩张同构，证明见证独立、单位、复合及配对相容性。
- 构造替换提升，沿扩张同构证明相等、单位与复合相容性，以及显示投影的拉回泛性质。
- 以显示交换方块为态射构造类型总范畴，组装对应的 comprehension，并证明笛卡尔态射恰对应拉回方块。
- 构造到箭头范畴的 comprehension 函子，证明当前 CwF 显示方块呈现的全忠实性。
- 推广任意范畴的截面广集，证明 CwF 项与显示投影截面的同构、配对及替换相容性。

固定族值预层 T 后，已可从配对预层的选定表示反向构造上下文扩张及 CwF，
并证明投影、变量、配对及表示的往返相容性。
[反向构造设计](./CwFRecovery.md) 区分这个已实现的必要充分准则，
以及下一阶段从显示映射和拉回数据构造 T 与表示所需的相干性。
从任意 comprehension 提取这些输入及不同呈现之间的比较仍是后续工作。

任意 comprehension 到 CwF 的转换、split replacement、
以及 Σ/Π/Id 的支持分别陈述附加假设后再开展。
[Local universes](https://arxiv.org/abs/1411.1736) 是需要额外条件和比较证明的构造，
不从现有弱 comprehension 接口无条件推出。

文献中的集合与等式按本库上述约定表述；结构定义及表示泛性质参考
[Castellan–Clairambault–Dybjer，§2.2、§5.1](https://perso.ens-lyon.fr/pierre.clairambault/cwfs.pdf)。
与采用其他基础约定的形式化之间的比较，另行给出精确命题；
本阶段不为此增加第二套 CwF 接口。

设计阶段的临时可行性检查已构造并编译
`A ↦ SectionS El[A]S` 作为代码函数广集上的相干族，
并检查不同代码/关系/解码纤维宇宙，以及布尔自同构的不同作用。
抽象核心的临时检查另构造了一个点模型，其中相等见证为 `bool`，
检验两种见证下的转换、配对 β/η、替换记号及扩张记号的连续使用。
结构包检查确认：启用 CwF 后可自动推导终对象和上下文扩张，
而只导入模块时不会选出任何具体模型。
宇宙检查覆盖上下文态射、类型、项的载体与各自相等关系处于不同层级的两个方向。
这些检查保留在仓库外，未增加常驻测试模块。

Code/El 模型另用一个布尔实例检查：代码有两个等价的代表，每对代码之间又有
两个 Type 值相等见证；不同代表之间的解码转换翻转布尔值。
实际计算验证了转换、替换和配对，并检查了等价替换与配对的相容性及 β/η。
这覆盖了非平凡转换，而不仅是常值项族。显式模型启用也有独立的临时检查。
计算检查还发现，基础函数广集和集合族态射的等价见证必须保持透明，
才能让依赖这些见证的转换归约；相关构造已改用 `Defined`。
此处的实际回归保留在 [Computations.v](../tests/Computations.v)，
通过会检查相等见证的解码传输确认复合替换转换能直接计算。
模型的宇宙回归保留在 [Universes.v](../tests/Universes.v)，
包括代码大于上下文、上下文载体/关系的两种排列，以及反向的代码载体/关系排列。
表示定理的宇宙回归另检查上下文态射、类型、项的载体与相等见证的独立层级，
覆盖两个方向的大小排列。临时布尔实例检查配对数据相等、非平凡转换下的重索引、
表示同构两个方向的实际计算，以及配对自然性；这些实例未另增常驻测试。
扩张转换另有 18 项临时公理检查，均无额外假设；布尔实例直接计算出
不同代码代表之间的扩张转换翻转纤维值，对称转换翻转回来，
并检查自相等、不同相等见证及配对/复合相容性。
已有的宇宙回归也检查两种大小排列下的扩张同构，未新增永久的布尔实例。
显示投影拉回的 24 项临时公理检查也均无额外假设。
布尔实例的锥满足广集相等，但底边替换与右边投影给出不同的代码代表；
中介态射可计算地完成非平凡纤维转换，并验证两条投影律、唯一性及锥相等见证独立性。
同一临时检查确认只启用 CwF 模型时不会选出 `HasPullback SetCat`。
常驻宇宙回归增加了两个方向的显示投影拉回检查，较大的实例仍留在仓库外。
Comprehension 构造及其临时实例的 23 项公理检查均无额外假设。
临时实例验证笛卡尔分解的非平凡纤维转换、交换证明见证独立、
不可逆的显示映射及其非笛卡尔性、复合记号连续使用，以及选择结构的显式启用。
这些实例仍留在仓库外。
常驻宇宙检查覆盖类型总范畴的 hom 广集及 comprehension 在两种大小排列下的实例化。
由于交换见证保留为数据，总范畴的态射载体需要容纳原态射及其相等见证；
其相等关系仍在原 `HomEq` 层级，不合并原范畴的两个层级。
另外的临时检查将类型和项固定在 `SetC@{Set Set}`，也能在更大的上下文态射层级上实例化 comprehension。
箭头范畴、全忠实性及项截面同构另有 24 项临时公理检查，均无额外假设。
布尔实例验证交换方块的证明见证不影响相等、全性提取的原像可直接计算、
复合与项/截面记号可连续使用，以及新截面操作与原集合族操作一致。
一个截面故意返回不同但等价的基底代表，其逆向项映射确实通过非平凡转换恢复原代表的纤维值。
这些检查仍留在仓库外；常驻宇宙回归检查两个大小方向的箭头 hom、截面广集、
CwF 全忠实性及项截面同构。箭头和截面保留 Type 值交换/右逆见证，
故它们的载体容纳这些见证，相等仍使用原态射相等层级。
一般箭头笛卡尔判别及选定结构转换另有 22 项临时公理检查，均无额外假设。
广集实例验证：只满足指定相等、代表值不同的交换锥也能给出可计算的笛卡尔因子；
反向判别及往返恢复的拉回中介态射可以直接归约；不同交换见证不影响中介态射的指定相等。
还验证了不可逆的布尔压缩方块既非笛卡尔也非拉回、非恒等基底同构确实改变第一投影，
以及两种选定结构必须显式启用。
这些实例与公理输出仍保留在仓库外。常驻宇宙回归只增加两个方向的一般判别与选定结构转换检查。

恢复并调整基础层引用后，在 Rocq 9.0.1、Dune 3.21.0 下，
`dune build @all @runtest @install` 通过。
抽象核心的 40 项与 Code/El 模型的 17 项 `Print Assumptions` 检查均无额外假设，
表示构造与其临时实例的 20 项检查也无额外假设，
并用归约确认模型的配对映射及表示同构两个方向可计算。临时实例和公理输出属于本地检查，
仓库中的计算和宇宙回归参与 CI；具体提交的 CI 结果记录在
[#13](https://github.com/Godalin/rocq-cats/issues/13)。

已接受的三个设计决定：

1. 采用本库默认集合及相等约定，接口直接命名为 CwF；严格替换律使用指定相等。
2. 使用一个现成的 FamCat 值函子统一组织类型、项和替换，并由泛性质提取配对。
3. 首个实例从 Code/El 开始；不把“任意族同构”选作类型相等，
   也不声称已经覆盖全部相干族。
