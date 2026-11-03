# Dual constructions and their ordinary interfaces

# 对偶构造及其通常接口

## One underlying construction

## 只保留一份底层构造

A dual construction uses the original theory on opposite categories. Ordinary
names, notation and arrow directions form an interface to that construction;
there is no independently rebuilt dual object and subsequent comparison theorem.
This rule is recorded in [AGENTS.md](../AGENTS.md).

对偶构造直接使用反范畴中的原理论。通常的名称、记号与箭头方向只构成该构造的
使用接口；不独立重建余对象，也不再证明两套构造的比较定理。
这一原则已记入 [AGENTS.md](../AGENTS.md)。

## Cocones

## 余锥

[Diagram.Dual](../theories/Cat/Diagram/Dual.v) stores a cocone `D ⇒∇ X`
through one field, `op_cone : Cone (D^opF) X`. `CoconeN` reads its legs
as the ordinary natural transformation `D ⇒ ConstF J X` and is a coercion,
so components and pointwise equality still use the ordinary interface.
`CoconeOfN` supplies ordinary natural-transformation data to this representation.
Neither adapter introduces a second cocone structure or universal property.

[Diagram.Dual](../theories/Cat/Diagram/Dual.v) 的余锥 `D ⇒∇ X`
只存储一个字段 `op_cone : Cone (D^opF) X`。`CoconeN` 将锥腿读作通常的
自然变换 `D ⇒ ConstF J X`，并作为强制转换，使分量及逐点相等继续使用通常接口。
`CoconeOfN` 将通常自然变换的数据送入该表示；两者都不引入第二种余锥结构或泛性质。

Postcomposition `f ∘Cocone κ` is opposite-cone precomposition. The action
`κ ∘∇ α` of a diagram transformation uses its opposite transformation and
the original vertical composition. `MapCocone F κ` uses `MapCone (F^opF)`
and the existing composition comparison. Laws reuse their original counterparts.
`CoconeCat D` and `CoconeApexF` likewise come from the cone category and apex
functor by opposition. A cocone is represented there by `(X; op_cone κ)`.

后合成 `f ∘Cocone κ` 就是反锥的预合成。图式自然变换的作用 `κ ∘∇ α`
使用其反变换及原来的垂直复合。`MapCocone F κ` 使用 `MapCone (F^opF)`
及已有复合比较；定律复用原来的对应定律。
`CoconeCat D` 与 `CoconeApexF` 同样由锥范畴及顶点函子取反得到，
余锥在其中表示为 `(X; op_cone κ)`。

## Colimits

## 余极限

[Colimit.Core](../theories/Cat/Colimit/Core.v) defines
`is_colimit κ := is_limit (op_cone κ)`. `HasColimit C D` contains only
`hasOpLimit : HasLimit (C^op) (D^opF)`. Object `colim D`, injections
`ιcolim[D]`, mediator `colim⟨κ⟩` and their universal laws read the original
limit data and theorems; the data are not reconstructed in a parallel record.

[Colimit.Core](../theories/Cat/Colimit/Core.v) 定义
`is_colimit κ := is_limit (op_cone κ)`。`HasColimit C D` 只包含
`hasOpLimit : HasLimit (C^op) (D^opF)`。对象 `colim D`、注入 `ιcolim[D]`、
中介 `colim⟨κ⟩` 及其泛性质定律直接读取原极限的数据与定理，
不在另一套平行记录中重建这些数据。

`HasColimitsOfShape C J` contains only the original selected structure
`HasLimitsOfShape (C^op) (J^op)`. `ColimitF` is constructed by taking the
opposite of `LimitF ∘F OpFctF` and adapting the double-opposite endpoints.
Its identity, composition and respectfulness are inherited functor laws.
Importing the modules does not choose any model structures.

`HasColimitsOfShape C J` 只包含原选定结构
`HasLimitsOfShape (C^op) (J^op)`。`ColimitF` 由 `LimitF ∘F OpFctF`
取反后适配双重反范畴端点得到；恒等、复合与保相等性直接继承已有函子律。
导入模块不会为具体模型选择结构。

## Adjunction and preservation interfaces

## 伴随与保持性接口

[Colimit.Adjunction](../theories/Cat/Colimit/Adjunction.v) exposes
`ColimitF ⊣ Δ[J,C]`. Its two hom maps are the inverse and forward maps of
the original opposite-limit adjunction, read at the ordinary endpoints.
The inverse and naturality laws use the original adjunction laws. Conversely,
`adjunction_unit_universal` supplies the stored opposite limit directly.
It is not necessary to prove a separate colimit mediator uniqueness theorem.

[Colimit.Adjunction](../theories/Cat/Colimit/Adjunction.v) 提供
`ColimitF ⊣ Δ[J,C]`。两个 Hom 映射是原反范畴极限伴随的逆、正向映射，
读回通常端点；互逆律及自然性使用原伴随定律。反向构造由
`adjunction_unit_universal` 直接给出存储的反范畴极限，无须另证余极限中介唯一性。

For arbitrary opposite-shape diagrams, `UnopF` reads a functor between
opposite categories in the original categories. `OpUnopF` supplies the
identity-component comparison back to the original diagram.
[TransportedLimit](../theories/Cat/Limit/Transport.v) reuses the existing
limit-transport theorem to expose the selected structure at that endpoint.
These are general functor/limit adapters, rather than duplicate dual constructions.

对于任意反形状图式，`UnopF` 将反范畴之间的函子读回原范畴，`OpUnopF`
提供返回原图式的恒等分量比较。
[TransportedLimit](../theories/Cat/Limit/Transport.v) 复用已有极限运输定理，
在该端点提供选定结构。它们是通用函子／极限适配，不是独立重建的对偶构造。

[Colimit.Preservation](../theories/Cat/Colimit/Preservation.v) directly
uses `right_adjoint_preserves_limit` with `OpAdjunction` on the stored cone,
then the composition comparison already used by `MapCocone`. The input
assumption is only that the specified source cocone is colimiting.

[Colimit.Preservation](../theories/Cat/Colimit/Preservation.v) 将
`OpAdjunction` 与 `right_adjoint_preserves_limit` 直接用于存储的锥，
再使用 `MapCocone` 中同一个复合比较；输入只要求指定源余锥为余极限。

## Validation and remaining work

## 验证与后续工作

Equalities use the designated setoid relations. Witnesses remain Type-valued
and computational maps transparent. The existing five permanent checks in
[Universes](../tests/Universes.v) cover independent hom/equality levels,
larger shapes and mixed-category preservation. Concrete computations and
assumption audits remain temporary.

相等使用指定广集关系，见证保留在 Type 中，计算映射保持透明。
[Universes](../tests/Universes.v) 中已有五项永久检查覆盖独立 Hom／相等层级、
更大的形状及混合范畴保持性；具体计算与公理审计仍作为临时检查。

Named coproduct, coequalizer and pushout interfaces and finite-colimit
constructions remain future work. They should wrap the original product,
equalizer, pullback and finite-limit constructions on opposite categories.

命名的余积、余等化子、推出接口及有限余极限构造仍为后续工作；
它们应包装反范畴中原来的积、等化子、拉回及有限极限构造。
