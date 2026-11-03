# Duality and colimits

# 对偶与余极限

## Opposite diagrams and cocones

## 反图式与余锥

[Diagram.Dual](../theories/Cat/Diagram/Dual.v) defines a cocone
`D ⇒∇ X` as the natural transformation `D ⇒ ConstF J X`.
Postcomposition is written `f ∘Cocone κ`; `MapCocone F κ` applies a functor
to its legs and apex. The equality of cocones is pointwise hom equality.

[Diagram.Dual](../theories/Cat/Diagram/Dual.v) 将余锥 `D ⇒∇ X`
定义为自然变换 `D ⇒ ConstF J X`。后合成为 `f ∘Cocone κ`；
`MapCocone F κ` 将函子作用于锥腿和顶点。余锥相等为逐点 Hom 相等。

`CoconeOp` and `CoconeUnop` convert between cocones on `D` and cones on
`D^opF`. `ConeOp` and `ConeUnop` give the converse orientation. They keep
the underlying arrows, respect pointwise equality, and cancel pointwise.
No comparison of functor records or naturality witnesses is involved.

`CoconeOp` 与 `CoconeUnop` 在 `D` 的余锥和 `D^opF` 的锥之间转换；
`ConeOp` 与 `ConeUnop` 处理反方向。转换保留底层箭头，保持逐点相等，
往返也按逐点相等成立；不比较函子记录或自然性见证。

`CoconeCat D` is the opposite of `ConeCat (D^opF)`; its objects present
cocones by their opposite cones. A native cocone `κ` is represented by
`(X; CoconeOp κ)`. Morphisms compare only their underlying apex maps,
and `CoconeApexF` forgets them to `C`.

`CoconeCat D` 是 `ConeCat (D^opF)` 的反范畴，对象通过反锥表示余锥。
原生余锥 `κ` 在其中表示为 `(X; CoconeOp κ)`。态射只比较底层顶点映射，
`CoconeApexF` 将它们忘却到 `C`。

## Universal properties and selected structures

## 泛性质与选定结构

[Colimit.Core](../theories/Cat/Colimit/Core.v) defines
`is_colimit κ := is_limit (CoconeOp κ)`.
`colimit_universal_iff` exposes the direct form: every cocone `μ : D ⇒∇ X`
has a unique `h : L → X` satisfying `h ∘Cocone κ ≈N μ`.
`limit_iff_op_colimit` also gives the reverse duality for limiting cones.

[Colimit.Core](../theories/Cat/Colimit/Core.v) 定义
`is_colimit κ := is_limit (CoconeOp κ)`。
`colimit_universal_iff` 给出直接形式：对每个余锥 `μ : D ⇒∇ X`，
存在唯一 `h : L → X`，使 `h ∘Cocone κ ≈N μ`。
`limit_iff_op_colimit` 也给出极限锥方向的对偶对应。

`HasColimit C D` chooses `colim D`, its injections `ιcolim[D]`, and
their universal property. The mediator `colim⟨ μ ⟩` is extracted from that
property; beta, eta, respectfulness and postcomposition follow from it.
`ColimitOpLimit` and `OpLimitColimit` convert selected structures without
installing global instances. `colimit_iff_initial` and `colimit_unique`
reuse the general limit and terminal-object results.

`HasColimit C D` 选择 `colim D`、注入 `ιcolim[D]` 及其泛性质。
中介 `colim⟨ μ ⟩` 从泛性质提取；β、η、保相等性与后合成律均由此导出。
`ColimitOpLimit` 与 `OpLimitColimit` 转换选定结构，不注册全局实例。
`colimit_iff_initial` 与 `colimit_unique` 复用一般极限及终对象定理。

## Adjunctions and preservation

## 伴随及保持性

`HasColimitsOfShape C J` supplies `ColimitF : Fct J C → C`.
[Colimit.Adjunction](../theories/Cat/Colimit/Adjunction.v) proves
`ColimitF ⊣ Δ[J,C]`. Conversely, the unit of any specified left adjoint
to the diagonal supplies chosen colimits. The two constructions form
`colimits_iff_diagonal_left_adjoint`, without equality of structure records.

`HasColimitsOfShape C J` 给出 `ColimitF : Fct J C → C`。
[Colimit.Adjunction](../theories/Cat/Colimit/Adjunction.v) 证明
`ColimitF ⊣ Δ[J,C]`。反之，任意给定的对角函子左伴随，其单位给出选定余极限。
双向构造形成 `colimits_iff_diagonal_left_adjoint`，不要求结构记录相等。

[Adjunction](../theories/Cat/Adjunction.v) constructs
`OpAdjunction : F ⊣ G → G^opF ⊣ F^opF` from the inverse hom correspondence.
Its unit and counit are the original counit and unit, respectively.
[Colimit.Preservation](../theories/Cat/Colimit/Preservation.v) then derives
`left_adjoint_preserves_colimit` from right-adjoint limit preservation.
It assumes only that the specified source cocone is colimiting.

[Adjunction](../theories/Cat/Adjunction.v) 使用逆 Hom 对应构造
`OpAdjunction : F ⊣ G → G^opF ⊣ F^opF`；单位与余单位分别是原来的余单位与单位。
[Colimit.Preservation](../theories/Cat/Colimit/Preservation.v) 随后从
右伴随保极限导出 `left_adjoint_preserves_colimit`，只要求指定的源余锥为余极限。

Opposition preserves functor composition up to the existing natural
isomorphism, rather than equality of law records.
[Limit.Transport](../theories/Cat/Limit/Transport.v) supplies the reusable
bridge: limiting cones transport along invertible diagram transformations
and pointwise equality of cone legs. Preservation uses this bridge explicitly.

取反与函子复合通过已有自然同构相容，不要求定律记录相等。
[Limit.Transport](../theories/Cat/Limit/Transport.v) 提供通用桥梁：
沿可逆图式自然变换及锥腿逐点相等运输极限锥。保持性定理显式使用该桥梁。

## Scope and validation

## 范围与验证

All equalities above are the specified setoid equalities. Relations and
universal witnesses remain Type-valued; mediator maps are transparent.
The shape, hom-carrier, equality-witness and law universes remain separate.
The five permanent checks in [Universes](../tests/Universes.v) exercise
both hom/equality orderings, larger shapes, and mixed-category preservation.
Concrete computations and assumption audits are temporary checks.

以上相等均为指定的广集相等。关系与泛见证保留在 Type 中，中介映射透明。
形状、Hom 载体、相等见证及定律的宇宙保持分离。
[Universes](../tests/Universes.v) 中五项永久检查覆盖 Hom／相等大小的两种排列、
更大的形状及混合范畴的保持性。具体计算与公理审计保留为临时检查。

This establishes the general dual foundation for issue #22. Named
coproduct, coequalizer and pushout interfaces, their special-shape
correspondences, and dual finite-limit constructions remain subsequent work.
Finite limits of `C` alone do not imply finite colimits of `C`.

这建立了 issue #22 所需的一般对偶基础。命名的余积、余等化子及推出接口、
相应的特殊形状对应，以及有限极限构造的对偶版本仍为后续工作。
仅有 `C` 的有限极限并不推出 `C` 的有限余极限。
