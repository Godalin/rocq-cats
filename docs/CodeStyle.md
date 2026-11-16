# Rocq source layout / Rocq 源码排版

These conventions capture repeated reviewed formatting in
[Cat/Natural.v](../theories/Cat/Natural.v),
[Cat/Adjunction.v](../theories/Cat/Adjunction.v) and
[Cat/ProductPullback.v](../theories/Cat/ProductPullback.v).
Group code by its mathematical and proof structure. About 80 columns is
a readability guide, not a reason to pack every short declaration or to
split every argument onto a separate line. Preserve the reviewed local
layout; do not turn isolated inconsistencies into general rules.

这些约定归纳自上述文件中反复出现、经用户手调的排版。按数学和证明结构组织
代码，约 80 列是可读性参考，不必把短声明尽量塞满，也不把每个参数都拆成
单独一行。保留已审阅的局部排版，不把偶见的不一致推广成规则。

## Declaration groups / 声明分组

Keep the ambient categories or structures near the declaration name.
Group dependent functors, objects and morphisms by role; related implicit
and explicit binders may share a line. Ordinary declaration parameter
continuations use four spaces; continued `Context` groups use two.
A declaration may benefit from these groups even when it fits on one line.

环境范畴或结构放在声明名附近，依赖它们的函子、对象及态射按角色分组；
相关的隐式、显式参数可以同行。普通声明的续行参数缩进四空格，
`Context` 的续行分组缩进两空格。不必等到一行超长才这样分组。

```coq
Definition HCompN {C D E : Cat}
    {G G' : Fct D E} {F F' : Fct C D}
    (β : G ⇒ G') (α : F ⇒ F')
  : (G ∘F F) ⇒ (G' ∘F F')
  := (β ∘Nr F') ∘Nv (G ∘Nl α).

Context {C D : Cat}
  {F : Fct C D} {G : Fct D C}
  (A : F ⊣ G).
```

## Types and terms / 类型及项

Start the result-type `:` and definition-body `:=` on separate lines,
each indented two spaces. Split a long result at an equation, connective
or complete argument boundary. Indent a nested argument one further level;
avoid large padding merely to align with the width of a keyword.

结果类型的 `:` 和定义体的 `:=` 各自另起一行，缩进两空格。
长结果在等式、联结词或完整参数的边界换行；嵌套参数再进一层，
不为对齐关键字的字符宽度补一长串空格。

```coq
Global Instance nat_whisker_l_proper {C D E : Cat}
    (G : Fct D E) {F F' : Fct C D}
  : Proper (NatEq ==> NatEq)
      (@WhiskerLN C D E G F F').

Theorem adj_unit_universal {X Y} (g : Hom X (G Y))
  : is_unique (λ f, fmap G f ∘ adj_unit X ≈ g)
      (unadjunct g).
```

## Proof steps / 证明步骤

Keep short steps belonging to one phase together, such as
`intros X. exists id.`. Split before a longer `change`, `exact`,
`apply` or a new proof phase. Use two-space proof nesting; do not build
column alignment around the spelling or width of a bullet. Wrap long
`rewrite` lists at commas, retaining coherent groups of laws together.

同一阶段的短步骤可以同行，如 `intros X. exists id.`。
较长的 `change`、`exact`、`apply` 或新的证明阶段另起一行。
证明按两空格层级缩进，不围绕分支标记的拼写或宽度做列对齐。
长 `rewrite` 列表在逗号处换行，相关定律仍可成组同行。

```coq
Next Obligation. intros X. exists id.
  split; cbn; apply comp_id_l.
Defined.
```

A whole short proof can remain `Proof. ... Qed.` or a one-line obligation.
Once the body spans lines, put `Qed.` or `Defined.` on its own line.
The first short step may stay after `Proof.` or `Next Obligation.`;
one tactic per line is not compulsory.

完整短证明可以保留 `Proof. ... Qed.` 或单行义务。
证明体跨行后，`Qed.`／`Defined.` 独占一行。开头的短步骤可以接在
`Proof.`／`Next Obligation.` 后，不强制每条战术都单占一行。

## Notation and records / 记号及记录

Separate notation's interpretation from its parsing options when grouping
helps reading. Keep options and the scope together when they remain short.
For record literals, retain named fields, the first field immediately after
`{|`, and aligned `;` and `|}`. Put a multiline record's closing delimiter on its
own line. Prefer a short constructor for single-field wrappers, as in
`Lift f` and `Lift H`, rather than a verbose field literal.

记号的解释与解析选项按需分行；选项和作用域较短时可同行。
记录字面量保留具名字段，首字段紧跟 `{|`，后续 `;` 和 `|}` 对齐；
多行记录的闭合符另起一行。单字段包装优先用简短构造器，如 `Lift f`、`Lift H`，
避免冗长的字段字面量。

```coq
Infix "∘Nh" := HCompN
  (at level 50, left associativity) : cat_scope.
```

Keep the existing separate English/Chinese coqdoc blocks and blank lines
around comments. Apply layout changes to the requested region, rather than
reflowing unrelated source while editing mathematics. Settle formatting
before expensive validation, following [the testing guide](./Testing.md).

沿用独立的英／中文 coqdoc 注释块及注释前后的空行。
排版调整限于当前请求范围，不在修改数学内容时顺便重排无关源码；
按[测试指南](./Testing.md)在昂贵验证前收齐排版。
