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

Use brackets when a public term notation takes a selected object, boundary
or other explicit data. Keep Rocq's `@` for explicit application of a name.
For ordinary term `Notation`, `Infix` and `Reserved` grammar, write the
precedence explicitly. Open `(at level …)` on its own line with two spaces
of indentation. Break a long list of modifiers at commas and indent its
continuation two more spaces. A scope starts on a separate line at two
spaces, with the colon at the start of that line. Keep a short interpretation
on the declaration line. For a long one, break before `:=` and indent it two
spaces, with the interpretation beginning immediately after `:=`.
Numeral and string notations use Rocq's primitive grammar. Give them a scope
without a precedence modifier. Named abbreviations and tactic notation use
their own grammar. A record field's `where` interpretation uses the
precedence in its reserved grammar.
Use level 0 for closed bracket notation and level 1 for new projection-like
postfix notation. For an existing precedence, group terms explicitly when
needed to avoid Rocq's deprecated level tolerance.

公共项记号若显式传入选定对象、端点或其他数据，用方括号标记；`@` 留给
Rocq 原生的显式应用。普通项记号 `Notation`、`Infix` 及其 `Reserved`
语法显式写优先级，`(at level …)` 另起一行，缩进两空格。
选项列表过长时在逗号后换行，续行再缩进两空格。作用域在冒号前换行，
缩进两空格。短解释与声明头同行，长解释在 `:=` 前换行并缩进两空格，
解释紧跟 `:=`。数值和字符串记号使用 Rocq 的原生语法，声明作用域即可省去
优先级选项。具名简写和战术记号使用各自的语法。记录字段的
`where` 解释沿用预留语法中的优先级。封闭方括号记号用级别 0，
新的投影式后缀用级别 1。保留既有优先级时，必要处明确加括号，
避免依赖 Rocq 将移除的宽松解析。

```coq
Notation "'id[' X ']'" := (@id _ X)
  (at level 0, format "id[ X ]")
  : hom_scope.

Infix "∘Nh" := HCompN
  (at level 50, left associativity)
  : cat_scope.
```

For record literals, keep named fields, the first field immediately after
`{|`, and aligned `;` and `|}`. Put a multiline record's closing delimiter on
its own line. Prefer a short constructor for a single-field wrapper.

记录字面量保留具名字段，首字段紧跟 `{|`，后续 `;` 和 `|}` 对齐；
多行记录的闭合符另起一行。单字段包装优先用简短构造器。

## Object and morphism products / 对象积与态射积

In functor/product theory that mixes object and morphism products, put
`Local Open Scope ob_scope.` after the other local scope openings. This
lets a coerced functor application such as `F (X × Y)` use object notation.
The existing argument scopes of `fmap`, composition and hom equality select
morphism notation for their arrow arguments, so the same formula can use
both products without explicit delimiters. Keep this default local to the
module or section; importing the theory retains the caller's scope choices.

在同时使用对象积与态射积的函子／积理论中，将
`Local Open Scope ob_scope.` 放在其他局部作用域打开命令之后，
使经强制转换的函子应用 `F (X × Y)` 使用对象记号。`fmap`、复合及 Hom 相等
已有的参数作用域会为其箭头参数选择态射记号，因此同一公式可不加显式分隔符
地使用两种积。这个默认设置限于当前模块或节；导入理论后保留调用方自己的
作用域选择。

```coq
Local Open Scope ob_scope.

Definition mapped_product {C D : Cat} `{PC : !HasProduct C}
    (F : Fct C D) {X Y X' Y' : C}
    (f : Hom X X') (g : Hom Y Y')
  : Hom (F (X × Y)) (F (X' × Y'))
  := fmap F (f × g).
```

A bare morphism product outside an argument with a known hom scope may
still need `%hom`. Give new operation arguments their mathematical scopes
through their types or `Arguments`, and keep bundle-owned choices explicit
where multiple choices share a category. Scope defaults choose notation;
the supplied terminal/product evidence still determines the construction.

没有已知 Hom 参数作用域的独立态射积仍可能需要 `%hom`。新增运算通过参数
类型或 `Arguments` 指定相应数学作用域；同一范畴有多份选择时，结构包拥有的
选择仍须显式固定。默认作用域决定记号解释，构造所用终对象／积仍由给定证据
决定。

Keep the existing separate English/Chinese coqdoc blocks and blank lines
around comments. Apply layout changes to the requested region, rather than
reflowing unrelated source while editing mathematics. Settle formatting
before expensive validation, following [the testing guide](./Testing.md).

沿用独立的英／中文 coqdoc 注释块及注释前后的空行。
排版调整限于当前请求范围，不在修改数学内容时顺便重排无关源码；
按[测试指南](./Testing.md)在昂贵验证前收齐排版。
