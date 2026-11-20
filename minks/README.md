# Minks

This is the first prototype for [issue #48](https://github.com/Godalin/rocq-cats/issues/48).
It is packaged as `rocq-minks` in its own Dune project and exposes
the Rocq entry point `Minks.all`. Cats depends on this package.

这是 [#48](https://github.com/Godalin/rocq-cats/issues/48) 的第一版原型。
独立的 Dune 项目将它打包为 `rocq-minks`，提供 Rocq 模块
`Minks.all`。Cats 依赖这个包。

To build the package with Rocq 9.3.0 and Rocq-Elpi 3.5.1 in the project switch:

在项目 switch 中使用 Rocq 9.3.0 和 Rocq-Elpi 3.5.1 构建工具包：

```sh
cd minks
opam exec --switch=rocq-cats -- dune build
```

If the current shell already uses the `rocq-cats` switch, run `dune build`
directly. The local `dune-workspace` makes `minks/` the build root. From the
repository root, Dune can also build Minks as part of the Cats workspace.
Use `dune build @install` inside `minks/` to check its package artifacts.

若当前 shell 已使用 `rocq-cats` switch，直接运行 `dune build` 即可。
本目录的 `dune-workspace` 将 `minks/` 设为构建根。从仓库根目录运行时，
Dune 也可以在 Cats 工作区内构建 Minks。要单独检查打包产物，在
`minks/` 内运行 `dune build @install`。

The `@install` target prepares the package files without installing them
into the switch. To install the local package, run
`opam install --switch=rocq-cats .` from this directory.

`@install` 只准备安装文件。若要装入 switch，在本目录运行
`opam install --switch=rocq-cats .`。

Import [`Minks.all`](theories/all.v) to use `Minks.Struct` and `Minks.Inspect`.
[Spec.v](theories/Spec.v) handles component identity and inheritance;
[Flat.v](theories/Flat.v) generates Rocq declarations.

导入 [`Minks.all`](theories/all.v) 即可使用 `Minks.Struct` 和 `Minks.Inspect`。
[Spec.v](theories/Spec.v) 处理组件身份及继承，[Flat.v](theories/Flat.v)
生成 Rocq 声明。

[examples/Algebra.v](examples/Algebra.v) declares the mixins and supplies
examples such as:

[examples/Algebra.v](examples/Algebra.v) 声明 Mixin，并给出如下示例：

```coq
From Minks Require Import all.

(* After declaring HasMagma and generating SetC: *)
Minks.Struct Magma extends SetC
  with  hasMagma : HasMagma [carrier, hasEquiv].

(* After generating both parents: *)
Minks.Struct Monoid extends Semigroup, UMagma.
Minks.Inspect Monoid.
```

Both `extends` and `with` are optional. List parents and new components
with commas; bracketed keys give the arguments to a mixin in order.
Parents must have been generated already. Earlier fields supply the
dependencies of later fields. The examples build under `@runtest` and
are not installed with the package.

`extends` 和 `with` 均可省略。用逗号分隔父结构或新组件；方括号中的键
按顺序传给 Mixin。父结构须先生成，后续字段可依赖前面的字段。
`@runtest` 编译例子，安装包时不包含它。

Use keys such as `hasPoint`, `hasMagma`, and `hasUnit` for stored mixins.
A choice with a mathematical role has its own class: `HasUnit` selects the
unit of the existing multiplication and provides its laws, just as
`HasBottom` selects a bottom for an existing order. `HasPoint` serves
pointed structures; distinct choices of that class use distinct keys,
as in `TwoPoints`.

存储组件使用 `hasPoint`、`hasMagma`、`hasUnit` 等键。有特定数学角色的
选取使用自己的类：`HasUnit` 为已有的乘法选单位元并提供定律，
就像 `HasBottom` 为已有的序选底元。`HasPoint` 用于带点结构；
同一个类有多份选择时用不同的键区分，如 `TwoPoints`。

Write named class dependencies with backtick parentheses, for example
`` `(E : !HasEquiv A) `(M : !HasMagma A E) ``.
The parameters remain explicit when applying the class, and their witnesses
are available to instance search within the declaration. The `!` keeps the
class application's supplied arguments. Rocq can still infer the instances
on methods such as `mul_assoc x y z`. Bracketed keys in `Minks.Struct`
connect the parameters to selected mixins.

类依赖用反引号加圆括号，例如
`` `(E : !HasEquiv A) `(M : !HasMagma A E) ``。
应用类时参数依然显式，在声明内部这些见证可由类型类搜索找到。
`!` 让类应用沿用给出的参数。调用 `mul_assoc x y z` 等方法时仍可推断实例。
`Minks.Struct` 的方括号把这些参数接到各自选定的组件。

Indent `with` by two spaces, leave two spaces after the keyword, and align
continuation entries. A future alias block would use one `where` after
`with`, with one space after its keyword to align the entries. Use role
names in the class first; reserve `where` for structure-specific aliases.

`with` 缩进两格，关键字后空两格，后续条目对齐。若以后需要结构特有的别名，
可在 `with` 后加一个 `where`，关键字后空一格以对齐；优先在类里定义角色名。

The examples use the UTF-8 notation from Stdlib 9.2 or later.
From this directory, build and check them:

例子使用 Stdlib 9.2 起提供的 UTF-8 记号。在本目录下编译并检查：

```sh
opam exec --switch=rocq-cats -- dune runtest
```

To load the example in a Rocq session after building:

编译后可在 Rocq 会话中加载例子：

```sh
opam exec --switch=rocq-cats -- rocq repl -q -Q _build/default/theories Minks -l examples/Algebra.v
```

For VS Code, use the `rocq-cats` switch's VsRocq server. The local
[`_CoqProject`](_CoqProject) maps the built theory to `Minks` and loads Elpi
when the editor initializes the document. After changing the project file,
reload the VS Code window so VsRocq reopens the document with those options.

在 VS Code 中使用 `rocq-cats` switch 的 VsRocq 服务。本目录的
[`_CoqProject`](_CoqProject) 将构建产物映射到 `Minks`，并在编辑器初始化
文档时加载 Elpi。修改项目文件后，重新加载 VS Code 窗口以应用新参数。

In that session, inspect the generated declarations and universe constraints:

要看生成的声明和宇宙约束，在会话中输入：

```coq
Minks.Inspect Monoid.
Set Printing Universes.
Print Monoid.
Print MonoidToSemigroup.
Print MonoidToUMagma.
Print Assumptions monoid_magma_coherence.
```

Handwritten mixin classes describe the mathematical data and laws.
The structure declarations list parent edges and name selected components
and their dependencies. A slot key is a declared identity, so it is shared only when
the same key is used with matching dependencies. Distinct slots can have
the same Rocq type. The command computes the closure in dependency order,
declares a polymorphic flat record and installs transparent forgetful
functions to its direct parents. The carrier is a coercion to a sort.
For each class that occurs once in the resulting record, Minks exports
the field projection as an instance. If several slots use the same class,
all of those projections remain explicit. `Minks.Inspect` shows this as
`[instance]` or `[explicit]`.

手写 Mixin 类描述数学数据及定律。结构声明列出继承边、所选组件及其依赖。
组件键声明组件身份；只有键和依赖都一致才共享。同型的组件仍可分别选取。命令
按依赖顺序计算闭包，声明宇宙多态的平铺记录，并生成到直接父结构的透明忘却
函数。载体字段可强制转换成类型。若某个类在生成记录中只有一个组件，Minks
导出这个组件的投影实例；若同一个类对应多个组件，则保留显式投影。
`Minks.Inspect` 分别显示 `[instance]` 和 `[explicit]`。

The algebra example checks both diamonds by conversion, keeps two independent point
choices of the same type, and rejects incompatible dependencies on a
shared slot. It instantiates the generated magma in both strict orderings
of carrier and equality-witness universes.

代数例子以定义相等检查两个菱形；保留同型但独立选择的两个点；拒绝同一共享组件
的冲突依赖；并以载体和相等见证宇宙的两种严格次序分别实例化生成的原群。

[Lattice.v](examples/Lattice.v) builds meet and join semilattices over
a common poset, then combines a lattice with bottom and a lattice with top.
`HasBottom` and `HasTop` each store a chosen value and its bound law
on the lattice's selected order. A term such as `leq bottom x` uses
the instance selected for the carrier and order of `x`.

[Lattice.v](examples/Lattice.v) 从同一偏序生成交、并半格，再把带底元的格和
带顶元的格合成有界格。`HasBottom` 和 `HasTop` 分别保存选定的值及其
在格的选定序上满足的界律。`leq bottom x` 根据 `x` 的载体和选定的序
推断对应的底元实例。

The prototype assumes one external carrier and takes explicit positional
dependency mappings. It generates the packed record, its ordinary Rocq
constructor, and `To` views. Fixed-parent `Of` and relative `Is` views,
explicit universe-instance mappings, diagnostics for generated constraints
and inference of omitted dependencies remain follow-up work. Rocq currently infers
some additional upper bounds; the printed universe parameter positions
are experimental.

当前原型固定一个外部载体，并用显式的位置映射描述依赖。已生成平铺记录、
普通 Rocq 构造器及 `To` 视图。固定父结构的 `Of`、相对 `Is` 视图、
显式宇宙实例映射、生成约束的诊断及省略依赖的推断留给后续。Rocq 目前会推断
一些额外的上界，打印出的宇宙参数位置仍是实验接口。
