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

For an editor session using an uninstalled build, launch VsRocq with the
workspace's Dune environment so it can load the `rocq-minks.plugin` parser.
After building the local theory, use `opam exec --switch=rocq-cats -- dune
exec -- vsrocqtop` from the same workspace root. This adds the workspace's
local install library to `OCAMLPATH`.

使用未安装的本地构建时，通过工作区的 Dune 环境启动 VsRocq，才能加载
`rocq-minks.plugin` 语法插件。构建本地理论后，从同一工作区根目录运行
`opam exec --switch=rocq-cats -- dune exec -- vsrocqtop`，Dune 会把
工作区的本地安装库加入 `OCAMLPATH`。

Import [`Minks.all`](theories/all.v) to use `Minks.Mixin`, `Minks.Struct`, and `Minks.Inspect`.
[Spec.v](theories/Spec.v) handles component identity and inheritance;
[Flat.v](theories/Flat.v) generates Rocq declarations.

导入 [`Minks.all`](theories/all.v) 即可使用 `Minks.Mixin`、`Minks.Struct` 和 `Minks.Inspect`。
[Spec.v](theories/Spec.v) 处理组件身份及继承，[Flat.v](theories/Flat.v)
生成 Rocq 声明。

[examples/Algebra.v](examples/Algebra.v) declares the mixins and supplies
examples such as:

[examples/Algebra.v](examples/Algebra.v) 声明 Mixin，并给出如下示例：

```coq
From Minks Require Import all.

(* After declaring HasMagma and generating SetC: *)
Minks.Struct Magma extends SetC
  with  hasMagma : HasMagma.

(* After generating both parents: *)
Minks.Struct Monoid extends Semigroup, UMagma.
Minks.Inspect Monoid.
```

Use `Minks.Mixin` in place of the usual class keyword. One declaration
defines a Rocq typeclass and stores the mixin's direct dependencies.
Minks reads the parameter order from the Rocq type, so a structure can omit
component keys when its stored choices determine the dependencies uniquely.

### Mixin parameters / Mixin 参数

Write `extends` after the local parameters and before the definition body.
The first parent supplies the carrier. Minks puts shared inherited
parameters first, respecting their dependencies, then the remaining
inherited parameters in the order of the parent list and the parents'
declarations. Parameters written on the child are appended last, in
declaration order. Their types may refer to the inherited parameters.

An inherited mixin witness is shared when both paths refer to the same
declaration and arguments. A value parameter is identified by its
introducing declaration and position. Independent value parameters stay
distinct even when their names and types coincide. An incompatible
selection of the same ancestor is an error. Inheritance supplies the
chosen witnesses as typeclass parameters.

Carrier and value parameters retain the binder from their declaration.
Parentheses make them explicit, and braces make them implicit. Inherited
mixin witnesses are implicit typeclass arguments. For example, write
`IsMonotone A f` to infer the order, or `@IsMonotone A O f` to select `O`.
`Minks.Struct` selects dependencies in declaration order using the stored component keys.

A shared ancestor has one universe instance. Other inherited universes
follow their respective branches, and local parameters can introduce new
universes. An explicit universe declaration fixes its own positional
order, and an explicit parent instance such as `extends HasEquiv@{u p}` names the levels
to use from that context. With inferred universes, Rocq determines the
final universe list and constraints.

`extends` 写在本层声明的参数之后、定义体之前。第一个父级提供载体。Minks 优先放置
共享的继承参数，并满足它们的依赖顺序，再按父级列表及各父级的声明顺序放置
其余继承参数。本层声明的参数按顺序追加到最后，其类型可以引用继承参数。

两条路径引用同一 Mixin 声明与同一组实参时，共享一份见证。值参数由最初引入它的
声明及位置确定。不同声明各自引入的参数保持独立，即使名字和类型相同。同一前驱
的选择不相容时，声明报错。继承把这些选定见证作为类型类参数传入。

载体和值参数保留声明时的括号属性，圆括号为显式，花括号为隐式。
继承的 Mixin 见证默认作为隐式类型类参数。例如 `IsMonotone A f` 会搜索序，
`@IsMonotone A O f` 则指定序 `O`。`Minks.Struct` 仍按声明顺序根据组件键选择依赖。

共享前驱使用同一份宇宙实例，各分支拥有各自的其余继承宇宙，本层参数可以引入
新的宇宙。显式宇宙声明按自身的书写顺序决定位置。例如 `extends HasEquiv@{u p}`
指定父级从当前上下文使用哪些宇宙。省略标注时，最终的宇宙列表和约束由 Rocq 推断。

```coq
Minks.Mixin HasPoint (A : Type)
  :=
  { point : A }.

Minks.Mixin HasSecondPoint extends HasPoint
  :=
  { second_point : A }.

Minks.Struct Pointed
  with  hasPoint : HasPoint.
Minks.Struct TwoPoints extends Pointed
  with  hasSecondPoint : HasSecondPoint.
Minks.Inspect HasSecondPoint.
```

An indexed law can append a value parameter. To pack a selected value and
its law, put both fields together in a mixin that a structure can select.

依赖给定值的定律可以追加一个值参数。若要打包选定值及其定律，可以把两者放到
同一个供结构使用的 Mixin 中。

```coq
Minks.Mixin IsNamedPoint (x : A) extends HasEquiv
  :=
  { named_point_refl : equiv x x }.
```

[The closure example](examples/Closure.v) appends a map and then a point
to inherited parameters. [The universe example](examples/Universes.v)
checks inferred, named, open and monomorphic instances and verifies that
the two branches can vary their universe levels independently.

[闭包算子示例](examples/Closure.v) 先追加一个映射，再在继承参数后追加一个点。
[宇宙示例](examples/Universes.v) 检查推断、具名、开放和单态的实例，并验证
两个分支的宇宙层级可以独立变化。

### Struct packing and views / Struct 打包与转换

When a declaration has one parent and one new mixin whose sole argument is
that complete parent, `extends` stores the parent once. Its constructor
and parent projection are named `ChildOfParent` and `ChildToParent`.

若声明只有一个父结构和一个新 Mixin，且该 Mixin 的唯一参数就是完整父结构，
`extends` 会保存一份父结构。构造器和父投影分别命名为
`ChildOfParent` 和 `ChildToParent`。

```coq
Minks.Struct PointedSetC extends SetC
  with  hasPoint : HasPoint.
```

When the mixins refer to inherited components, `extends` merges those
components by key and shares the carrier. Inherited fields shared by
multiple parents come first in dependency order. The other inherited
fields follow parent and declaration order, followed by the local fields.
A stored-parent bundle can also
participate in this merge. For example, `MonoidalCat extends SemigroupalCat,
PremonoidalCat` shares the tensor and associator of both parents.

当 Mixin 依赖继承的组件时，`extends` 按键合并组件并共享载体。保存完整父结构
的打包也可以参与合并。多条父级路径共享的继承字段按依赖顺序放在前面，
其余继承字段按父级及声明顺序放置，最后追加本层字段。例如 `MonoidalCat extends SemigroupalCat, PremonoidalCat`
共享两条分支的张量和结合子。

Use `key as field : Mixin [dependencies]` to name a projection explicitly. Dependencies and
merging still use the key. A directly stored parent uses its record
projection. Minks constructs transparent views to all declared ancestors
of a flat structure from the exact fields it stores.

When a new flat structure is declared, Minks also checks both directions
against earlier flat structures in the same module. A proper subset of component
keys gives a view if the carrier, mixin identity and selected dependency
keys agree and the reconstructed record typechecks. The view becomes
available in the module where both structures first meet at a declaration,
so a larger structure may be declared first. Identical component sets keep their distinct identities. The generated views are named
`ChildToAncestor` and can be called explicitly.

用 `key as field : Mixin [dependencies]` 可指定投影名。依赖和合并仍按键进行。直接保存的父级
用记录投影。平铺结构到已声明祖先的透明转换从结构保存的字段重建目标。

声明新的平铺结构时，Minks 也会与同一模块中先声明的平铺结构双向比较。目标组件键为严格
子集、载体及 Mixin 标识和所选依赖键一致，且重建记录通过类型检查时，即可生成转换。
转换在两者首次一起参与检查的声明所在模块可用，因此可以先声明较大的结构。组件集合
相同的两个结构保留各自身份。生成的转换使用 `ChildToAncestor` 作为具名函数。

In flat declarations, both `extends` and `with` are optional. Commas
separate parents and components. Bracketed keys give mixin arguments in order.
Parents must have been generated already. Earlier fields supply the
dependencies of later fields. The examples build under `@runtest` and
are not installed with the package.

在平铺声明中，`extends` 和 `with` 均可省略。用逗号分隔父结构或新组件。方括号中的键
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

`Minks.Struct` accepts components declared with `Minks.Mixin`.
An explicit bracketed list selects stored components when there is more
than one matching choice, and each key is checked against the mixin's
parameter metadata. For example, `hasMagma : HasMagma [carrier, hasOtherEquiv]`
selects `hasOtherEquiv` as the equality for the multiplication.

`Minks.Struct` 的组件须由 `Minks.Mixin` 声明。若有多份匹配的选择，
可以用方括号指定组件键，每个键都会按 Mixin 的参数元数据校验。
例如 `hasMagma : HasMagma [carrier, hasOtherEquiv]` 使用
`hasOtherEquiv` 作为乘法依赖的广集相等。

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

Flat generation takes one shared carrier and explicit positional dependency
mappings. It generates the packed record, its ordinary Rocq constructor,
and `To` views. Relative `Is` views,
explicit universe-instance mappings, diagnostics for generated constraints
and inference of omitted dependencies remain follow-up work. Rocq currently infers
some additional upper bounds; the printed universe parameter positions
are experimental.

平铺生成固定一个外部载体，并用显式的位置映射描述依赖。已生成平铺记录、
普通 Rocq 构造器及 `To` 视图。相对 `Is` 视图、
显式宇宙实例映射、生成约束的诊断及省略依赖的推断留给后续。Rocq 目前会推断
一些额外的上界，打印出的宇宙参数位置仍是实验接口。
