(** * From Categories to Limits: One Boolean Example

    We will organize the same data in five successive ways: a category, a
    diagram functor, a natural transformation, a product and a limit. The
    concrete question is simple: how can we record a Boolean value together
    with its negation? Every definition and example below is checked by Rocq. *)

(** * 从范畴到极限：一个贯穿始终的布尔例子

    我们用五种逐步发展的结构组织同一份数据：范畴、图式函子、自然变换、积与极限。
    具体问题很简单：如何同时记录一个布尔值及其取反？下文的每个定义与示例都由
    Rocq 检查。 *)

From Stdlib Require Import
  Bool.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Diagram.Discrete
  Cat.Product.Core
  Cat.Limit.Core
  Cat.Limit.Product
  Instance.Bool.Group
  Instance.Set.Core
  Instance.Set.Product.

(** ** 1. A category supplies objects and composable arrows

    Work in [SetCat]. Its objects are setoids [SetC], and its arrows are
    functions preserving their specified equality. Arrow equality is
    pointwise equality in the target setoid. Identity and composition are
    the usual operations on functions, equipped with respectfulness proofs.

    Our object [BoolS] has carrier [bool] and specified equality [eq]. Native
    equality is this particular setoid's choice, not a requirement on other
    objects. Reusing [BoolS] does not select its optional algebraic structures.
    Negation gives our first arrow. Preservation of this native equality is
    inferred automatically. The following equation compares arrows in
    [SetCat]. *)

(** ** 1. 范畴提供对象与可复合的箭头

    在 [SetCat] 中工作。对象是广集 [SetC]，箭头是保持指定相等的函数，箭头相等
    是目标广集中的逐点相等。恒等和复合是通常的函数运算，附带保相等证明。

    对象 [BoolS] 的载体是 [bool]，指定相等是 [eq]。原生相等只是这个具体广集
    的选择，并非对其他对象的要求。复用 [BoolS] 不会启用其可选的代数结构。
    取反给出第一条箭头，保持这个原生相等的证明自动推断。随后的方程是
    [SetCat] 中的箭头相等。 *)

Program Definition negation_resp
  : Hom (Cat := SetCat) BoolS BoolS
  :=
  {|func := negb
  |}.

(** Negating twice is the identity arrow. This equality compares the output
    at each input; the proof checks the two Boolean values. *)

(** 取反两次是恒等箭头。相等逐点比较输出，证明检查两个布尔输入。 *)

Example negation_twice
  : negation_resp ∘ negation_resp ≈ id.
Proof. intros []; reflexivity. Qed.

(** ** 2. A functor turns a shape into a diagram

    [PairShape] has two objects, named [false] and [true], and only identity
    arrows. These names label the left and right positions of the diagram;
    they are not the Boolean elements inside the assigned objects.

    [⟨BoolS, BoolS⟩D] assigns [BoolS] to each position. It also sends every
    identity to an identity and respects composition: that is the functor
    structure, already supplied by [PairDiagram]. There is no arrow connecting
    the two positions, so this diagram asks for two independent observations.

    Another functor, [ConstF PairShape BoolS], assigns the same source object
    to both positions. It will be the domain of our natural transformation. *)

(** ** 2. 函子将形状变成图式

    [PairShape] 有两个对象，分别名为 [false] 和 [true]，只有恒等箭头。这些名字
    标记图式的左、右位置，并不是赋给这些位置的对象内部的布尔元素。

    [⟨BoolS, BoolS⟩D] 为每个位置赋予 [BoolS]，并将恒等送到恒等、保持复合；这
    就是 [PairDiagram] 已经提供的函子结构。两个位置之间没有箭头，因此这个图式
    要求两份独立的观察。

    另一个函子 [ConstF PairShape BoolS] 将同一个源对象赋给两个位置，它将成为
    自然变换的定义域。 *)

Definition BooleanDiagram
  : Functor PairShape SetCat
  := ⟨BoolS, BoolS⟩D.

(** The diagram preserves identities, as every functor must. *)

(** 与所有函子一样，这个图式保持恒等。 *)

Example boolean_diagram_id (j : @Ob PairShape)
  : fmap BooleanDiagram (@id j) ≈ id.
Proof. apply functor_id. Qed.

(** ** 3. A natural transformation supplies compatible observations

    A transformation [F ⇒ G] gives an arrow [F j → G j] at each position.
    For every shape arrow [a : Hom i j], naturality requires
    [α j ∘ fmap F a ≈ fmap G a ∘ α i]. Our shape is discrete, so these
    conditions follow from identity laws. For a shape with nonidentity
    arrows, naturality would impose additional commutative squares.

    Take identity at the left position and negation at the right. [PairCone]
    packages these components and their naturality. The resulting natural
    transformation is a cone, since its domain is a constant diagram:
    [BoolS ⇒Δ BooleanDiagram] abbreviates
    [ConstF PairShape BoolS ⇒ BooleanDiagram]. No new kind of arrow is needed. *)

(** ** 3. 自然变换提供相容的观察

    自然变换 [F ⇒ G] 为每个位置给出箭头 [F j → G j]。对于每条形状箭头
    [a : Hom i j]，自然性要求
    [α j ∘ fmap F a ≈ fmap G a ∘ α i]。本例的形状离散，因此这些条件由恒等律
    保证。若形状含有非恒等箭头，自然性就会额外要求相应的方块交换。

    在左位置取恒等，右位置取反。[PairCone] 将这些分量与自然性组织起来。
    由于定义域是常图式，这个自然变换就是锥：[BoolS ⇒Δ BooleanDiagram] 是
    [ConstF PairShape BoolS ⇒ BooleanDiagram] 的简写，无需引入另一种箭头。 *)

Definition BooleanCone
  : BoolS ⇒Δ BooleanDiagram
  := ⟨id, negation_resp⟩Cone.

(** Evaluating its components recovers the two observations. *)

(** 取出自然变换的分量，就恢复两份观察。 *)

Example boolean_cone_components (b : bool)
  : BooleanCone false b ≈S b ∧ BooleanCone true b ≈S negb b.
Proof. split; reflexivity. Qed.

(** ** 4. A product records both observations universally

    Explicitly enable the existing product structure on [SetCat]. The
    object [BoolS × BoolS] has ordered pairs as elements, componentwise
    equality, and two coordinate projections. Pairing forms the map
    [⟨id, negation_resp⟩], which sends [b] to [(b, negb b)].

    The product itself contains all four Boolean pairs. Our map reaches only
    [(false, true)] and [(true, false)]; it is one map into the product.
    What makes this object a product is its universal property for every
    source setoid [Q] and every pair of arrows [f, g]. The beta equations
    recover the observations, and uniqueness determines their pairing. *)

(** ** 4. 积以泛的方式记录两份观察

    显式启用 [SetCat] 已有的积结构。[BoolS × BoolS] 的元素是有序对，相等逐分量
    定义，两个坐标投影就是积投影。配对给出映射 [⟨id, negation_resp⟩]，将 [b]
    送到 [(b, negb b)]。

    积本身包含全部四个布尔对。本例的映射只到达 [(false, true)] 和
    [(true, false)]，它是一条指向积的映射。使这个对象成为积的是对每个源广集
    [Q] 和每对箭头 [f, g] 都成立的泛性质：β 方程恢复观察，唯一性确定其配对。 *)

Local Existing Instance SetCat_HasProduct.

(** The paired observations, with their concrete computation. *)

(** 配对后的观察及其具体计算。 *)

Definition BooleanPair
  : Hom (Cat := SetCat) BoolS (BoolS × BoolS)
  := ⟨id, negation_resp⟩.

(** Its value is the input paired with its negation. *)

(** 其值就是输入与输入取反组成的有序对。 *)

Example boolean_pair_value (b : bool)
  : BooleanPair b ≈S (b, negb b).
Proof. split; reflexivity. Qed.

(** Both projections recover the given arrows, for an arbitrary source. *)

(** 对于任意源，两个投影都恢复给定箭头。 *)

Example boolean_pair_β {Q : SetC} (f g : Hom (Cat := SetCat) Q BoolS)
  : π1 ∘ ⟨f,g⟩ ≈ f ∧ π2 ∘ ⟨f,g⟩ ≈ g.
Proof. split; [apply product_β1 | apply product_β2]. Qed.

(** The projection equations determine the arrow up to specified equality.
    In the diagram, B denotes [BoolS]. *)

(** 投影方程在指定相等意义下唯一确定箭头。图中的 B 表示 [BoolS]。 *)

Example boolean_pair_unique {Q : SetC}
    (f g : Hom (Cat := SetCat) Q BoolS) (h : Hom Q (BoolS × BoolS))
    (H1 : π1 ∘ h ≈ f) (H2 : π2 ∘ h ≈ g)
  : h ≈ ⟨f,g⟩.
Proof. apply product_pair_unique. split; assumption. Qed.

(** @lang both
%
\[
\begin{tikzcd}[column sep=large, row sep=large]
  & Q \arrow[ddl, bend right=25, "f"']
      \arrow[ddr, bend left=25, "g"]
      \arrow[d, dashed, "{\exists!\,\langle f,g\rangle}"] & \\
  & \mathbb B\times\mathbb B \arrow[dl, "\pi_1"]
      \arrow[dr, "\pi_2"'] & \\
  \mathbb B & & \mathbb B
\end{tikzcd}
\]
%
*)

(** ** 5. The same universal property makes this product a limit

    A limit of a diagram [D] is a cone [κ] such that every cone [μ] factors
    through it by a unique apex map [h]: [κ ∘Cone h ≈N μ]. For our discrete
    two-object shape, this equation is precisely the two projection equations
    above. Thus a binary product is a limit of a two-object discrete diagram.

    [ProductDiagramLimit] reuses this correspondence to select the product
    as the limit apex and its projections as the limiting cone. We explicitly
    enable this choice only for [BooleanDiagram]. For any cone [μ], its
    limit mediator is the pairing of its two components. *)

(** ** 5. 同一个泛性质使这个积成为极限

    图式 [D] 的极限是一个锥 [κ]，使每个锥 [μ] 都经唯一的顶点映射 [h] 分解，
    即 [κ ∘Cone h ≈N μ]。对于本例的两对象离散形状，这个方程恰好就是上面的
    两个投影方程。因此，二元积是两对象离散图式的极限。

    [ProductDiagramLimit] 复用这个对应，将积选为极限顶点、投影选为极限锥。
    我们仅为 [BooleanDiagram] 显式启用这项选择。对于任意锥 [μ]，它的极限中介
    就是两个分量的配对。 *)

Definition BooleanLimit
  : HasLimit SetCat BooleanDiagram
  := ProductDiagramLimit BooleanDiagram.

Local Existing Instance BooleanLimit.

(** The general limiting mediator recovers ordinary pairing. *)

(** 一般极限中介恢复通常的配对。 *)

Example boolean_limit_pair {Q : SetC} (μ : Q ⇒Δ BooleanDiagram)
  : lim⟨μ⟩ ≈ ⟨μ false, μ true⟩.
Proof.
  apply product_pair_unique. split. (* .unfold .all *)
  - exact (limit_β μ false).
  - exact (limit_β μ true).
Qed.

(** Our original cone therefore has exactly the earlier concrete map. *)

(** 因此，最初那个锥的中介正是先前的具体映射。 *)

Example boolean_limit_mediator
  : lim⟨BooleanCone⟩ ≈ BooleanPair.
Proof. apply boolean_limit_pair. Qed.

(** The chosen universal construction computes on both Boolean inputs. *)

(** 选定泛构造在两个布尔输入上都能直接计算。 *)

Example boolean_limit_values
  : lim⟨BooleanCone⟩ false ≈S (false, true)
    ∧ lim⟨BooleanCone⟩ true ≈S (true, false).
Proof. split; split; reflexivity. Qed.

(** The factorization equation uniquely determines a mediator of any cone. *)

(** 对于任意锥，分解方程唯一确定其中介。 *)

Example boolean_limit_unique {Q : SetC} (μ : Q ⇒Δ BooleanDiagram)
    (h : Hom Q (lim BooleanDiagram))
    (H : πlim[BooleanDiagram] ∘Cone h ≈N μ)
  : h ≈ lim⟨μ⟩.
Proof. apply limit_lift_unique. exact H. Qed.
