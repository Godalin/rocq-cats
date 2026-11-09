(** * Category Nerves Are Determined in Dimension Two

    A simplex in a category nerve records ordered vertices and composable
    arrows. Edges specify the arrows; triangles assert their composition
    equations. In dimension at least three the boundary already contains
    all this information, so it determines a unique simplex. No arrow needs
    to be invertible. All equalities below use the specified setoid relation. *)

(** * 范畴 nerve 由二维数据确定

    范畴 nerve 的单形记录有序顶点及可复合箭头。边指定箭头，三角形断言其复合
    方程。至少三维时，边界已包含全部这些信息，因此唯一确定单形。无需任何箭头
    可逆。下文全部相等均使用指定广集关系。 *)

From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Chain
  Cat.Groupoid.Core
  Instance.Set.Simplicial.Vertex.Kan.

Local Open Scope nat_scope.

(** ** 1. A category with a noninvertible arrow

    The ordinal [Ord 1] has two objects and a single arrow from the first
    to the second, with no arrow back. Its object setoid uses native equality
    on these concrete finite positions. Equality acts by identity arrows;
    thin hom equality makes this action independent of equality witnesses. *)

(** ** 1. 含有不可逆箭头的范畴

    序数 [Ord 1] 有两个对象及从首对象到次对象的唯一箭头，没有反向箭头。其对象
    广集对这些具体有限位置使用原生相等。相等通过恒等箭头作用；薄 Hom 相等保证
    此作用不依赖相等见证。 *)

Program Definition OrderedObjects
  : Functor (EqGpd (FinS 2)) [Ord 1]
  :=
  {|F0 i := i
  ; F1 i j e := _
  |}.
Next Obligation.
  destruct e. exact (@Cats.Cat.Core.id [Ord 1] i).
Defined.
Next Obligation. intros f g H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** The forward arrow has no inverse, so this selected category is not
    a groupoid. This is a mathematical obstruction, not an instance search. *)

(** 正向箭头没有逆，因此此选定范畴不是群胚；这是数学上的障碍，而非实例搜索失败。 *)

Example ordered_not_groupoid
  : ¬ IsGroupoid (VertexCat OrderedObjects).
Proof.
  intros H.
  destruct (@groupoid_inv (VertexCat OrderedObjects) H
    fin_first (fin_next fin_first) tt).
Defined.

(** ** 2. Choose the general coskeletal structure

    The theorem [vertex_IsCoskeletal] only requires the object action.
    We enable its chosen structure locally. In particular, importing the
    theorem does not silently select a model structure. *)

(** ** 2. 选取一般余骨架结构

    定理 [vertex_IsCoskeletal] 仅要求对象作用。此处局部启用其选定结构；特别地，
    导入该定理不会隐式选择模型结构。 *)

Definition OrderedNerve
  : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(OrderedObjects).

Local Instance ordered_coskeletal
  : OrderedNerve ⦂ Cosk[2]
  := vertex_IsCoskeletal OrderedObjects.

(** A boundary in dimension [3 + n] has a chosen filler recovering the
    entire boundary map, including all its restrictions and overlaps. *)

(** [3 + n] 维边界具有选定填充，恢复整个边界映射及其全部限制与交叠。 *)

Example ordered_boundary_filling (n : nat)
    (b : BoundaryS OrderedNerve (S (S (S n))))
  : (fill∂[OrderedNerve; 2; n] b)↾∂[OrderedNerve; S (S (S n))] ≈S b.
Proof. exact (coskeletal_fill_β n b). Defined.

(** Uniqueness recovers any simplex from its boundary in specified
    equality; neither functor records nor proof fields are identified. *)

(** 唯一性按指定相等从边界恢复任意单形，不等同函子记录或证明字段。 *)

Example ordered_simplex_recovery (n : nat)
    (x : OrderedNerve (S (S (S n))))
  : fill∂[OrderedNerve; 2; n]
      (x↾∂[OrderedNerve; S (S (S n))]) ≈S x.
Proof. exact (coskeletal_fill_η n x). Defined.

(** ** 3. Coskeletality does not supply Kan filling

    The nerve–groupoid criterion shows that this nerve cannot have Kan
    fillers. Outer horns ask for division by arrows, which is stronger than
    the composition equations needed to fill higher boundaries. *)

(** ** 3. 余骨架性不提供 Kan 填充

    nerve–群胚刻画说明此 nerve 不可能具有 Kan 填充。外 horn 要求箭头的除法，
    这比填充高维边界所需的复合方程更强。 *)

Example ordered_not_kan
  : ¬ HasKanFillers OrderedNerve.
Proof.
  intros H. apply ordered_not_groupoid.
  exact (fst (vertex_kan_groupoid_iff OrderedObjects) H).
Defined.
