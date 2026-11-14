From Cats Require Export
  Instance.Set.Simplicial.Cocycle.SphereCylinder
  Instance.Set.Simplicial.Homotopy.OneReduced.
From Cats Require Import
  Cat.Natural
  Instance.Set.Yoneda.

Local Open Scope nat_scope.

(** * A Sphere Coefficient Invariant of Homotopic Maps

    The preceding comparison required a relative cylinder. A homotopy of
    arbitrary maps into the cocycle model supplies such a cylinder on
    every source sphere: all target edges agree with the constant edge,
    so even its basepoint trajectory is constant in specified equality.
    Apply the general reduction in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.OneReduced.OneReducedSphereCylinder}
    {%[OneReducedSphereCylinder]%}%, then the three-tetrahedron comparison.

    We also retain finite chains of homotopies, reversals and natural
    equalities between maps with this fixed codomain. The existing
    [GeneratedS] descent theorem extends coefficient evaluation to these
    chains without a second induction or a quotient axiom. This is a
    concrete invariant, not a general definition of Kan homotopy groups
    or a category obtained by inverting weak equivalences. *)

(** * 同伦映射的球面系数不变量

    前章的比较要求相对柱。到 cocycle 模型的任意映射同伦，在每个源球面上
    都提供这种柱：全部目标边均与常值边相等，因此连基点轨迹也按指定相等
    为常值。先应用一般约化
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.OneReduced.OneReducedSphereCylinder}
    {%[OneReducedSphereCylinder]%}%，再应用三份四面体的比较。

    还保留固定此余域的映射之间有限次同伦、反向及自然相等的链。既有
    [GeneratedS] 下降定理将系数求值推广到这些链，无须第二次归纳或商公理。
    这是具体不变量，不是一般 Kan 同伦群的定义，也不是将弱等价取逆所得的
    范畴。 *)

(** ** The Constant Edge of the Cocycle Model

    Fix only a coefficient monoid and independent ambient sizes. The
    degree-one uniqueness theorem provides the entire reduction law. *)

(** ** Cocycle 模型的常值边

    只固定系数幺半群及独立环境大小。一维唯一性定理提供完整约化定律。 *)

Section CocycleHomotopies.
Universes u p.
Context {M : SetC} `{HM : !Monoid M}.

Let Z
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Z²(M).

(** Every edge agrees with the constant edge at the unit vertex. *)

(** 每条边均与单位顶点处的常值边相等。 *)

Lemma cocycle_edge_constant (z : Z 1)
  : z ≈S simplex_constant Z (two_cocycle_simplex_unit 0) 1.
Proof. apply two_cocycle_one_unique. Defined.

(** Restrict a full homotopy to a source sphere, retaining its actual
    cylinder map and the whole relative boundary. *)

(** 将完整同伦限制到源球面，保留实际柱映射及整个相对边界。 *)

Definition CocycleHomotopySphereCylinder
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Z}
    (H : SimplicialHomotopy f g) (b : X 0) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Z (two_cocycle_simplex_unit 0)
      (one_reduced_sphere_resp Z (two_cocycle_simplex_unit 0)
        cocycle_edge_constant (f 2 x.1))
      (one_reduced_sphere_resp Z (two_cocycle_simplex_unit 0)
        cocycle_edge_constant (g 2 x.1))
  := OneReducedSphereCylinder Z (two_cocycle_simplex_unit 0)
      cocycle_edge_constant H b x.

(** Homotopic maps give equal coefficients on every based source sphere.
    The maps need not be declared based; target edge uniqueness controls
    the trajectory of its base vertex. *)

(** 同伦映射在每个源基点球面上给出相等系数。不要求映射预先声明为基点映射；
    目标边唯一性控制其基点顶点的轨迹。 *)

Lemma cocycle_homotopy_sphere_value
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Z}
    (H : SimplicialHomotopy f g) (b : X 0) (x : TwoSphereS X b)
  : two_cocycle_triangle_value_resp (f 2 x.1) ≈S
      two_cocycle_triangle_value_resp (g 2 x.1).
Proof.
  exact (cocycle_two_sphere_cylinder_value _ _
    (CocycleHomotopySphereCylinder H b x)).
Defined.

(** Keep the actual maps as representatives. Generated equality retains
    all intermediate maps, full homotopies and natural-equality witnesses;
    its size may exceed the original simplex equality bound. *)

(** 保留实际映射作为代表。生成相等保留全部中间映射、完整同伦及自然相等见证；
    其大小可以超过原有单形相等界。 *)

Definition CocycleHomotopyMapS
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  : SetC
  := GeneratedS (Nat_SetS X Z)
      (λ f g, ((f ≈N g) + SimplicialHomotopy f g)%type).

(** Natural equality gives a generator of the map relation. *)

(** 自然相等给出映射关系的生成元。 *)

Definition cocycle_homotopy_map_eq
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Z}
    (E : f ≈N g)
  : (f : CocycleHomotopyMapS X) ≈S g
  := closure_step (inl E).

(** A whole directed homotopy gives a retained generator. *)

(** 整份有向同伦给出一个保留生成元。 *)

Definition cocycle_homotopy_map_step
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Z}
    (H : SimplicialHomotopy f g)
  : (f : CocycleHomotopyMapS X) ≈S g
  := closure_step (inr H).

(** Evaluate a map on a fixed source sphere and decode its triangle. *)

(** 将映射作用于固定源球面，再读取其三角形。 *)

Program Definition cocycle_sphere_evaluation_resp
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (b : X 0) (x : TwoSphereS X b)
  : Nat_SetS X Z →r M
  :=
  {|func f := two_cocycle_triangle_value_resp (f 2 x.1)
  |}.
Next Obligation.
  intros f g E.
  exact (@func_proper _ _ (two_cocycle_triangle_value_resp : Z 2 →r M)
    _ _ (E 2 x.1)).
Defined.

(** Descent proves invariance under arbitrary finite homotopy chains,
    their reversals and natural equality changes, using existing general
    generated-setoid theory. The evaluation map stays computational. *)

(** 由既有一般生成广集理论下降，得到任意有限同伦链、其反向及自然相等替换
    下的不变性。求值映射仍为可计算数据。 *)

Definition cocycle_homotopy_evaluation_resp
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}
    (b : X 0) (x : TwoSphereS X b)
  : CocycleHomotopyMapS X →r M.
Proof.
  refine (generated_resp (cocycle_sphere_evaluation_resp b x) _).
  intros f g [E | H].
  - exact (@func_proper _ _ (cocycle_sphere_evaluation_resp b x) _ _ E).
  - exact (cocycle_homotopy_sphere_value H b x).
Defined.

End CocycleHomotopies.
