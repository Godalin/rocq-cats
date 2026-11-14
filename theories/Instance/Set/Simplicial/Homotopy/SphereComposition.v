From Cats Require Export
  Instance.Set.Simplicial.Homotopy.Sphere.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Composing Based Two-Spheres by a Tetrahedron

    In the simplex presentation of sphere composition, the two input faces
    are [d_3 w = x] and [d_1 w = y]; the zeroth face is constant and the
    second face is the output [z]. Thus composition fills the missing
    second face of a horn. Here we retain the tetrahedron itself and all
    four face equations. This definition neither selects fillers nor
    asserts that an arbitrary simplicial setoid has a group of classes.
    Compare the elementary homotopy in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.Sphere.TwoSphereHomotopy}
    {%[TwoSphereHomotopy]%}%: it has two constant faces instead of one. *)

(** * 通过四面体合成基点二维球面

    在球面合成的单形呈现中，两个输入面是 [d_3 w = x] 与 [d_1 w = y]；
    第零面为常值，第二面是输出 [z]。因此合成填充一个角缺少的第二面。
    这里保留四面体本身及全部四个面方程。此定义既不选择填充，也不声称
    任意单纯广集的类构成群。可对照
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.Sphere.TwoSphereHomotopy}
    {%[TwoSphereHomotopy]%}%：初等同伦有两个常值面，而非一个。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
x\in X_2 & w\in X_3 \arrow[l,"d_3"']
  \arrow[r,"d_1"] \arrow[d,"d_2"'] & y\in X_2 \\
& z\in X_2 &
\end{tikzcd}
\qquad $d_0w=b_2.$
\end{center}%
*)

(** ** A Witness with Three Sphere Faces

    Fix independent simplex carrier/equality sizes and a base vertex.
    Replacement compares triangles in their original specified equality;
    it never compares their boundary witnesses. *)

(** ** 带三个球面面的见证

    固定独立的单形载体／相等大小及一个基点。代表替换按三角形原有指定相等
    比较，不比较边界见证。 *)

Section SphereComposition.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** An actual tetrahedron witnessing the ordered composite [x], then [y]. *)

(** 见证先 [x] 后 [y] 的有序合成的一份实际四面体。 *)

Definition TwoSphereComposite (x y z : TwoSphereS X b)
  : Type
  := ∃ w : X 3,
      (d[X; 2; fin_first] w ≈S simplex_constant X b 2) ∧
      (d[X; 2; fin_first⁺] w ≈S y.1) ∧
      (d[X; 2; fin_first⁺⁺] w ≈S z.1) ∧
      (d[X; 2; fin_first⁺⁺⁺] w ≈S x.1).

(** Changing any of the three representatives retains the same filler. *)

(** 更换三个代表中的任意一个，均保留相同填充。 *)

Definition TwoSphereCompositeChangeEndpoints
    {x y z x' y' z' : TwoSphereS X b}
    (H : TwoSphereComposite x y z)
    (E : x ≈S x') (F : y ≈S y') (G : z ≈S z')
  : TwoSphereComposite x' y' z'.
Proof.
  destruct H as [w [H0 [H1 [H2 H3]]]].
  exists w. split; [exact H0 |]. split; [| split].
  - transitivity y.1; assumption.
  - transitivity z.1; assumption.
  - transitivity x.1; assumption.
Defined.

(** Composition witnesses respect native sphere equality in every slot. *)

(** 合成见证在每个位置保持球面的原生相等。 *)

Global Instance TwoSphereComposite_proper
  : Proper ([≈S] ==> [≈S] ==> [≈S] ==> iffT) TwoSphereComposite.
Proof.
  intros x x' E y y' F z z' G. split; intros H.
  - exact (TwoSphereCompositeChangeEndpoints H E F G).
  - exact (TwoSphereCompositeChangeEndpoints H
      (symmetry E) (symmetry F) (symmetry G)).
Defined.

End SphereComposition.
