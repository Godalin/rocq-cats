From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereHorn.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Chosen Sphere Composites and Inverse Candidates

    The preceding chapter glues arbitrary based triangles into an actual
    tetrahedron horn and reads its missing sphere. Here the face table
    specifies the roles in
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereComposition.TwoSphereComposite}
    {%[TwoSphereComposite]%}%: face zero is constant, face three is the
    first input, face one is the second input, and face two is the output.

    Filling the missing second face constructs a composite. Leaving face
    one or face three missing instead gives right or left inverse candidates
    with constant output. Each candidate retains an actual tetrahedron and
    its four face equations. No respectfulness of selected fillers, equality
    of their choices, associativity or group structure on classes is asserted. *)

(** * 选定球面合成与逆候选

    前章将任意基点三角形粘成实际四面体 horn，并读出其缺失球面。此处用面表
    指定 %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereComposition.TwoSphereComposite}
    {%[TwoSphereComposite]%}% 的角色：第零面为常值，第三面为第一个输入，
    第一面为第二个输入，第二面为输出。

    填充缺失的第二面得到合成；改为缺少第一面或第三面，则得到输出为常值的
    右逆或左逆候选。每个候选均保留实际四面体及四个面方程。不预设选定填充
    保相等、不同选择相等、结合律或类上的群结构。 *)

(** The dashed arrows are the requested sphere faces, not equations
    already true of the inputs. All three constructions use the same
    actual horn gluing; only the missing index and supplied faces change. *)

(** 虚线箭头表示所寻找的球面面，并非输入已满足的方程。三个构造使用同一个
    实际 horn 粘合，只更换缺失索引及给定面。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
x & w \arrow[l,"{d_3}"'] \arrow[r,"{d_1}"]
  \arrow[d,dashed,"{d_2}"'] & y \\
& z &
\end{tikzcd}
\qquad $d_0w=b_2.$
\end{center}%
*)

(** ** Face Tables at One Base Vertex

    Fix independent ambient sizes and a base vertex. Four sphere values
    describe a horn for any missing index; the omitted value is a dummy
    and does not constrain the filler. *)

(** ** 一个基点顶点处的面表

    固定独立环境大小及基点顶点。四个球面值对任意缺失索引描述一个 horn；
    缺失处的值只是占位，不对填充增加约束。 *)

Section SphereKanFaces.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Supply the three nonconstant roles; the zeroth face is always constant. *)

(** 给出三个可非平凡角色；第零面始终为常值。 *)

Definition sphere_composition_faces (x y z : TwoSphereS X b) (j : Ordinal 3)
  : TwoSphereS X b
  := match fin_rank j with
  | 1 => y
  | 2 => z
  | 3 => x
  | _ => two_sphere_base X b
  end.

(** A filler with face two missing retains precisely a composite witness. *)

(** 缺失第二面的填充恰好保留一份合成见证。 *)

Definition SphereHornComposite (x y : TwoSphereS X b) (w : X 3)
    (H : is_horn_filler (SphereTetrahedronHornN X b fin_first⁺⁺
      (sphere_composition_faces x y (two_sphere_base X b))) w)
  : TwoSphereComposite X b x y
      (sphere_tetrahedron_missing_sphere X b fin_first⁺⁺
        (sphere_composition_faces x y (two_sphere_base X b)) w H).
Proof.
  exists w. split; [| split; [| split]].
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first
      ltac:(intros E; discriminate E)).
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first⁺
      ltac:(intros E; discriminate E)).
  - reflexivity.
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first⁺⁺⁺
      ltac:(intros E; discriminate E)).
Defined.

(** A filler with face one missing supplies a right inverse candidate. *)

(** 缺失第一面的填充提供一份右逆候选。 *)

Definition SphereHornRightInverse (x : TwoSphereS X b) (w : X 3)
    (H : is_horn_filler (SphereTetrahedronHornN X b fin_first⁺
      (sphere_composition_faces x (two_sphere_base X b)
        (two_sphere_base X b))) w)
  : TwoSphereComposite X b x
      (sphere_tetrahedron_missing_sphere X b fin_first⁺
        (sphere_composition_faces x (two_sphere_base X b)
          (two_sphere_base X b)) w H) (two_sphere_base X b).
Proof.
  exists w. split; [| split; [| split]].
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first
      ltac:(intros E; discriminate E)).
  - reflexivity.
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first⁺⁺
      ltac:(intros E; discriminate E)).
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first⁺⁺⁺
      ltac:(intros E; discriminate E)).
Defined.

(** A filler with face three missing supplies a left inverse candidate. *)

(** 缺失第三面的填充提供一份左逆候选。 *)

Definition SphereHornLeftInverse (x : TwoSphereS X b) (w : X 3)
    (H : is_horn_filler (SphereTetrahedronHornN X b fin_first⁺⁺⁺
      (sphere_composition_faces (two_sphere_base X b) x
        (two_sphere_base X b))) w)
  : TwoSphereComposite X b
      (sphere_tetrahedron_missing_sphere X b fin_first⁺⁺⁺
        (sphere_composition_faces (two_sphere_base X b) x
          (two_sphere_base X b)) w H) x (two_sphere_base X b).
Proof.
  exists w. split; [| split; [| split]].
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first
      ltac:(intros E; discriminate E)).
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first⁺
      ltac:(intros E; discriminate E)).
  - exact (sphere_tetrahedron_filler_face X b _ _ w H fin_first⁺⁺
      ltac:(intros E; discriminate E)).
  - reflexivity.
Defined.

End SphereKanFaces.

(** ** Selecting Only the Required Horn Fillers

    Fix a simplicial setoid and a vertex. Each construction asks only for
    its own three-dimensional horn choice. A locally supplied Kan structure
    provides these choices through its existing inherited field; importing
    this module does not register a chosen structure. *)

(** ** 仅选择所需 Horn 的填充

    固定单纯广集及顶点。每个构造只要求其自身三维 horn 的选择；局部给定的
    Kan 结构经既有继承字段提供这些选择。导入本模块不会注册选定结构。 *)

Section ChosenSphereKanOperations.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Select a composite together with its actual witnessing tetrahedron. *)

(** 选择合成，并保留实际见证四面体。 *)

Definition SphereKanComposite `{HX : !HasHornFillers X 3 fin_first⁺⁺}
    (x y : TwoSphereS X b)
  : ∃ z : TwoSphereS X b, TwoSphereComposite X b x y z.
Proof.
  pose (a := sphere_composition_faces X b x y (two_sphere_base X b)).
  pose (w := SphereTetrahedronFill X b fin_first⁺⁺ a).
  exists (sphere_tetrahedron_missing_sphere X b _ a w.1 w.2).
  exact (SphereHornComposite X b x y w.1 w.2).
Defined.

(** Select a candidate composing on the right to the constant sphere. *)

(** 选择一个在右侧合成得到常值球面的候选。 *)

Definition SphereKanRightInverse `{HX : !HasHornFillers X 3 fin_first⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b x y (two_sphere_base X b).
Proof.
  pose (a := sphere_composition_faces X b x
    (two_sphere_base X b) (two_sphere_base X b)).
  pose (w := SphereTetrahedronFill X b fin_first⁺ a).
  exists (sphere_tetrahedron_missing_sphere X b _ a w.1 w.2).
  exact (SphereHornRightInverse X b x w.1 w.2).
Defined.

(** Select a candidate composing on the left to the constant sphere.
    This is an independent choice; equality with the right candidate is
    a later theorem, not a stored assumption. *)

(** 选择一个在左侧合成得到常值球面的候选。这是独立选择；它与右候选的相等
    应为后续定理，而非保存的假设。 *)

Definition SphereKanLeftInverse `{HX : !HasHornFillers X 3 fin_first⁺⁺⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b y x (two_sphere_base X b).
Proof.
  pose (a := sphere_composition_faces X b (two_sphere_base X b)
    x (two_sphere_base X b)).
  pose (w := SphereTetrahedronFill X b fin_first⁺⁺⁺ a).
  exists (sphere_tetrahedron_missing_sphere X b _ a w.1 w.2).
  exact (SphereHornLeftInverse X b x w.1 w.2).
Defined.

End ChosenSphereKanOperations.
