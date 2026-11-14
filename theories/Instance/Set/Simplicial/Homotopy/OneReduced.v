From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereCylinder.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

Local Open Scope nat_scope.

(** * Homotopies into a Target with Only the Constant Edge

    A general simplicial homotopy may move the basepoint. Suppose instead
    that every edge of the target agrees with the constant edge at a fixed
    vertex. Its basepoint trajectory then agrees with that edge, and all
    restrictions of the trajectory agree with constant simplices. This is
    the precise reduction used here; we do not choose a Kan structure or
    assume that arbitrary based homotopies fix their basepoint.

    Together with the full boundary lemma
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two sphere boundary constant}
    {%[two_sphere_boundary_constant]%}%, this turns the restriction of any
    homotopy to a source sphere into an actual relative sphere cylinder. *)

(** * 到只有常值边的目标的同伦

    一般单纯同伦可以移动基点。若目标的每条边都与固定顶点处的常值边相等，
    则基点轨迹与该常值边相等，其全部限制也与常值单形相等。这是此处使用的
    确切约化条件；不选择 Kan 结构，也不预设任意基点同伦均固定基点。

    结合完整边界引理
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereCylinder.two sphere boundary constant}
    {%[two_sphere_boundary_constant]%}%，即可将任意同伦在源球面上的限制
    转为实际相对球面柱。 *)

(** The square is naturality along a time operator τ from degree n to
    degree one. Its upper-right value is a single target edge; the explicit
    edge law makes that edge constant. The lower-right value is therefore
    constant too, including every time simplex on the sphere boundary. *)

(** 此方块是沿从 n 维到一维的时间算子 τ 的自然性。右上角的值是一条目标边；
    显式边定律使该边为常值。因此右下角的值也为常值，涵盖球面边界上的每个
    时间单形。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
(\operatorname{const}_1 b,\operatorname{id}_{[1]})
  \arrow[r,mapsto,"{H_1}"] \arrow[d,mapsto,"{\tau^*}"'] &
H_1(\operatorname{const}_1 b,\operatorname{id}_{[1]})
  \arrow[d,mapsto,"{\tau^*}"] \\
(\operatorname{const}_n b,\tau) \arrow[r,mapsto,"{H_n}"'] &
H_n(\operatorname{const}_n b,\tau)
\end{tikzcd}
\end{center}%
*)

(** ** Constant Trajectories and Image Spheres

    Fix independent ambient sizes, a target vertex and the explicit law
    that every target edge is its constant edge. No record or equality of
    edge witnesses is compared, and no global model structure is selected. *)

(** ** 常值轨迹与像球面

    固定独立环境大小、目标顶点及每条目标边均等于其常值边的显式定律。
    不比较边见证的记录或相等，也不全局选择模型结构。 *)

Section OneReducedHomotopies.
Universes u p.
Context (Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (c : Y 0)
    (E1 : ∀ z : Y 1, z ≈S simplex_constant Y c 1).

(** Every target triangle is a based sphere, with its original triangle
    retained as data. *)

(** 每个目标三角形均为基点球面，原三角形作为数据保留。 *)

Program Definition one_reduced_sphere_resp
  : Y 2 →r TwoSphereS Y c
  :=
  {|func z := (z; λ i, E1 (d[Y; 1; i] z))
  |}.
Next Obligation. intros x y H. exact H. Defined.

(** Naturality along time expresses every basepoint trajectory simplex
    as a restriction of the single trajectory edge. *)

(** 沿时间的自然性将每个基点轨迹单形表示为同一条轨迹边的限制。 *)

Lemma one_reduced_homotopy_trace
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Y}
    (H : SimplicialHomotopy f g) (b : X 0) (n : nat)
    (t : (Δ[1] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : homotopy_map H n (simplex_constant X b n, t) ≈S
      simplex_constant Y c n.
Proof.
  pose (τ := lower t).
  pose (z := (simplex_constant X b 1, simplex_generic 1)
    : SimplicialCylinderF X 1).
  transitivity (homotopy_map H n ((SimplicialCylinderF X)[τ]Δ z)).
  - apply func_proper. split.
    + symmetry. exact (simplex_constant_restrict X b τ).
    + refine {|lower := _
              |}. symmetry.
      change (@HomEq Δ n 1%nat (id ∘ τ) τ).
      apply comp_id_l.
  - transitivity (Y[τ]Δ (homotopy_map H 1 z)).
    + exact (simplex_restrict_natural (homotopy_map H) τ z).
    + transitivity (Y[τ]Δ (simplex_constant Y c 1)).
      * apply func_proper. apply E1.
      * apply simplex_constant_restrict.
Defined.

(** Restrict a whole homotopy to a source sphere. The relative boundary
    follows from its constant spatial boundary and the constant trajectory
    just proved. The stored map is the actual precomposed homotopy. *)

(** 将整个同伦限制到源球面。相对边界来自其常值空间边界及刚证明的常值轨迹。
    保存的映射就是实际预复合同伦。 *)

Definition OneReducedSphereCylinder
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {f g : X ⇒ Y}
    (H : SimplicialHomotopy f g) (b : X 0) (x : TwoSphereS X b)
  : TwoSphereCylinderHomotopy Y c
      (one_reduced_sphere_resp (f 2 x.1))
      (one_reduced_sphere_resp (g 2 x.1)).
Proof.
  assert (Ef : (f ∘Nv ⟦x.1⟧Δ[X; 2]) ≈N ⟦f 2 x.1⟧Δ[Y; 2]).
  { intros n [θ]. exact (simplex_restrict_natural f θ x.1). }
  assert (Eg : (g ∘Nv ⟦x.1⟧Δ[X; 2]) ≈N ⟦g 2 x.1⟧Δ[Y; 2]).
  { intros n [θ]. exact (simplex_restrict_natural g θ x.1). }
  exists (HomotopyChangeEndpoints
    (SimplicialPreHomotopy H ⟦x.1⟧Δ[X; 2]) Ef Eg).
  intros n a t.
  change (homotopy_map H n (X[(lower a).1]Δ x.1, t) ≈S
    simplex_constant Y c n).
  transitivity (homotopy_map H n (simplex_constant X b n, t)).
  - apply func_proper. split.
    + apply two_sphere_boundary_constant.
    + reflexivity.
  - exact (one_reduced_homotopy_trace H b n t).
Defined.

End OneReducedHomotopies.
