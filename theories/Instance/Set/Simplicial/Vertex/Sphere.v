From Cats Require Export
  Instance.Set.Simplicial.Homotopy.Sphere
  Instance.Set.Simplicial.Vertex.Sieve.
From Cats Require Import
  Instance.Set.Simplicial.Matching.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Ordinary Nerves Have Only One Based Two-Sphere

    A triangle in an ordinary category nerve is determined by its edges
    and vertices. Thus fixing all three edges to the constant edge leaves
    just the constant sphere, already in specified equality. This is
    stronger than identifying their generated homotopy classes and does
    not require the category to be a groupoid.

    We reuse the general sieve reflection theorem: vertices and edges of
    a triangle lie in its boundary. No separate reconstruction of nerve
    records or equality of their proof fields is needed. *)

(** * 普通 Nerve 只有一个基点二维球面

    普通范畴 nerve 的三角形由其边和顶点确定。因此，将三条边固定为常值边
    后，只剩一个常值球面，且已在指定相等下唯一。这比识别其生成同伦类更强，
    也不要求该范畴为群胚。

    复用一般筛反映定理：三角形的顶点和边都属于其边界。不另行重构 nerve
    记录，也不要求其中证明字段相等。 *)

(** ** Reflecting Triangle Equality

    Fix an object presentation and independent ambient sizes. Finite
    ordinal avoidance gives retained boundary witnesses; general descent
    reflection then compares the underlying triangles. *)

(** ** 反映三角形相等

    固定对象呈现及独立环境大小。有限序数避点给出保留的边界见证，再由一般
    下降反映比较底层三角形。 *)

Section NerveSpheres.
Universes u p.
Context {A : SetC} {C : Cat} (T : Fct (EqGpd A) C).

Let N
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Nᵥ(T).

(** Three equal corresponding faces force equality of whole triangles. *)

(** 三个对应面相等迫使整个三角形相等。 *)

Definition vertex_triangle_faces_reflect (x y : N 2)
    (H : ∀ i : Ordinal 2, d[N; 1; i] x ≈S d[N; 1; i] y)
  : x ≈S y.
Proof.
  assert (V : ∀ f : (@Hom Δ) 0 2, f ∈Sv BoundarySieve 2).
  { intros f. destruct (@fin_avoid_pair 0 (f fin_first) (f fin_first))
      as [j [Hj _]].
    apply (boundary_member_of_omission j f).
    intros [[] | []] E. apply Hj. symmetry. exact E. }
  assert (E : ∀ f : (@Hom Δ) 1 2, f ∈Sv BoundarySieve 2).
  { intros f. destruct (@fin_avoid_pair 0 (f fin_first) (f (fin_first⁺)))
      as [j [H0 H1]].
    apply (boundary_member_of_omission j f).
    intros [[] | [[] | []]] Q; [apply H0 | apply H1]; symmetry; exact Q. }
  apply (vertex_sieve_reflects T (BoundarySieve 2) V E x y).
  apply (snd (boundary_map_eq_iff _ _)). intros i. exact (H i).
Defined.

(** All based two-spheres agree, even before passing to homotopy classes. *)

(** 所有基点二维球面在转到同伦类之前就已相等。 *)

Lemma vertex_two_sphere_unique (b : N 0) (x y : TwoSphereS N b)
  : x ≈S y.
Proof.
  apply vertex_triangle_faces_reflect. intros i.
  transitivity (simplex_constant N b 1); [exact (x.2 i) | symmetry; exact (y.2 i)].
Defined.

(** Consequently the generated sphere-class setoid has only one element
    in specified equality; the distinguished sphere supplies that element. *)

(** 因此，生成球面类广集按指定相等只有一个元素；指定常值球面提供该元素。 *)

Lemma vertex_two_sphere_class_unique (b : N 0)
    (x y : TwoSphereClassS N b)
  : x ≈S y.
Proof. apply two_sphere_class_eq. apply vertex_two_sphere_unique. Defined.

End NerveSpheres.
