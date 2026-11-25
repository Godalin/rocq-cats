From Cats Require Import
  Instance.Set.Simplicial.FaceGluing
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Nonconstant Four-Dimensional Horn and Degenerate Intersections

    Use the standard four-simplex, whose vertices stay distinct. Inspect
    the actual descended values, including a common factor of degree five;
    no higher-dimensional filler is selected. *)

(** * 非常值四维 Horn 与退化交叠

    使用顶点保持不同的标准四维单形，读取实际下降值，包括一个五维共同因子；
    不选择更高维填充。 *)

Definition T
  : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Δ[4].

Definition actual_faces (j : Ordinal 4)
  : T 3
  := d[T; 3; j] (simplex_generic 4).

Definition actual_horn
  : HornS T 4 fin_first⁺⁺
  := HornFacesN T 2 fin_first⁺⁺ actual_faces
      (λ j k _ _ E, simplex_faces_pairwise T (simplex_generic 4) j k E).

(** Read the four ordered vertices of a tetrahedron. *)

(** 读取四面体的四个有序顶点。 *)

Definition tetrahedron_ranks (x : T 3)
  : nat * nat * nat * nat
  := (fin_rank (lower x fin_first), fin_rank (lower x fin_first⁺),
      fin_rank (lower x fin_first⁺⁺), fin_rank (lower x fin_first⁺⁺⁺)).

(** Each of the four retained tetrahedra computes with its own omission. *)

(** 四个保留四面体分别按自身的省略位置计算。 *)

Example retained_faces_compute
  : (tetrahedron_ranks (face[fin_first⁺⁺; fin_first;
        ltac:(intros E; discriminate E)] actual_horn),
     tetrahedron_ranks (face[fin_first⁺⁺; fin_first⁺;
        ltac:(intros E; discriminate E)] actual_horn),
     tetrahedron_ranks (face[fin_first⁺⁺; fin_first⁺⁺⁺;
        ltac:(intros E; discriminate E)] actual_horn),
     tetrahedron_ranks (face[fin_first⁺⁺; fin_first⁺⁺⁺⁺;
        ltac:(intros E; discriminate E)] actual_horn))
      = ((1, 2, 3, 4), (0, 2, 3, 4), (0, 1, 2, 4), (0, 1, 2, 3)).
Proof. vm_compute. reflexivity. Defined.

(** The intersection of faces 1 and 4 is triangle 023. Repeat its positions
    with a degree-five map rather than testing just the generic triangle. *)

(** 面 1 与面 4 交于三角形 023；用五维映射重复其位置，而非仅检查生成三角形。 *)

Definition repeated_triangle
  : (@Hom Δ) 5 2
  := σ[2; fin_first] ∘ σ[3; fin_first⁺⁺] ∘ σ[4; fin_first⁺⁺⁺⁺].

Definition through_face_one
  : (@Hom Δ) 5 3
  := δ[2; fin_first⁺⁺⁺] ∘ repeated_triangle.

Definition through_face_four
  : (@Hom Δ) 5 3
  := δ[2; fin_first⁺] ∘ repeated_triangle.

(** The two factorizations give the same actual shape map. *)

(** 两个分解给出相同的实际形状映射。 *)

Lemma repeated_common_factor
  : δ[3; fin_first⁺] ∘ through_face_one ≈
      δ[3; fin_first⁺⁺⁺⁺] ∘ through_face_four.
Proof.
  apply (snd (simplex_eq_iff _ _)).
  intros [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; reflexivity.
Defined.

(** The extracted mediator retains its vertex computation. *)

(** 提取的中介保留其顶点计算。 *)

Definition repeated_mediator
  : (@Hom Δ) 5 2
  := (CofaceIntersectionFactor fin_first⁺ fin_first⁺⁺⁺⁺
      ltac:(intros E; discriminate E)
      through_face_one through_face_four repeated_common_factor).1.

Example mediator_computes
  : (fin_rank (repeated_mediator fin_first),
     fin_rank (repeated_mediator fin_first⁺),
     fin_rank (repeated_mediator fin_first⁺⁺),
     fin_rank (repeated_mediator fin_first⁺⁺⁺),
     fin_rank (repeated_mediator fin_first⁺⁺⁺⁺),
     fin_rank (repeated_mediator fin_first⁺⁺⁺⁺⁺))
      = (0, 0, 1, 1, 2, 2).
Proof. vm_compute. reflexivity. Defined.

(** Evaluate the whole horn on both retained sieve factorizations. *)

(** 在两个保留筛分解上求整个 horn 的值。 *)

Program Definition from_face_one
  : Λ[4; fin_first⁺⁺] 5
  :=
  {|lower := (δ[3; fin_first⁺] ∘ through_face_one; _)
  |}.
Next Obligation.
  pose (J := (ltac:(exists (fin_first⁺ : Ordinal 4);
    intros E; discriminate E) : ∃ j : Ordinal 4, ¬ j = fin_first⁺⁺)).
  exists J, through_face_one.
  reflexivity.
Defined.

Program Definition from_face_four
  : Λ[4; fin_first⁺⁺] 5
  :=
  {|lower := (δ[3; fin_first⁺⁺⁺⁺] ∘ through_face_four; _)
  |}.
Next Obligation.
  pose (J := (ltac:(exists (fin_first⁺⁺⁺⁺ : Ordinal 4);
    intros E; discriminate E) : ∃ j : Ordinal 4, ¬ j = fin_first⁺⁺)).
  exists J, through_face_four.
  reflexivity.
Defined.

Definition ranks_six (x : T 5)
  : nat * nat * nat * nat * nat * nat
  := (fin_rank (lower x fin_first), fin_rank (lower x fin_first⁺),
      fin_rank (lower x fin_first⁺⁺), fin_rank (lower x fin_first⁺⁺⁺),
      fin_rank (lower x fin_first⁺⁺⁺⁺), fin_rank (lower x fin_first⁺⁺⁺⁺⁺)).

Example repeated_overlap_computes
  : (ranks_six (actual_horn 5 from_face_one),
     ranks_six (actual_horn 5 from_face_four))
      = ((0, 0, 2, 2, 3, 3), (0, 0, 2, 2, 3, 3)).
Proof. vm_compute. reflexivity. Defined.

(** Importing gluing does not choose fillers, even for standard simplices. *)

(** 导入粘合不为标准单形隐式选取填充。 *)

Fail Definition unchosen_Kan
  : HasKanFillers T
  := _.

Fail Definition unchosen_four_horn
  : HasHornFillers T 4 fin_first⁺⁺
  := _.
