From Cats Require Export
  Instance.Set.Simplicial.Homotopy.SphereUnit.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Associativity from an Actual Four-Horn

    Let A compose x with y to s, B compose y with z to t, and C compose
    s with z to l. Place B, C and A at faces one, two and four of a
    four-simplex, with constant face zero. Their six intersections agree:
    they use the shared triangles z, y and s, and the constant boundaries.
    No equation compares the two bracketed outputs in advance.

    Descend these faces with the existing
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}% and fill the horn with face three missing. That
    missing tetrahedron composes x with t to the same output l. Compare
    it with any supplied composite D of x with t to r, using
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKanComparison.two_sphere_composite_output_eq}
    {%[two_sphere_composite_output_eq]%}%. This yields class equality
    between l and r and hence associativity of the actual selected product.

    Missing-face-three selection suffices for rebracketing; comparison
    additionally needs missing-face-two selection. A supplied filler
    needs no chosen structure at all. The diagram's dashed arrow reads
    the new composite E; its faces two and one are l and t. The class
    equality follows only after comparison.
    The next chapter's
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroup.TwoSphereClassGroup}
    {%[TwoSphereClassGroup]%}% assembles the stronger structures and
    inverse uniqueness using the existing algebra hierarchy. *)

(** * 从实际四维 Horn 得到结合律

    设 A 将 x 与 y 合成为 s，B 将 y 与 z 合成为 t，C 将 s 与 z 合成为 l。
    把 B、C、A 放在四维单形的第一、第二、第四面，第零面取常值。六个交叠由
    共同三角形 z、y、s 及常值边界给出，不预先等同两种括号方式的输出。

    用既有
    %\coqref{Cats.Instance.Set.Simplicial.FaceGluing.HornFacesN}
    {%[HornFacesN]%}% 下降这些面，并填充缺失第三面的 horn。缺失四面体将 x
    与 t 合成为同一个输出 l。再用
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereKanComparison.two_sphere_composite_output_eq}
    {%[two_sphere_composite_output_eq]%}% 与任意给定的 (x,t) 到 r 的合成 D
    比较，得到 l 与 r 的类相等，继而证明实际选定乘积的结合律。

    重括号仅需缺第三面的选择，比较另需缺第二面的选择。给定实际填充时完全
    无需选定结构。下图虚线读出新合成 E，其第二、第一面是 l、t；类相等在
    比较之后才得到。下一章的
    %\coqref{Cats.Instance.Set.Simplicial.Homotopy.SphereGroup.TwoSphereClassGroup}
    {%[TwoSphereClassGroup]%}% 复用既有代数层级，组装更强结构及逆唯一性。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
B & V \arrow[l,"d_1"'] \arrow[r,"d_2"] \arrow[d,dashed,"d_3"'] & C \\
& E \arrow[dl,"d_2"'] \arrow[dr,"d_1"] & \\
l && t
\end{tikzcd}
\qquad $d_0V=b_3,\ d_4V=A,\ d_0E=b_2,\ d_3E=x.$
\end{center}%
*)

(** ** Three Composite Tetrahedra on One Horn

    Fix independent simplex carrier/equality sizes and a base vertex.
    Three supplied composite witnesses determine the retained faces;
    face three is a dummy and imposes no equation on a filler. *)

(** ** 一个 Horn 上的三个合成四面体

    固定独立的单形载体／相等大小及基点。三份给定合成见证确定保留面，第三面
    是占位项，不对填充施加方程。 *)

Section AssociativityHorn.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

(** Retain B, C and A, in that order, at positions one, two and four. *)

(** 将 B、C、A 依次保留在第一、第二、第四位置。 *)

Definition sphere_associativity_faces (a bc sc : X 3) (j : Ordinal 4)
  : X 3
  := match fin_rank j with
  | 1 => bc
  | 2 => sc
  | 4 => a
  | _ => simplex_constant X b 3
  end.

(** The six intersections use only shared inputs/intermediate output,
    not an equality between the two bracketed results. *)

(** 六个交叠只使用共同输入及中间输出，不使用两种括号结果间的相等。 *)

Lemma sphere_associativity_faces_pairwise
    {x y z s t l : TwoSphereS X b}
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (j k : Ordinal 4) (Hj : ¬ j = fin_first⁺⁺⁺)
    (Hk : ¬ k = fin_first⁺⁺⁺) (E : ¬ j = k)
  : d[X; 2; coface_intersection_index j k E]
      (sphere_associativity_faces A.1 B.1 C.1 j) ≈S
      d[X; 2; coface_intersection_index k j (λ F, E (symmetry F))]
        (sphere_associativity_faces A.1 B.1 C.1 k).
Proof.
  destruct A as [a [A0 [A1 [A2 A3]]]],
    B as [bc [B0 [B1 [B2 B3]]]], C as [sc [C0 [C1 [C2 C3]]]].
  assert (A01 : d[X; 2; fin_first] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] bc).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact B0. }
  assert (A02 : d[X; 2; fin_first⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] sc).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact C0. }
  assert (A04 : d[X; 2; fin_first⁺⁺⁺] (simplex_constant X b 3) ≈S
    d[X; 2; fin_first] a).
  { transitivity (simplex_constant X b 2).
    - apply simplex_constant_restrict.
    - symmetry. exact A0. }
  assert (A12 : d[X; 2; fin_first⁺] bc ≈S d[X; 2; fin_first⁺] sc).
  { transitivity z.1; [exact B1 | symmetry; exact C1]. }
  assert (A14 : d[X; 2; fin_first⁺⁺⁺] bc ≈S d[X; 2; fin_first⁺] a).
  { transitivity y.1; [exact B3 | symmetry; exact A1]. }
  assert (A24 : d[X; 2; fin_first⁺⁺⁺] sc ≈S d[X; 2; fin_first⁺⁺] a).
  { transitivity s.1; [exact C3 | symmetry; exact A2]. }
  destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]],
    k as [[] | [[] | [[] | [[] | [[] | []]]]]];
    try solve [destruct (Hj eq_refl) | destruct (Hk eq_refl) |
      destruct (E eq_refl)].
  all: first [exact A01 | exact A02 | exact A04 | exact A12 |
    exact A14 | exact A24 | exact (symmetry A01) | exact (symmetry A02) |
    exact (symmetry A04) | exact (symmetry A12) | exact (symmetry A14) |
    exact (symmetry A24)].
Defined.

(** Pairwise descent gives the actual missing-face-three horn map. *)

(** 逐对下降给出实际缺第三面的 horn 映射。 *)

Definition SphereAssociativityHornN
    {x y z s t l : TwoSphereS X b}
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
  : HornS X 4 fin_first⁺⁺⁺
  := HornFacesN X 2 fin_first⁺⁺⁺
      (sphere_associativity_faces A.1 B.1 C.1)
      (sphere_associativity_faces_pairwise A B C).

(** An actual filler recovers each retained tetrahedron. *)

(** 实际填充恢复每个保留四面体。 *)

Lemma sphere_associativity_filler_face
    {x y z s t l : TwoSphereS X b}
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (V : X 4) (HV : is_horn_filler (SphereAssociativityHornN A B C) V)
    (j : Ordinal 4) (Hj : ¬ j = fin_first⁺⁺⁺)
  : d[X; 3; j] V ≈S sphere_associativity_faces A.1 B.1 C.1 j.
Proof.
  transitivity (face[fin_first⁺⁺⁺; j; Hj] (SphereAssociativityHornN A B C)).
  - exact (fst (horn_filler_faces_iff _ V) HV j Hj).
  - apply horn_faces_β.
Defined.

(** The missing face composes x with t, retaining the original output l.
    This is a transparent construction from a supplied actual filler. *)

(** 缺失面将 x 与 t 合成，保留原输出 l；这是从给定实际填充出发的透明构造。 *)

Definition SphereCompositeReassociateOfFiller
    {x y z s t l : TwoSphereS X b}
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (V : X 4) (HV : is_horn_filler (SphereAssociativityHornN A B C) V)
  : TwoSphereComposite X b x t l.
Proof.
  exists (d[X; 3; fin_first⁺⁺⁺] V). split; [| split; [| split]].
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] (simplex_constant X b 3)).
      * apply func_proper. exact (sphere_associativity_filler_face A B C
          V HV fin_first ltac:(intros E; discriminate E)).
      * apply simplex_constant_restrict.
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] B.1).
      * apply func_proper. exact (sphere_associativity_filler_face A B C
          V HV fin_first⁺ ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd B.2))).
  - transitivity (d[X; 2; fin_first⁺⁺] (d[X; 3; fin_first⁺⁺] V)).
    + symmetry. exact (simplex_face_comp (X := X)
        (fin_first⁺⁺ : Ordinal 3) fin_first⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺] C.1).
      * apply func_proper. exact (sphere_associativity_filler_face A B C
          V HV fin_first⁺⁺ ltac:(intros E; discriminate E)).
      * exact (fst (snd (snd C.2))).
  - transitivity (d[X; 2; fin_first⁺⁺⁺] (d[X; 3; fin_first⁺⁺⁺⁺] V)).
    + exact (simplex_face_comp (X := X)
        (fin_first⁺⁺⁺ : Ordinal 3) fin_first⁺⁺⁺
        ltac:(cbn; repeat constructor) V).
    + transitivity (d[X; 2; fin_first⁺⁺⁺] A.1).
      * apply func_proper. exact (sphere_associativity_filler_face A B C
          V HV fin_first⁺⁺⁺⁺ ltac:(intros E; discriminate E)).
      * exact (snd (snd (snd A.2))).
Defined.

End AssociativityHorn.

(** ** Chosen Rebracketing with One Four-Horn Selection

    Fix the ambient simplicial setoid and vertex. Only missing-face-three
    selection is needed to change brackets while keeping the output.
    The input composite witnesses may come from unrelated constructions. *)

(** ** 仅用一个四维选择的选定重括号

    固定环境单纯广集及顶点。改变括号并保留输出只需缺第三面的选择。给定合成
    见证可以来自无关构造。 *)

Section ChosenReassociation.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.

(** Fill the actual associativity horn and retain its missing tetrahedron. *)

(** 填充实际结合律 horn，保留其缺失四面体。 *)

Definition SphereCompositeReassociate
    {x y z s t l : TwoSphereS X b}
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
  : TwoSphereComposite X b x t l.
Proof.
  pose (V := horn_fill (SphereAssociativityHornN X b A B C)).
  exact (SphereCompositeReassociateOfFiller X b A B C V.1 V.2).
Defined.

End ChosenReassociation.

(** ** Associativity in Class Equality

    Fix missing-face-two comparison and missing-face-three rebracketing
    choices. No dimension-three choice is needed for supplied composites;
    specialize afterward to one explicit choice of class multiplication.
    These lemmas do not package a stronger algebraic structure yet. *)

(** ** 类相等下的结合律

    固定缺第二面的比较及缺第三面的重括号选择。对给定合成不要求三维选择；
    随后再特化到一个显式类乘法选择。这些引理尚不打包更强代数结构。 *)

Section ClassAssociativity.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.

(** Four arbitrary composites on the two bracketings have class-equal
    outputs. Their tetrahedra and filler choices need not be equal. *)

(** 两种括号方式上的四份任意合成具有类相等输出，无须等同四面体或填充选择。 *)

Lemma two_sphere_composite_assoc
    {x y z s t l r : TwoSphereS X b}
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (D : TwoSphereComposite X b x t r)
  : (l : TwoSphereClassS X b) ≈S r.
Proof.
  exact (two_sphere_composite_output_eq X b
    (SphereCompositeReassociate X b A B C) D).
Defined.

(** The actual selected class multiplication is associative, with only
    the two required dimension-four choices. *)

(** 实际选定类乘法满足结合律，仅需两个所需四维选择。 *)

Lemma two_sphere_kan_mul_assoc
    (H : HasHornFillers X 3 fin_first⁺⁺) (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_kan_mul X b H x y) z ≈S
      two_sphere_kan_mul X b H x (two_sphere_kan_mul X b H y z).
Proof.
  exact (two_sphere_composite_assoc
    (TwoSphereKanMulComposite X b H x y)
    (TwoSphereKanMulComposite X b H y z)
    (TwoSphereKanMulComposite X b H (two_sphere_kan_mul X b H x y) z)
    (TwoSphereKanMulComposite X b H x (two_sphere_kan_mul X b H y z))).
Defined.

End ClassAssociativity.
