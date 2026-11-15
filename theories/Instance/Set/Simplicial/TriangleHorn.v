From Cats Require Export
  Instance.Set.Simplicial.TriangleProduct
  Instance.Set.Simplicial.Boundary.
From Cats Require Import
  Cat.Core.
From Stdlib Require Import
  Lia.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Finite Relative Horn Order for the Triangle Product

    Start with the spatial boundary times the full parameter triangle,
    together with the spatial triangle times the parameter horn. For
    each missing parameter face, attach three tetrahedra followed by
    six four-simplices. The ordering matters: the old region meets each
    new cell in exactly one horn, in every source degree.

    The region below retains actual old-face or earlier-cell factors.
    It is not yet a presheaf pushout square. Such squares, followed by
    the already integrated single-horn extension, are later consumers. *)

(** * 三角积的有限相对 horn 次序

    初始区域为空间边界乘完整参数三角形，再并上空间三角形乘参数 horn。
    每个参数缺面先附着三个四面体，再附着六个四单形。次序是必要的：旧区域
    与每个新单形的交叠在任意来源维数中恰为一个 horn。

    下述区域保留实际旧面或先前单形的分解。它尚不是预层推出方形；这些方形
    及已经集成的单次 horn 延拓将是后续消费者。 *)

(** Write A_k for the supplied coordinate pairs at stage k in any
    degree. The left arrows below transport membership, and the last
    arrow forgets the witness; it is covered by the final-stage theorem.
    The right triangle is constructed from old-region membership of h:
    its face j is retained and both actual coordinates are recovered.
    Turning the regions into presheaves and proving their pushout squares
    remains necessary before using
    %\coqref{Cats.Instance.Set.Simplicial.HornAttachment.HornAttachmentExtension}
    {%[HornAttachmentExtension]%}%. *)

(** 在任一维中，以 A_k 表示阶段 k 的给定坐标对。左图箭头运输隶属，末箭头
    忘却见证，最终阶段定理给出其覆盖。右侧三角形由 h 的旧区域隶属构造：
    面 j 保留，两个实际坐标均被恢复。在使用
    %\coqref{Cats.Instance.Set.Simplicial.HornAttachment.HornAttachmentExtension}
    {%[HornAttachmentExtension]%}% 前，仍须将区域实现为预层并证明推出方形。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large]
A_0 \arrow[r] & A_3 \arrow[r] & A_9
  \arrow[r,"{\mathrm{cover}}"] & \Delta[2]\times\Delta[2]
\end{tikzcd}
\qquad
\begin{tikzcd}[column sep=large,row sep=large]
{[n]} \arrow[r,"h"] \arrow[dr,dashed,"q"'] & {[d_s]} \\
& {[d_s-1]} \arrow[u,"{\delta_j}"',"{j\ne r_s}"]
\end{tikzcd}
\end{center}%
*)

(** The first three cells have dimension three, the remaining six
    dimension four. Store the face dimension so the successor is explicit. *)

(** 前三个单形维数为三，后六个为四；保存面的维数，使单形维数显式为后继。 *)

Definition simplex_triangle_horn_face_dim (s : Ordinal 8)
  : nat
  := if Nat.ltb (fin_rank s) 3 then 2 else 3.

(** Actual coordinates of the nine cells. A tetrahedron is a coface of
    an existing staircase; a four-cell is an existing staircase itself. *)

(** 九个单形的实际坐标。四面体是已有阶梯的余面，四单形就是已有阶梯本身。 *)

Definition SimplexTriangleHornCell (r : Ordinal 2) (s : Ordinal 8)
  : ((@Hom Δ) (S (simplex_triangle_horn_face_dim s)) 2 *
      (@Hom Δ) (S (simplex_triangle_horn_face_dim s)) 2)%type
  := match s as k return
      ((@Hom Δ) (S (simplex_triangle_horn_face_dim k)) 2 *
       (@Hom Δ) (S (simplex_triangle_horn_face_dim k)) 2)%type with
  | inl _ => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first : Ordinal 5) ∘ δ[3; fin_first⁺⁺],
         SimplexTriangleProductTimeF (fin_first : Ordinal 5) ∘ δ[3; fin_first⁺⁺])
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺],
         SimplexTriangleProductTimeF (fin_first⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺])
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺⁺],
         SimplexTriangleProductTimeF (fin_first⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺⁺])
    end
  | inr (inl _) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺],
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺])
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first : Ordinal 5) ∘ δ[3; fin_first⁺⁺],
         SimplexTriangleProductTimeF (fin_first : Ordinal 5) ∘ δ[3; fin_first⁺⁺])
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺],
         SimplexTriangleProductTimeF (fin_first⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺])
    end
  | inr (inr (inl _)) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺],
         SimplexTriangleProductTimeF (fin_first⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺])
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺],
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺])
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺⁺],
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺⁺ : Ordinal 5) ∘ δ[3; fin_first⁺⁺⁺⁺])
    end
  | inr (inr (inr (inl _))) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first : Ordinal 5))
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first : Ordinal 5))
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first : Ordinal 5))
    end
  | inr (inr (inr (inr (inl _)))) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺ : Ordinal 5))
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺ : Ordinal 5))
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺ : Ordinal 5))
    end
  | inr (inr (inr (inr (inr (inl _))))) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺ : Ordinal 5))
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺ : Ordinal 5))
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺ : Ordinal 5))
    end
  | inr (inr (inr (inr (inr (inr (inl _)))))) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺⁺⁺ : Ordinal 5))
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺ : Ordinal 5))
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺ : Ordinal 5))
    end
  | inr (inr (inr (inr (inr (inr (inr (inl _))))))) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺⁺ : Ordinal 5))
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺⁺ : Ordinal 5))
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺⁺ : Ordinal 5))
    end
  | inr (inr (inr (inr (inr (inr (inr (inr (_)))))))) => match r with
    | inl _ =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺ : Ordinal 5))
    | inr (inl _) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺⁺⁺ : Ordinal 5))
    | inr (inr (_)) =>
        (SimplexTriangleProductSpaceF (fin_first⁺⁺⁺⁺⁺ : Ordinal 5),
         SimplexTriangleProductTimeF (fin_first⁺⁺⁺⁺⁺ : Ordinal 5))
    end
  end.

(** The primary spatial coordinate of the supplied cell. *)

(** 给定单形的空间坐标。 *)

Definition SimplexTriangleHornSpaceF (r : Ordinal 2) (s : Ordinal 8)
  : (@Hom Δ) (S (simplex_triangle_horn_face_dim s)) 2
  := fst (SimplexTriangleHornCell r s).

(** The parameter coordinate of that same cell. *)

(** 同一单形的参数坐标。 *)

Definition SimplexTriangleHornTimeF (r : Ordinal 2) (s : Ordinal 8)
  : (@Hom Δ) (S (simplex_triangle_horn_face_dim s)) 2
  := snd (SimplexTriangleHornCell r s).

(** The newly supplied face at each step. All other faces are old. *)

(** 每步新增的面；其余面均已属于旧区域。 *)

Definition simplex_triangle_horn_missing (r : Ordinal 2) (s : Ordinal 8)
  : Ordinal (S (simplex_triangle_horn_face_dim s))
  := match s as k return Ordinal (S (simplex_triangle_horn_face_dim k)) with
  | inl _ => match r with
    | inl _ => fin_first
    | inr (inl _) => fin_first⁺
    | inr (inr (_)) => fin_first⁺
    end
  | inr (inl _) => match r with
    | inl _ => fin_first⁺
    | inr (inl _) => fin_first⁺
    | inr (inr (_)) => fin_first⁺
    end
  | inr (inr (inl _)) => match r with
    | inl _ => fin_first
    | inr (inl _) => fin_first⁺⁺
    | inr (inr (_)) => fin_first⁺⁺
    end
  | inr (inr (inr (inl _))) => match r with
    | inl _ => fin_first
    | inr (inl _) => fin_first⁺
    | inr (inr (_)) => fin_first⁺⁺
    end
  | inr (inr (inr (inr (inl _)))) => match r with
    | inl _ => fin_first⁺
    | inr (inl _) => fin_first⁺
    | inr (inr (_)) => fin_first⁺
    end
  | inr (inr (inr (inr (inr (inl _))))) => match r with
    | inl _ => fin_first
    | inr (inl _) => fin_first⁺
    | inr (inr (_)) => fin_first⁺
    end
  | inr (inr (inr (inr (inr (inr (inl _)))))) => match r with
    | inl _ => fin_first⁺⁺
    | inr (inl _) => fin_first⁺⁺
    | inr (inr (_)) => fin_first⁺⁺⁺
    end
  | inr (inr (inr (inr (inr (inr (inr (inl _))))))) => match r with
    | inl _ => fin_first⁺
    | inr (inl _) => fin_first⁺⁺
    | inr (inr (_)) => fin_first⁺⁺
    end
  | inr (inr (inr (inr (inr (inr (inr (inr (_)))))))) => match r with
    | inl _ => fin_first
    | inr (inl _) => fin_first⁺⁺⁺
    | inr (inr (_)) => fin_first⁺⁺⁺⁺
    end
  end.

(** The initial region retains a spatial boundary factor or a parameter
    horn factor. Both are the existing generated-sieve memberships. *)

(** 初始区域保留空间边界分解或参数 horn 分解，二者均复用已有生成筛隶属。 *)

Definition is_triangle_horn_base (r : Ordinal 2) {n : nat}
    (a b : (@Hom Δ) n 2)
  : Type
  := ((a ∈Sv BoundarySieve 2) + (b ∈Sv HornSieve 2 r))%type.

(** At stage k, keep the base or a coordinate factor through one of
    the first k cells. Membership witnesses are not equated. *)

(** 阶段 k 保留初始区域或经过前 k 个单形之一的双坐标分解，不等同隶属见证。 *)

Definition is_triangle_horn_stage (r : Ordinal 2) (k : nat) {n : nat}
    (a b : (@Hom Δ) n 2)
  : Type
  := (is_triangle_horn_base r a b +
      (∃ s : Ordinal 8, (fin_rank s < k) *
        (∃ h : (@Hom Δ) n (S (simplex_triangle_horn_face_dim s)),
          (a ≈ SimplexTriangleHornSpaceF r s ∘ h) ∧
          (b ≈ SimplexTriangleHornTimeF r s ∘ h))))%type.

(** ** Closure of the Supplied Regions

    Fix a parameter missing face and a stage. Transport uses specified
    operator equality. Precomposition retains the same old generator
    and composes its factor, so all source dimensions are allowed. *)

(** ** 给定区域的封闭性

    固定参数缺面和阶段；运输使用指定算子相等。预合成保留同一旧生成元并复合
    其因子，故允许任意来源维数。 *)

Section RegionClosure.
Context (r : Ordinal 2) (k : nat).

(** Changing either coordinate by specified equality preserves membership. *)

(** 按指定相等改变任一坐标均保持隶属。 *)

Definition triangle_horn_stage_transport {n : nat}
    (a a' b b' : (@Hom Δ) n 2) (E : a ≈ a') (F : b ≈ b')
    (H : is_triangle_horn_stage r k a b)
  : is_triangle_horn_stage r k a' b'.
Proof.
  destruct H as [[A | B] | [s [K [h [A B]]]]].
  - left. left. exact (fst (@sieve_member_proper Δ 2
      (BoundarySieve 2) n a a' E) A).
  - left. right. exact (fst (@sieve_member_proper Δ 2
      (HornSieve 2 r) n b b' F) B).
  - right. exists s. split; [exact K |]. exists h. split.
    + transitivity a; [symmetry; exact E | exact A].
    + transitivity b; [symmetry; exact F | exact B].
Defined.

(** Restrict both coordinates along the same arbitrary shape operator. *)

(** 沿同一任意形状算子限制两个坐标。 *)

Definition triangle_horn_stage_pre {n m : nat}
    (a b : (@Hom Δ) n 2) (θ : (@Hom Δ) m n)
    (H : is_triangle_horn_stage r k a b)
  : is_triangle_horn_stage r k (a ∘ θ) (b ∘ θ).
Proof.
  destruct H as [[A | B] | [s [K [h [A B]]]]].
  - left. left. exact (sieve_precomp (BoundarySieve 2) a θ A).
  - left. right. exact (sieve_precomp (HornSieve 2 r) b θ B).
  - right. exists s. split; [exact K |]. exists (h ∘ θ). split.
    + rewrite A, comp_assoc. reflexivity.
    + rewrite B, comp_assoc. reflexivity.
Defined.

End RegionClosure.

Local Ltac triangle_fin_cases x :=
  first [destruct x as [[] | x]; [idtac | triangle_fin_cases x] | destruct x].

Local Ltac triangle_boundary_face i :=
  lazymatch goal with
  | |- is_triangle_horn_stage ?r ?k ?a ?b =>
      let H := fresh "avoid" in
      assert (H : ∀ z, ¬ a z = i) by
        (intros z E; triangle_fin_cases z; discriminate E);
      left; left; exists i, (CofacePreimageF i a H);
      symmetry; apply coface_preimage_β
  end.

Local Ltac triangle_parameter_face i :=
  lazymatch goal with
  | |- is_triangle_horn_stage ?r ?k ?a ?b =>
      let H := fresh "avoid" in
      let R := fresh "retained" in
      assert (R : ¬ i = r) by discriminate;
      assert (H : ∀ z, ¬ b z = i) by
        (intros z E; triangle_fin_cases z; discriminate E);
      left; right; exists (i; R), (CofacePreimageF i b H);
      symmetry; apply coface_preimage_β
  end.

Local Ltac triangle_shape_equations :=
  split; apply (snd (simplex_eq_iff _ _)); intros z;
    triangle_fin_cases z; reflexivity.

Local Ltac triangle_earlier_face s :=
  right; exists s; split; [cbn; lia |];
  first
    [exists (id : (@Hom Δ) 3 3); triangle_shape_equations
    |exists (δ[2; fin_first]); triangle_shape_equations
    |exists (δ[2; fin_first⁺]); triangle_shape_equations
    |exists (δ[2; fin_first⁺⁺]); triangle_shape_equations
    |exists (δ[2; fin_first⁺⁺⁺]); triangle_shape_equations
    |exists (δ[3; fin_first]); triangle_shape_equations
    |exists (δ[3; fin_first⁺]); triangle_shape_equations
    |exists (δ[3; fin_first⁺⁺]); triangle_shape_equations
    |exists (δ[3; fin_first⁺⁺⁺]); triangle_shape_equations
    |exists (δ[3; fin_first⁺⁺⁺⁺]); triangle_shape_equations].

(** Every retained facet has an actual old-region factor. Finite search
    in this proof only constructs the certified face/earlier-cell witness;
    it is not an assumed attachment or target extension. *)

(** 每个保留面都有实际旧区域分解。证明中的有限搜索仅构造经过验证的旧面／
    先前单形见证，不预设附着或目标延拓。 *)

Definition triangle_horn_retained_face (r : Ordinal 2) (s : Ordinal 8)
    (j : Ordinal (S (simplex_triangle_horn_face_dim s)))
    (H : ¬ j = simplex_triangle_horn_missing r s)
  : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ δ[simplex_triangle_horn_face_dim s; j])
      (SimplexTriangleHornTimeF r s ∘ δ[simplex_triangle_horn_face_dim s; j]).
Proof.
  triangle_fin_cases r; triangle_fin_cases s; triangle_fin_cases j;
    try (destruct (H eq_refl)).
  all: first
    [triangle_boundary_face (fin_first : Ordinal 2)
    |triangle_boundary_face (fin_first⁺ : Ordinal 2)
    |triangle_boundary_face (fin_first⁺⁺ : Ordinal 2)
    |triangle_parameter_face (fin_first : Ordinal 2)
    |triangle_parameter_face (fin_first⁺ : Ordinal 2)
    |triangle_parameter_face (fin_first⁺⁺ : Ordinal 2)
    |triangle_earlier_face (fin_first : Ordinal 8)
    |triangle_earlier_face (fin_first⁺ : Ordinal 8)
    |triangle_earlier_face (fin_first⁺⁺ : Ordinal 8)
    |triangle_earlier_face (fin_first⁺⁺⁺ : Ordinal 8)
    |triangle_earlier_face (fin_first⁺⁺⁺⁺ : Ordinal 8)
    |triangle_earlier_face (fin_first⁺⁺⁺⁺⁺ : Ordinal 8)
    |triangle_earlier_face (fin_first⁺⁺⁺⁺⁺⁺ : Ordinal 8)
    |triangle_earlier_face (fin_first⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8)
    |triangle_earlier_face (fin_first⁺⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8)].
Defined.

Local Ltac triangle_vertex :=
  first
    [exists fin_first; split; [discriminate | reflexivity]
    |exists (fin_first⁺); split; [discriminate | reflexivity]
    |exists (fin_first⁺⁺); split; [discriminate | reflexivity]
    |exists (fin_first⁺⁺⁺); split; [discriminate | reflexivity]
    |exists (fin_first⁺⁺⁺⁺); split; [discriminate | reflexivity]].

(** Every spatial vertex occurs on the retained vertices of a new cell.
    Therefore a spatial boundary cannot contain its missing facet. *)

(** 新单形的保留顶点包含每个空间顶点，因此空间边界不能包含其新增面。 *)

Definition triangle_horn_spatial_vertex (r : Ordinal 2) (s : Ordinal 8)
    (i : Ordinal 2)
  : ∃ j : Ordinal (S (simplex_triangle_horn_face_dim s)),
      (¬ j = simplex_triangle_horn_missing r s) ∧
      (SimplexTriangleHornSpaceF r s j = i).
Proof.
  triangle_fin_cases r; triangle_fin_cases s; triangle_fin_cases i;
    triangle_vertex.
Defined.

(** Every retained parameter vertex also occurs on that same retained
    vertex set. The parameter vertex excluded from the horn is explicit. *)

(** 同一保留顶点集也包含每个保留参数顶点；参数 horn 排除的顶点显式给出。 *)

Definition triangle_horn_parameter_vertex (r : Ordinal 2) (s : Ordinal 8)
    (i : Ordinal 2) (H : ¬ i = r)
  : ∃ j : Ordinal (S (simplex_triangle_horn_face_dim s)),
      (¬ j = simplex_triangle_horn_missing r s) ∧
      (SimplexTriangleHornTimeF r s j = i).
Proof.
  triangle_fin_cases r; triangle_fin_cases s; triangle_fin_cases i;
    try (destruct (H eq_refl)).
  all: triangle_vertex.
Defined.

Local Ltac triangle_vertex_separated :=
  split; [discriminate |]; intros w; triangle_fin_cases w;
    intros [A B]; first [discriminate A | discriminate B].

(** Some retained vertex of a new cell lies outside each earlier cell.
    Both coordinate inequalities are tested together: a single coordinate
    alone need not separate the cells. This is finite geometric data. *)

(** 对每个先前单形，新单形的某个保留顶点落在其外。联合检验两个坐标；单个
    坐标不必分离两个单形。这是有限几何数据。 *)

Definition triangle_horn_earlier_separation (r : Ordinal 2)
    (s t : Ordinal 8) (H : fin_rank t < fin_rank s)
  : ∃ j : Ordinal (S (simplex_triangle_horn_face_dim s)),
      (¬ j = simplex_triangle_horn_missing r s) ∧
      (∀ w : Ordinal (S (simplex_triangle_horn_face_dim t)),
        ¬ ((SimplexTriangleHornSpaceF r s j = SimplexTriangleHornSpaceF r t w) ∧
           (SimplexTriangleHornTimeF r s j = SimplexTriangleHornTimeF r t w))).
Proof.
  triangle_fin_cases r; triangle_fin_cases s; triangle_fin_cases t;
    cbn [fin_rank] in H; try lia.
  all: first
    [exists fin_first; triangle_vertex_separated
    |exists (fin_first⁺); triangle_vertex_separated
    |exists (fin_first⁺⁺); triangle_vertex_separated
    |exists (fin_first⁺⁺⁺); triangle_vertex_separated
    |exists (fin_first⁺⁺⁺⁺); triangle_vertex_separated].
Defined.

(** ** The Exact Intersection in Every Degree

    Fix one actual new cell and any operator into it. Membership in the
    preceding region forces its image to avoid a retained vertex; the
    existing coface preimage then constructs the actual horn factor.
    Conversely each retained face was already proved old, and restriction
    preserves that membership. No nondegeneracy assumption is imposed. *)

(** ** 任意维中的精确交叠

    固定一个实际新单形及任意入射算子。属于前一区域迫使其像省略一个保留顶点，
    再由既有余面原像构造实际 horn 分解。反之，每个保留面均已属于旧域，限制
    保持隶属。不要求入射单形非退化。 *)

Section ExactIntersection.
Context (r : Ordinal 2) (s : Ordinal 8).
Context {n : nat} (h : (@Hom Δ) n (S (simplex_triangle_horn_face_dim s))).

(** Each possible old-region witness supplies an omitted retained vertex.
    Earlier-cell separation uses both actual coordinate equations. *)

(** 每种旧区域见证都提供一个被省略的保留顶点；先前单形的分离使用两个实际
    坐标方程。 *)

Definition triangle_horn_stage_avoids
    (H : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ h)
      (SimplexTriangleHornTimeF r s ∘ h))
  : ∃ j : Ordinal (S (simplex_triangle_horn_face_dim s)),
      (¬ j = simplex_triangle_horn_missing r s) ∧ (∀ z, ¬ h z = j).
Proof.
  destruct H as [[[i [f E]] | [[i I] [f E]]] | [t [K [f [E F]]]]].
  - destruct (triangle_horn_spatial_vertex r s i) as [j [J V]].
    exists j. split; [exact J |]. intros z Z.
    apply (@fin_skip_avoids 2 i (f z)).
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    change (SimplexTriangleHornSpaceF r s (h z) = δ[1; i] (f z)) in Ez.
    change (δ[1; i] (f z) = i). rewrite Z, V in Ez. symmetry. exact Ez.
  - destruct (triangle_horn_parameter_vertex r s i I) as [j [J V]].
    exists j. split; [exact J |]. intros z Z.
    apply (@fin_skip_avoids 2 i (f z)).
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    change (SimplexTriangleHornTimeF r s (h z) = δ[1; i] (f z)) in Ez.
    change (δ[1; i] (f z) = i). rewrite Z, V in Ez. symmetry. exact Ez.
  - destruct (triangle_horn_earlier_separation r s t K) as [j [J V]].
    exists j. split; [exact J |]. intros z Z. apply (V (f z)).
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    pose proof (fst (simplex_eq_iff _ _) F z) as Fz.
    change (SimplexTriangleHornSpaceF r s (h z) =
      SimplexTriangleHornSpaceF r t (f z)) in Ez.
    change (SimplexTriangleHornTimeF r s (h z) =
      SimplexTriangleHornTimeF r t (f z)) in Fz.
    rewrite Z in Ez, Fz. split; assumption.
Defined.

(** Retain the exact horn member, including its computed coface factor. *)

(** 保留精确的 horn 隶属，包括其计算所得的余面因子。 *)

Definition triangle_horn_stage_reflect
    (H : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ h)
      (SimplexTriangleHornTimeF r s ∘ h))
  : h ∈Sv HornSieve (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s).
Proof.
  destruct (triangle_horn_stage_avoids H) as [j [J V]].
  exists (j; J), (CofacePreimageF j h V).
  symmetry. apply coface_preimage_β.
Defined.

(** A horn restriction lands in the old region by its retained face,
    followed by the same arbitrary-degree factor. *)

(** horn 限制先经过保留面、再经过同一个任意维因子，因而落在旧区域中。 *)

Definition triangle_horn_stage_from_horn
    (H : h ∈Sv HornSieve (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s))
  : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ h)
      (SimplexTriangleHornTimeF r s ∘ h).
Proof.
  destruct H as [[j J] [q E]].
  pose (P := triangle_horn_stage_pre r (fin_rank s)
    (SimplexTriangleHornSpaceF r s ∘ δ[simplex_triangle_horn_face_dim s; j])
    (SimplexTriangleHornTimeF r s ∘ δ[simplex_triangle_horn_face_dim s; j]) q
    (triangle_horn_retained_face r s j J)).
  refine (triangle_horn_stage_transport r (fin_rank s) _ _ _ _ _ _ P).
  - rewrite E, comp_assoc. reflexivity.
  - rewrite E, comp_assoc. reflexivity.
Defined.

(** The old-region preimage of this cell is exactly its specified horn.
    The equivalence transforms membership witnesses, not their records. *)

(** 此单形的旧区域原像恰为指定 horn；双向转换隶属见证，不等同见证记录。 *)

Definition triangle_horn_stage_preimage_iff
  : is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ h)
      (SimplexTriangleHornTimeF r s ∘ h) ↔
      h ∈Sv HornSieve (S (simplex_triangle_horn_face_dim s))
        (simplex_triangle_horn_missing r s)
  := (triangle_horn_stage_reflect, triangle_horn_stage_from_horn).

End ExactIntersection.

(** The zero stage is precisely the supplied relative boundary/horn
    region. There cannot be an earlier cell at stage zero. *)

(** 零阶段恰为给定相对边界／horn 区域；此时不可能有先前单形。 *)

Definition triangle_horn_stage_zero_iff (r : Ordinal 2) {n : nat}
    (a b : (@Hom Δ) n 2)
  : is_triangle_horn_stage r 0%nat a b ↔ is_triangle_horn_base r a b.
Proof.
  split.
  - intros [H | [s [K H]]]; [exact H | lia].
  - intros H. left. exact H.
Defined.

(** Advancing a stage retains every old coordinate pair and its factors. *)

(** 推进阶段保留每个旧坐标对及其分解。 *)

Definition triangle_horn_stage_mono (r : Ordinal 2) (k l : nat)
    (K : k ≤ l) {n : nat} (a b : (@Hom Δ) n 2)
    (H : is_triangle_horn_stage r k a b)
  : is_triangle_horn_stage r l a b.
Proof.
  destruct H as [H | [s [L H]]]; [left; exact H |].
  right. exists s. split; [lia | exact H].
Defined.

(** The supplied new cell is present immediately after its attachment. *)

(** 给定新单形在对应附着之后立即属于该阶段。 *)

Definition triangle_horn_stage_cell (r : Ordinal 2) (s : Ordinal 8)
  : is_triangle_horn_stage r (S (fin_rank s))
      (SimplexTriangleHornSpaceF r s) (SimplexTriangleHornTimeF r s).
Proof.
  right. exists s. split; [lia |]. exists id. split;
    symmetry; apply comp_id_r.
Defined.

(** Locate each original maximal staircase among the last six cells. *)

(** 在后六个单形中定位每个原始最大阶梯。 *)

Definition simplex_triangle_horn_maximal_step (r : Ordinal 2) (i : Ordinal 5)
  : Ordinal 8
  := match r with
  | inl _ => match i with
    | inl _ => fin_first⁺⁺⁺
    | inr (inl _) => fin_first⁺⁺⁺⁺⁺
    | inr (inr (inl _)) => fin_first⁺⁺⁺⁺⁺⁺⁺⁺
    | inr (inr (inr (inl _))) => fin_first⁺⁺⁺⁺
    | inr (inr (inr (inr (inl _)))) => fin_first⁺⁺⁺⁺⁺⁺⁺
    | inr (inr (inr (inr (inr (_))))) => fin_first⁺⁺⁺⁺⁺⁺
    end
  | inr (inl _) => match i with
    | inl _ => fin_first⁺⁺⁺
    | inr (inl _) => fin_first⁺⁺⁺⁺
    | inr (inr (inl _)) => fin_first⁺⁺⁺⁺⁺
    | inr (inr (inr (inl _))) => fin_first⁺⁺⁺⁺⁺⁺
    | inr (inr (inr (inr (inl _)))) => fin_first⁺⁺⁺⁺⁺⁺⁺
    | inr (inr (inr (inr (inr (_))))) => fin_first⁺⁺⁺⁺⁺⁺⁺⁺
    end
  | inr (inr (_)) => match i with
    | inl _ => fin_first⁺⁺⁺
    | inr (inl _) => fin_first⁺⁺⁺⁺
    | inr (inr (inl _)) => fin_first⁺⁺⁺⁺⁺
    | inr (inr (inr (inl _))) => fin_first⁺⁺⁺⁺⁺⁺
    | inr (inr (inr (inr (inl _)))) => fin_first⁺⁺⁺⁺⁺⁺⁺
    | inr (inr (inr (inr (inr (_))))) => fin_first⁺⁺⁺⁺⁺⁺⁺⁺
    end
  end.

(** Every product simplex is in the final stage. Reuse the integrated
    six-staircase factorization, including its arbitrary source degree. *)

(** 每个积单形都属于最终阶段，复用已集成的六阶梯分解及其任意来源维数。 *)

Definition triangle_horn_stage_complete (r : Ordinal 2) {n : nat}
    (a b : (@Hom Δ) n 2)
  : is_triangle_horn_stage r 9 a b.
Proof.
  destruct (SimplexTriangleProductFactor a b) as [i [h [E F]]].
  right. exists (simplex_triangle_horn_maximal_step r i).
  triangle_fin_cases r; triangle_fin_cases i.
  all: split; [cbn; lia | exists h; split; symmetry; assumption].
Defined.

(** Both coordinates jointly distinguish vertices of every attached cell.
    This is injectivity of finite positions, not equality of functor records. *)

(** 两个坐标联合区分每个附着单形的顶点；这是有限位置的单射性，不是函子记录
    相等。 *)

Definition triangle_horn_cell_vertices_injective (r : Ordinal 2)
    (s : Ordinal 8) (i j : Ordinal (S (simplex_triangle_horn_face_dim s)))
  : SimplexTriangleHornSpaceF r s i = SimplexTriangleHornSpaceF r s j →
      SimplexTriangleHornTimeF r s i = SimplexTriangleHornTimeF r s j → i = j.
Proof.
  triangle_fin_cases r; triangle_fin_cases s;
    triangle_fin_cases i; triangle_fin_cases j; intros E F;
    first [reflexivity | discriminate E | discriminate F].
Defined.

(** Thus two operators into the same cell agree whenever both coordinates
    agree. Their law witnesses and operator records need not be equal. *)

(** 因此，进入同一单形的两个算子只要双坐标相等，便按指定算子相等一致；
    不要求定律见证或算子记录相等。 *)

Definition triangle_horn_cell_factors_eq (r : Ordinal 2) (s : Ordinal 8)
    {n : nat} (f g : (@Hom Δ) n (S (simplex_triangle_horn_face_dim s)))
    (E : SimplexTriangleHornSpaceF r s ∘ f ≈ SimplexTriangleHornSpaceF r s ∘ g)
    (F : SimplexTriangleHornTimeF r s ∘ f ≈ SimplexTriangleHornTimeF r s ∘ g)
  : f ≈ g.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  apply (triangle_horn_cell_vertices_injective r s).
  - exact (fst (simplex_eq_iff _ _) E z).
  - exact (fst (simplex_eq_iff _ _) F z).
Defined.

(** The missing facet is genuinely new: its retained vertices cannot
    all avoid the retained position forced by old-region membership. *)

(** 缺失面确实是新的：旧区域隶属迫使省略的保留位置不可能被该面全部避开。 *)

Definition triangle_horn_missing_face_not_old (r : Ordinal 2) (s : Ordinal 8)
  : ¬ is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s ∘ δ[simplex_triangle_horn_face_dim s;
        simplex_triangle_horn_missing r s])
      (SimplexTriangleHornTimeF r s ∘ δ[simplex_triangle_horn_face_dim s;
        simplex_triangle_horn_missing r s]).
Proof.
  intros H.
  destruct (triangle_horn_stage_avoids r s
    (δ[simplex_triangle_horn_face_dim s; simplex_triangle_horn_missing r s]) H)
    as [j [J V]].
  pose (P := @fin_unskip (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing r s) j J).
  exact (V P.1 P.2).
Defined.

(** The whole cell is also new, since restricting it to its missing
    facet would otherwise contradict the preceding result. *)

(** 整个单形也是新的；否则限制到缺失面后会与上一定理矛盾。 *)

Definition triangle_horn_cell_not_old (r : Ordinal 2) (s : Ordinal 8)
  : ¬ is_triangle_horn_stage r (fin_rank s)
      (SimplexTriangleHornSpaceF r s) (SimplexTriangleHornTimeF r s).
Proof.
  intros H. apply (triangle_horn_missing_face_not_old r s).
  exact (triangle_horn_stage_pre r (fin_rank s)
    (SimplexTriangleHornSpaceF r s) (SimplexTriangleHornTimeF r s)
    (δ[simplex_triangle_horn_face_dim s; simplex_triangle_horn_missing r s]) H).
Defined.
