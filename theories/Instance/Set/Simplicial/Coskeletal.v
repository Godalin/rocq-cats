From Cats Require Export
  Instance.Set.Simplicial.Matching.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Unique Boundary Filling and Coskeletality

    A k-coskeletal simplicial setoid has a unique filler for every boundary
    in dimensions strictly above k. Uniqueness uses specified equality;
    the retained fillers are computational, without a choice axiom. *)

(** * 唯一边界填充与余骨架性

    k 余骨架单纯广集在严格高于 k 的维度中，每个边界都具有唯一填充。唯一性使用
    指定相等；保留的填充可计算，不需要选择公理。 *)

(** A boundary filler restricts to the entire given boundary map. *)

(** 边界填充的整个限制映射等于给定边界。 *)

Definition is_boundary_filler@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (b : BoundaryS X n) (x : X n)
  : Type
  := x↾∂[X; n] ≈S b.

(** Checking a positive-dimensional boundary filler reduces to all faces. *)

(** 正维边界填充的检查归结为全部面方程。 *)

Definition boundary_filler_faces_iff@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {n : nat}
    (b : BoundaryS X (S n)) (x : X (S n))
  : is_boundary_filler b x ↔ ∀ j, d[X; n; j] x ≈S face∂[j] b
  := boundary_map_eq_iff (x↾∂[X; S n]) b.

(** Keep every unique boundary fiber at its native value sizes. Matching
    objects may be larger; only the later isomorphism uses common lifts. *)

(** 将每个唯一边界纤维保留在原生值大小；匹配对象可以更大，只有后续同构才使用
    共同提升。 *)

Class IsCoskeletal@{u p +}
    (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (k : nat)
  :=
  { coskeletal_boundary_universal (n : nat) (b : BoundaryS X (S (k + n)))
    : ∃ x : X (S (k + n)),
        is_unique (R := carrier_equiv (X (S (k + n))))
          (is_boundary_filler b) x
  }.

Notation "X '⦂' 'Cosk[' k ']'" := (IsCoskeletal X k)
  (at level 50, no associativity) : type_scope.

(** ** Respectful Coskeletal Filling

    Fix a simplicial setoid [X] that is [k]-coskeletal. Its unique boundary
    fillers above dimension [k] determine a filling map that respects the
    specified boundary equality. *)

(** ** Coskeletal 填充的保相等性

    固定 [k]-coskeletal 的单纯广集 [X]，由高于维度 [k] 的唯一边界填充确定填充映射，并证明它保持指定边界相等。 *)

Section CoskeletalFilling.
Universes u p.
Context {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {k : nat}
    `{HK : !IsCoskeletal X k}.

(** Fillers respect equal boundary data by their universal uniqueness. *)

(** 泛唯一性保证填充保持边界数据的相等。 *)

Program Definition coskeletal_fill_resp (n : nat)
  : BoundaryS X (S (k + n)) →r X (S (k + n))
  :=
  {|func b := (coskeletal_boundary_universal n b).1
  |}.
Next Obligation.
  intros b c E.
  apply (that _ _ (coskeletal_boundary_universal n c).2).
  unfold is_boundary_filler.
  transitivity b;
    [exact (this _ _ (coskeletal_boundary_universal n b).2) | exact E].
Defined.

End CoskeletalFilling.

Notation "'fill∂[' X ';' k ';' n ']'" := (@coskeletal_fill_resp X k _ n)
  : hom_scope.

(** ** Computation Laws for Coskeletal Filling

    Under the same [k]-coskeletal assumption on [X], derive the two inverse
    laws relating filling to boundary restriction. *)

(** ** Coskeletal 填充的计算定律

    在 [X] 的同一 [k]-coskeletal 假设下，导出填充与边界限制之间的两个互逆定律。 *)

Section CoskeletalLaws.
Universes u p.
Context {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {k : nat}
    `{HK : !IsCoskeletal X k}.

(** Restriction recovers the boundary supplied to filling. *)

(** 限制恢复送入填充的边界。 *)

Lemma coskeletal_fill_β (n : nat) (b : BoundaryS X (S (k + n)))
  : (fill∂[X; k; n] b)↾∂[X; S (k + n)] ≈S b.
Proof. exact (this _ _ (coskeletal_boundary_universal n b).2). Defined.

(** Filling the boundary of a simplex recovers that simplex. *)

(** 填充单形的边界恢复该单形。 *)

Lemma coskeletal_fill_η (n : nat) (x : X (S (k + n)))
  : fill∂[X; k; n] (x↾∂[X; S (k + n)]) ≈S x.
Proof.
  symmetry. apply (that _ _ (coskeletal_boundary_universal n
    (x↾∂[X; S (k + n)])).2).
  unfold is_boundary_filler. reflexivity.
Defined.

End CoskeletalLaws.

(** Coskeletality makes boundary restriction an isomorphism after the
    ordinary size inclusion of both native setoids into common universes. *)

(** 将两个原生广集通常嵌入共同宇宙后，余骨架性使边界限制成为同构。 *)

Definition coskeletal_boundary_iso@{u p v q +}
    {X : Functor (Δ^op) SetCat@{v q _ _ _ _ _}} {k : nat}
    `{HK : !IsCoskeletal X k} (n : nat)
  : LiftS@{_ _ u p} (X (S (k + n))) ≅[SetCat]
      LiftS@{_ _ u p} (BoundaryS X (S (k + n))).
Proof.
  exists ((boundary_restrict_resp (S (k + n)))^↑S),
    ((coskeletal_fill_resp n)^↑S).
  split.
  - intros [x]. exact {|lower := coskeletal_fill_η n x
                       |}.
  - intros [b]. exact {|lower := coskeletal_fill_β n b
                       |}.
Defined.

(** Unique filling of one horn reflects equality from the whole boundary.
    Neither arbitrary Kan filling nor mere existence alone suffices. *)

(** 一个 horn 的唯一填充即可从整个边界反映相等；任意 Kan 填充或仅有存在性
    本身均不足够。 *)

Definition boundary_reflects_from_horns@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}}
    {n : nat} {i : Ordinal n}
    (U : ∀ h : HornS X n i, ∃ x : X n,
      is_unique (R := carrier_equiv (X n)) (is_horn_filler h) x)
    (x y : X n) (E : x↾∂[X; n] ≈S y↾∂[X; n])
  : x ≈S y.
Proof.
  pose (h := y↾Λ[X; n; i]).
  transitivity (U h).1.
  - apply (that _ _ (U h).2). intros m a.
    exact (E m (HornBoundaryN n i m a)).
  - symmetry. apply (that _ _ (U h).2).
    unfold is_horn_filler, h. reflexivity.
Defined.

(** Unique first-horn filling in two adjacent positive dimensions gives
    unique boundary filling in the upper dimension. The missing face is
    recovered from its own boundary using lower-dimensional uniqueness. *)

(** 相邻两个正维度中的第一 horn 唯一填充，给出较高维度的唯一边界填充。
    缺失面由其自身边界及低维唯一性恢复。 *)

Definition boundary_from_horns_universal@{u p +}
    {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} (n : nat)
    (L : ∀ h : HornS X (S n) fin_first, ∃ x : X (S n),
      is_unique (R := carrier_equiv (X (S n))) (is_horn_filler h) x)
    (U : ∀ h : HornS X (S (S n)) fin_first, ∃ x : X (S (S n)),
      is_unique (R := carrier_equiv (X (S (S n)))) (is_horn_filler h) x)
    (b : BoundaryS X (S (S n)))
  : ∃ x : X (S (S n)),
      is_unique (R := carrier_equiv (X (S (S n)))) (is_boundary_filler b) x.
Proof.
  pose (h := boundary_horn_resp (S (S n)) fin_first b).
  destruct (U h) as [x Hx].
  assert (R : ∀ j : Ordinal (S n),
      d[X; S n; j⁺] x ≈S face∂[j⁺] b).
  { intros j. assert (Hj : ¬ j⁺ = (fin_first : Ordinal (S (S n))))
      by discriminate.
    transitivity (face[fin_first; j⁺; Hj] h).
    - exact (fst (horn_filler_faces_iff h x) (this _ _ Hx) j⁺ Hj).
    - exact (boundary_horn_face fin_first j⁺ Hj b). }
  assert (B : is_boundary_filler b x).
  { apply (snd (boundary_filler_faces_iff b x)). intros [[] | j].
    - apply (boundary_reflects_from_horns L).
      apply (snd (boundary_map_eq_iff _ _)). intros j.
      change (d[X; n; j] (d[X; S n; fin_first] x) ≈S
        d[X; n; j] (face∂[fin_first] b)).
      pose (Hj := PeanoNat.Nat.le_0_l (fin_rank j)).
      transitivity (d[X; n; fin_first] (d[X; S n; j⁺] x)).
      + exact (simplex_face_comp fin_first j Hj x).
      + transitivity (d[X; n; fin_first] (face∂[j⁺] b)).
        * exact (@func_proper _ _ (d[X; n; fin_first]) _ _ (R j)).
        * symmetry. exact (boundary_face_comp b fin_first j Hj).
    - exact (R j). }
  exists x. refine
    {|this := B
    ; that := _
    |}.
  intros y Hy. apply (boundary_reflects_from_horns U).
  transitivity b; [exact Hy | symmetry; exact B].
Defined.
