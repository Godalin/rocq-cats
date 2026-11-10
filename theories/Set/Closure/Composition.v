From Cats.Set.Closure Require Export Core.

(** * Composition of Closure Operators

    Two closures do not automatically compose to a closure. A one-sided
    interchange comparison is sufficient. The resulting composite is the
    least extension closed under both operations, with explicit witnesses. *)

(** * 闭包算子的复合

    两个闭包的复合不自动成为闭包；单向交换比较已足够。所得复合是同时对
    两个操作闭合的最小扩张，并保留显式见证。 *)

Local Open Scope closure_scope.

Section Composition.
Context {X : Type} {R : crelation X} `{HR : !PreOrder R}.
Context (c d : Closure R).

(** Interchange has a specified direction. It is not an equality of
    composites, nor an assertion that arbitrary closures commute. *)

(** 交换具有指定方向，不是复合相等，也不断言任意闭包可交换。 *)

Definition is_closure_interchange
  : Type
  := ∀ x, R (c (d x)) (d (c x)).

Context (h : is_closure_interchange).

(** The composite applies [c] first, then [d]. In its flattening proof,
    interchange moves the middle [c] past [d]; the two original flattening
    laws then remove the repeated layers. *)

(** 复合先应用 [c] 再应用 [d]。压平证明用交换将中间的 [c] 移过 [d]，
    再用两个原有压平律消去重复层。 *)

Program Definition CompositeClosure
  : Closure R
  :=
  {|closure_map x := d (c x)
  |}.
Next Obligation.
  split.
  - intros x y k. exact (closure_monotone d (closure_monotone c k)).
  - split.
    + intros x. exact (transitivity (closure_inflate c x)
        (closure_inflate d (c x))).
    + intros x.
      exact (transitivity (closure_monotone d (h (c x)))
        (transitivity (closure_flatten d (c (c x)))
          (closure_monotone d (closure_flatten c x)))).
Defined.

(** A composite-closed object is closed under each factor. Conversely,
    successive monotonicity and closedness flatten the composite at every
    object closed under both factors. *)

(** 复合闭对象对每个因子都闭合；反过来，连续使用单调性与闭性，可在同时对
    两因子闭合的对象处压平复合。 *)

Definition composite_closure_closed (x : X)
  : is_closed CompositeClosure x ↔ (is_closed c x ∧ is_closed d x).
Proof.
  split.
  - intros k. split.
    + exact (transitivity (closure_inflate d (c x)) k).
    + exact (transitivity (closure_monotone d (closure_inflate c x)) k).
  - intros [hc hd]. exact (transitivity (closure_monotone d hc) hd).
Defined.

(** Simultaneous closedness is exactly the target condition needed for
    the least-extension property. This is the form used by relation closures. *)

(** 同时闭性恰好是最小扩张泛性质所需的目标条件；关系闭包可直接使用此形式。 *)

Definition composite_closure_universal {x y : X}
    (hc : is_closed c y) (hd : is_closed d y)
  : R (CompositeClosure x) y ↔ R x y
  := closure_universal CompositeClosure
      (snd (composite_closure_closed y) (hc, hd)).

(** Each factor lies below the composite in pointwise operator order. *)

(** 每个因子在逐点算子顺序中都位于复合之下。 *)

Definition composite_closure_upper
  : (c ⊑Cl CompositeClosure) ∧ (d ⊑Cl CompositeClosure).
Proof.
  split; intros x.
  - exact (closure_inflate d (c x)).
  - exact (closure_monotone d (closure_inflate c x)).
Defined.

(** The composite is the least upper bound of its factors among closure
    operators. This does not assert that every pair admits such a composite. *)

(** 复合是闭包算子中两个因子的最小上界；这不声称每对闭包都具有这种复合。 *)

Definition composite_closure_least (e : Closure R)
    (hc : c ⊑Cl e) (hd : d ⊑Cl e)
  : CompositeClosure ⊑Cl e.
Proof.
  apply (snd (closure_le_iff_closed _ _)). intros x hx.
  apply (snd (composite_closure_closed x)). split.
  - exact (fst (closure_le_iff_closed c e) hc x hx).
  - exact (fst (closure_le_iff_closed d e) hd x hx).
Defined.

End Composition.
