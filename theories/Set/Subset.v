From Cats.Set Require Export
  Morphism.

(** * Subsets with Retained Membership

    Membership may contain computational data. Equality compares only the
    underlying elements, without comparing membership witnesses. *)

(** * 保留隶属见证的子集

    隶属可以包含计算数据；相等只比较底层元素，不比较隶属见证。 *)

(** A predicate cuts out a setoid with the inherited specified equality.
    Its carrier universe must contain the retained membership data. *)

(** 谓词截出继承指定相等的广集；载体宇宙须容纳保留的隶属数据。 *)

Program Definition SubsetS (X : SetC) (P : X → Type)
  : SetC
  :=
  {|carrier := ∃ x : X, P x
  ; carrier_equiv x y := x.1 ≈S y.1
  |}.
Next Obligation.
  split.
  - intros [x H]. reflexivity.
  - intros [x H] [y K] E. symmetry. exact E.
  - intros [x H] [y K] [z L] E F. transitivity y; assumption.
Defined.

(** Forget membership while preserving the underlying equality. *)

(** 忘却隶属见证并保持底层相等。 *)

Program Definition subset_inclusion_resp {X : SetC} {P : X → Type}
  : SubsetS X P →r X
  :=
  {|func x := x.1
  |}.
Next Obligation. intros x y H. exact H. Defined.

(** A respectful map whose values have chosen membership lifts to the
    subset. No equation on the chosen witnesses is required. *)

(** 若保相等映射的值具有选定隶属见证，则该映射提升到子集；无需比较所选见证。 *)

Program Definition subset_pair_resp {X Y : SetC} {P : Y → Type}
    (f : X →r Y) (H : ∀ x, P (f x))
  : X →r SubsetS Y P
  :=
  {|func x := (f x; H x)
  |}.
Next Obligation. intros x y E. exact (@func_proper _ _ f x y E). Defined.
