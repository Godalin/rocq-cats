From Cats.Set Require Export
  Ordinal.

(** * Avoiding Small Families of Finite Positions

    With more available positions than specified ones, choose an unused
    position by finite case analysis. Witnesses are transparent, and
    repeated inputs are permitted; no choice principle is needed. *)

(** * 避开有限位置的小族

    可用位置多于指定位置时，可通过有限分类选出未使用的位置。见证透明，
    允许输入重复，不需要选择原理。 *)

(** Avoid 4 specified positions among at least 5. *)

(** 在至少 5 个位置中避开 4 个指定位置。 *)

Definition fin_avoid_quadruple {n : nat}
    (a b c d : Fin (S (S (S (S (S n))))))
  : ∃ v : Fin (S (S (S (S (S n))))),
      (¬ v = a) ∧ (¬ v = b) ∧ (¬ v = c) ∧ (¬ v = d).
Proof.
  destruct a as [[] | a], b as [[] | b], c as [[] | c], d as [[] | d].
  - exists (fin_next fin_first). repeat split; discriminate.
  - destruct (fin_avoid_triple d d d) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_triple c c c) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_triple c d d) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_triple b b b) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_triple b d d) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_triple b c c) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_triple b c d) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_triple a a a) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_triple a d d) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_triple a c c) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_triple a c d) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_triple a b b) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_triple a b d) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_triple a b c) as [v [H0 [H1 H2]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - exists fin_first. repeat split; discriminate.
Defined.

(** Avoid 5 specified positions among at least 6. *)

(** 在至少 6 个位置中避开 5 个指定位置。 *)

Definition fin_avoid_quintuple {n : nat}
    (a b c d e : Fin (S (S (S (S (S (S n)))))))
  : ∃ v : Fin (S (S (S (S (S (S n)))))),
      (¬ v = a) ∧ (¬ v = b) ∧ (¬ v = c) ∧ (¬ v = d) ∧ (¬ v = e).
Proof.
  destruct a as [[] | a], b as [[] | b], c as [[] | c], d as [[] | d], e as [[] | e].
  - exists (fin_next fin_first). repeat split; discriminate.
  - destruct (fin_avoid_quadruple e e e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_quadruple d d d d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_quadruple d e e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple c c c c) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_quadruple c e e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple c d d d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple c d e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple b b b b) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_quadruple b e e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple b d d d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple b d e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple b c c c) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple b c e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple b c d d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple b c d e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
    + intros E. apply H3. now injection E.
  - destruct (fin_avoid_quadruple a a a a) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
  - destruct (fin_avoid_quadruple a e e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple a d d d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple a d e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple a c c c) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple a c e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple a c d d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple a c d e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
    + intros E. apply H3. now injection E.
  - destruct (fin_avoid_quadruple a b b b) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
  - destruct (fin_avoid_quadruple a b e e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple a b d d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple a b d e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
    + intros E. apply H3. now injection E.
  - destruct (fin_avoid_quadruple a b c c) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
  - destruct (fin_avoid_quadruple a b c e) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
    + intros E. apply H3. now injection E.
  - destruct (fin_avoid_quadruple a b c d) as [v [H0 [H1 [H2 H3]]]].
    exists (fin_next v). repeat split; try discriminate.
    + intros E. apply H0. now injection E.
    + intros E. apply H1. now injection E.
    + intros E. apply H2. now injection E.
    + intros E. apply H3. now injection E.
  - exists fin_first. repeat split; discriminate.
Defined.
