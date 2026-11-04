From Cats Require Export
  Cat.Shape.Simplex.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core.
From Cats.Set Require Export
  Ordinal.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Cofaces and Codegeneracies

    Finite indices enforce all generator bounds. End inclusion [i↑] preserves
    an index; successor [i⁺] raises it by one in a larger ordinal.
    Write [δ[i]] and [σ[i]], or [δ[n; i]] and [σ[n; i]] to specify the
    dimension explicitly when the finite type does not determine it. *)

(** * 余面与余退化

    有限索引保证生成映射的全部界条件；末端嵌入 [i↑] 保持索引，而后继嵌入
    [i⁺] 在较大序数中将其增加一。记作 [δ[i]]、[σ[i]]；有限类型无法
    确定维数时，可用 [δ[n; i]]、[σ[n; i]] 显式指定。 *)

Program Definition Coface {n : nat} (i : Ordinal (S n))
  : (@Hom Δ) n (S n)
  := @OrdinalF n (S n) (@fin_skip (S n) i) _.
Next Obligation.
  change (fin_rank (@fin_skip (S n) i x) ≤
    fin_rank (@fin_skip (S n) i y)).
  rewrite !fin_skip_rank. apply skip_rank_monotone. exact H.
Defined.

Notation "'δ[' i ']'" := (Coface i) : hom_scope.
Notation "'δ[' n ';' i ']'" := (@Coface n i) : hom_scope.

(** A codegeneracy identifies adjacent positions. *)

(** 余退化合并相邻位置。 *)

Program Definition Codegeneracy {n : nat} (i : Ordinal n)
  : (@Hom Δ) (S n) n
  := @OrdinalF (S n) n (@fin_merge n i) _.
Next Obligation.
  change (fin_rank (@fin_merge n i x) ≤ fin_rank (@fin_merge n i y)).
  rewrite !fin_merge_rank. apply merge_rank_monotone. exact H.
Defined.

Notation "'σ[' i ']'" := (Codegeneracy i) : hom_scope.
Notation "'σ[' n ';' i ']'" := (@Codegeneracy n i) : hom_scope.

(** Cofaces commute with the standard upper-index shift, for i <= j. *)

(** 当 i <= j 时，余面在标准的上索引移位下交换。 *)

Lemma coface_comp {n : nat} (i j : Ordinal (S n))
    (H : fin_rank i ≤ fin_rank j)
  : δ[S n; i↑] ∘ δ[n; j] ≈ δ[S n; j⁺] ∘ δ[n; i].
Proof.
  apply simplex_eq_of_rank. intros x.
  change (fin_rank (@fin_skip (S (S n)) i↑
      (@fin_skip (S n) j x)) =
    fin_rank (@fin_skip (S (S n)) j⁺ (@fin_skip (S n) i x))).
  rewrite !fin_skip_rank, ordinal_weaken_rank, ordinal_next_rank.
  apply skip_rank_comp. exact H.
Defined.

(** Codegeneracies commute with the standard upper-index shift. *)

(** 余退化在标准的上索引移位下交换。 *)

Lemma codegeneracy_comp {n : nat} (i j : Ordinal n)
    (H : fin_rank i ≤ fin_rank j)
  : σ[n; i] ∘ σ[S n; j⁺] ≈ σ[n; j] ∘ σ[S n; i↑].
Proof.
  apply simplex_eq_of_rank. intros x.
  change (fin_rank (@fin_merge n i (@fin_merge (S n) j⁺ x)) =
    fin_rank (@fin_merge n j (@fin_merge (S n) i↑ x))).
  rewrite !fin_merge_rank, ordinal_weaken_rank, ordinal_next_rank.
  apply merge_rank_comp. exact H.
Defined.

(** Merging cancels the coface at the same index. *)

(** 合并消去同索引的余面。 *)

Lemma codegeneracy_coface_id {n : nat} (i : Ordinal n)
  : σ[n; i] ∘ δ[n; i↑] ≈ (id : (@Hom Δ) n n).
Proof.
  apply simplex_eq_of_rank. intros x.
  change (fin_rank (@fin_merge n i
    (@fin_skip (S n) i↑ x)) = fin_rank x).
  rewrite fin_merge_rank, fin_skip_rank, ordinal_weaken_rank.
  apply merge_skip_rank_id.
Defined.

(** Merging also cancels the coface at the next index. *)

(** 合并同样消去紧邻后继索引处的余面。 *)

Lemma codegeneracy_coface_next {n : nat} (i : Ordinal n)
  : σ[n; i] ∘ δ[n; i⁺] ≈ (id : (@Hom Δ) n n).
Proof.
  apply simplex_eq_of_rank. intros x.
  change (fin_rank (@fin_merge n i
    (@fin_skip (S n) i⁺ x)) = fin_rank x).
  rewrite fin_merge_rank, fin_skip_rank, ordinal_next_rank.
  apply merge_skip_rank_next.
Defined.

(** Move a coface past a strictly later codegeneracy. *)

(** 将余面移过严格在其后的余退化。 *)

Lemma codegeneracy_coface_before {n : nat}
    (i : Ordinal (S n)) (j : Ordinal n)
    (H : fin_rank i ≤ fin_rank j)
  : σ[S n; j⁺] ∘ δ[S n; i↑] ≈ δ[n; i] ∘ σ[n; j].
Proof.
  apply simplex_eq_of_rank. intros x.
  change (fin_rank (@fin_merge (S n) j⁺
      (@fin_skip (S (S n)) i↑ x)) =
    fin_rank (@fin_skip (S n) i (@fin_merge n j x))).
  repeat first [rewrite fin_merge_rank | rewrite fin_skip_rank |
    rewrite ordinal_weaken_rank | rewrite ordinal_next_rank].
  apply merge_skip_rank_before. exact H.
Defined.

(** Move a coface past a strictly earlier codegeneracy. *)

(** 将余面移过严格在其前的余退化。 *)

Lemma codegeneracy_coface_after {n : nat}
    (i : Ordinal (S n)) (j : Ordinal n)
    (H : fin_rank j < fin_rank i)
  : σ[S n; j↑] ∘ δ[S n; i⁺] ≈ δ[n; i] ∘ σ[n; j].
Proof.
  apply simplex_eq_of_rank. intros x.
  change (fin_rank (@fin_merge (S n) j↑
      (@fin_skip (S (S n)) i⁺ x)) =
    fin_rank (@fin_skip (S n) i (@fin_merge n j x))).
  repeat first [rewrite fin_merge_rank | rewrite fin_skip_rank |
    rewrite ordinal_weaken_rank | rewrite ordinal_next_rank].
  apply merge_skip_rank_after. exact H.
Defined.
