From Cats.Set.Relation Require Export StrongNormalization.

(** * Reducibility Candidates

    A candidate is a Type-valued predicate on a directed relation. Its
    members are strongly normalizing, steps preserve membership, and
    membership expands from all reducts of a designated neutral element.
    Neutrality is a supplied predicate; no syntax or category is required.
    These are properties of a predicate, not a chosen normalization
    algorithm or an equality of its witnesses. *)

(** * 可归约性候选

    候选是有向关系上的 Type 值谓词：其成员强归一化，步骤保持成员性，且指定
    中性元素的所有后继属于候选时，该元素也属于候选。中性性由参数谓词给出，
    不要求语法或范畴。这些是谓词的性质，不是选定的归一化算法或见证相等。 *)

(** The carrier, edge, neutrality and membership universes are independent.
    Normalization trees and quantified laws have their own size bounds. *)

(** 载体、边、中性性和成员性的宇宙独立；归一化树与量化定律另有大小界。 *)

Class IsReducibilityCandidate@{a r n p s l} {A : Type@{a}}
    (R : A → A → Type@{r}) (N : A → Type@{n}) (P : A → Type@{p})
  : Type@{l}
  :=
  {
  (** Membership supplies a tree covering every directed continuation. *)

  (** 成员性提供覆盖每个有向后续的树。 *)

    candidate_sn : ∀ x, P x → SN@{a r s} R x

  (** Every immediate reduct inherits membership. *)

  (** 每个直接后继继承成员性。 *)

  ; candidate_step : ∀ x y, R x y → P x → P y

  (** A neutral element belongs when all its immediate reducts belong;
      it need not have a reduct, so neutral terminal elements belong too. *)

  (** 中性元素的全部直接后继属于候选时，它也属于候选；它不必具有后继，
      因而终止的中性元素同样属于候选。 *)

  ; candidate_expand : ∀ x, N x → (∀ y, R x y → P y) → P x
  }.

Arguments candidate_sn {_ _ _ _} {_} _ _.
Arguments candidate_step {_ _ _ _} {_} _ _ _ _.
Arguments candidate_expand {_ _ _ _} {_} _ _ _.

(** Step closure iterates along a finite directed path. The path and
    normalization-tree universes are independent: membership transport
    uses the step law, not a comparison or resizing of trees. *)

(** 步骤封闭沿有限有向路径迭代。路径和归一化树的宇宙独立：成员性传递使用
    步骤律，不比较或缩小树。 *)

Definition candidate_rtc@{a r n p s k w +} {A : Type@{a}}
    {R : A → A → Type@{r}} {N : A → Type@{n}} {P : A → Type@{p}}
    (hP : IsReducibilityCandidate@{a r n p s k} R N P)
    {x y : A} (h : ReflTransClosure@{a r w} R x y)
  : P x → P y.
Proof.
  induction h as [x | x y z h q ih]; intros p.
  - exact p.
  - exact (ih (@candidate_step _ _ _ _ hP x y h p)).
Defined.

(** Pointwise equivalent predicates have equivalent candidate laws. This
    transports membership evidence rather than equating predicates or
    their normalization trees. *)

(** 逐点等价的谓词具有等价候选律；这里传递成员见证，不要求谓词或归一化树
    本身相等。 *)

Global Instance IsReducibilityCandidate_proper@{a r n p s l +}
    {A : Type@{a}} (R : A → A → Type@{r}) (N : A → Type@{n})
  : Proper (pointwise_relation A iffT ==> iffT)
      (@IsReducibilityCandidate@{a r n p s l} A R N).
Proof.
  intros P Q e. split; intros h.
  - refine {|candidate_sn := λ x p,
              @candidate_sn A R N P h x (snd (e x) p)
            ; candidate_step := λ x y k p,
                fst (e y) (@candidate_step A R N P h x y k (snd (e x) p))
            ; candidate_expand := λ x n next,
                fst (e x) (@candidate_expand A R N P h x n
                  (λ y k, snd (e y) (next y k)))
            |}.
  - refine {|candidate_sn := λ x p,
              @candidate_sn A R N Q h x (fst (e x) p)
            ; candidate_step := λ x y k p,
                snd (e y) (@candidate_step A R N Q h x y k (fst (e x) p))
            ; candidate_expand := λ x n next,
                snd (e x) (@candidate_expand A R N Q h x n
                  (λ y k, fst (e y) (next y k)))
            |}.
Defined.

(** ** The Normalization Predicate

    Fix an arbitrary directed relation and any neutrality predicate.
    Strong normalization itself is a candidate: its tree constructor
    already supplies expansion, even without the neutrality assumption. *)

(** ** 归一化谓词

    固定任意有向关系及任意中性性谓词。强归一化本身是候选：其树构造器已经
    提供展开，甚至不需要中性性假设。 *)

Section NormalizationCandidate.
Context {A : Type} (R : crelation A) (N : A → Type).

(** Candidate laws for normalization keep all outgoing branches. *)

(** 归一化的候选律保留全部向外分支。 *)

Global Instance SN_IsReducibilityCandidate
  : IsReducibilityCandidate R N (SN R).
Proof.
  refine {|candidate_sn := λ x p, p
          ; candidate_step := λ x y h p, sn_step p h
          ; candidate_expand := λ x n next, sn_intro next
          |}.
Defined.

End NormalizationCandidate.
