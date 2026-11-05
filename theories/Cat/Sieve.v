From Cats Require Export
  Cat.Core.

(** * Sieves and Their Generators

    A sieve on A is a specified-equality invariant family of arrows into A,
    closed under precomposition. All membership and factorization witnesses
    live in Type. No equality of those witnesses is imposed. *)

(** * 筛及其生成元

    A 上的筛是指向 A 的箭头族，保持指定相等并在预合成下封闭。隶属及分解见证
    均保留在 Type 中，不要求这些见证相等。 *)

(** Membership respects hom equality and restriction. *)

(** 隶属保持 Hom 相等及限制。 *)

Class Sieve (C : Cat) (A : @Ob C)
  :=
  { sieve_member {X : @Ob C} : Hom X A → Type
  ; sieve_member_proper {X}
    :: Proper (@HomEq C X A ==> iffT) (@sieve_member X)
  ; sieve_precomp {X Y} (f : Hom X A) (g : Hom Y X)
    : sieve_member f → sieve_member (f ∘ g)
  }.

Arguments sieve_member {_ _} _ {_} _.
Arguments sieve_precomp {_ _} _ {_ _} _ _ _.

Notation "f '∈Sv' S" := (sieve_member S f)
  (at level 70, no associativity) : type_scope.

(** The generated sieve retains a generator, a factor, and its equation.
    This is a union of images, without quotienting or choosing a unique
    representation of an arrow. *)

(** 生成筛保留生成元、因子及分解方程。它是像的并，不取商，也不选取箭头的唯一
    表示。 *)

Program Definition GeneratedSieve {C : Cat} {A : @Ob C}
    {I : Type} (D : I → @Ob C) (g : ∀ i, Hom (D i) A)
  : Sieve C A
  :=
  {|sieve_member X f := ∃ i : I, ∃ h : Hom X (D i), f ≈ g i ∘ h
  |}.
Next Obligation.
  intros f f' H. split; intros [i [h K]]; exists i, h.
  - transitivity f; [symmetry; exact H | exact K].
  - transitivity f'; assumption.
Defined.
Next Obligation.
  destruct X0 as [i [h H]]. exists i, (h ∘ g0).
  rewrite H, comp_assoc. reflexivity.
Defined.

(** Each generator belongs to its generated sieve. *)

(** 每个生成元均属于其生成筛。 *)

Definition generated_sieve_member {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A) (i : I)
  : g i ∈Sv GeneratedSieve D g
  := (i; (id; symmetry (comp_id_r (g i)))).

(** A sieve contains every generated arrow exactly when it contains all
    generators. Both implications transform retained membership data. *)

(** 筛包含全部生成箭头，当且仅当它包含全部生成元；双向均转换保留的隶属数据。 *)

Definition generated_sieve_universal {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    (S : Sieve C A)
  : (∀ i, g i ∈Sv S) ↔
      (∀ X (f : Hom X A), f ∈Sv GeneratedSieve D g → f ∈Sv S).
Proof.
  split.
  - intros H X f [i [h E]].
    apply (snd (@sieve_member_proper C A S X f (g i ∘ h) E)).
    exact (sieve_precomp S (g i) h (H i)).
  - intros H i. exact (H _ _ (generated_sieve_member g i)).
Defined.

(** The empty family generates the empty sieve at every dimension. *)

(** 空生成族在每个维度生成空筛。 *)

Definition EmptySieve (C : Cat) (A : @Ob C)
  : Sieve C A
  := @GeneratedSieve C A Empty_set (λ _, A) (λ i, match i with end).
