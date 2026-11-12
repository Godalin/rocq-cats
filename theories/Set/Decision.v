From Cats.Set Require Export Core.

(** * Constructive Decisions

    A decision contains a witness or a map refuting every possible witness.
    The proposition being decided may itself be Type valued. Native
    equality of indices is one concrete application, distinct from the
    specified equality of an arbitrary setoid. *)

(** * 构造性判定

    判定包含一个见证，或反驳任意可能见证的映射。被判定的命题本身可以取值于
    Type。索引的原生相等是一个具体应用，区别于任意广集的指定相等。 *)

(** Retain the chosen alternative and its computational witness. *)

(** 保留所选分支及其计算见证。 *)

Definition Decision (P : Type)
  : Type
  := P ∨ ¬ P.

(** Transfer a decision across two constructive implication maps. Their
    witness universes remain independent. *)

(** 沿两条构造性蕴含映射传递判定；两边见证的宇宙保持独立。 *)

Definition decision_iff {P Q : Type} (h : P ↔ Q) (d : Decision Q)
  : Decision P.
Proof.
  destruct d as [q | n].
  - left. exact (snd h q).
  - right. intros p. exact (n (fst h p)).
Defined.

(** Use a standard-library decision for a Prop-valued proposition. *)

(** 使用标准库对 Prop 值命题的判定。 *)

Definition decision_of_sumbool {P : Prop} (d : {P} + {~ P})
  : Decision P.
Proof.
  destruct d as [p | n].
  - left. exact p.
  - right. intros p. destruct (n p).
Defined.

(** Expose a Prop-valued decision to standard-library algorithms. *)

(** 将 Prop 值判定提供给标准库算法。 *)

Definition decision_to_sumbool {P : Prop} (d : Decision P)
  : {P} + {~ P}.
Proof.
  destruct d as [p | n].
  - left. exact p.
  - right. intros p. destruct (n p).
Defined.

(** Native equality transport is injective along every path, by equality
    elimination. No uniqueness of paths is required. *)

(** 沿任意路径的原生相等输运都是单射，由相等消去证明，无须路径唯一性。 *)

Definition native_transport_injective {I : Type} (F : I → Type)
    (i j : I) (p : i = j) (x y : F i)
    (h : eq_rect i F x j p = eq_rect i F y j p)
  : x = y.
Proof. destruct p. exact h. Defined.

(** Decidable index equality makes packing into a dependent sum injective
    within each fiber. Project both packed values back to the chosen fiber
    with the same decision. A reflexive decision may carry any path;
    transport injectivity cancels that path without postulating UIP. *)

(** 索引相等可判定时，打包到依赖和在每个纤维上是单射。使用同一个判定将
    两个打包值投影回所选纤维。自反判定可以携带任意路径；输运单射性消去该
    路径，无须假定 UIP。 *)

Definition decidable_fiber_injective {I : Type}
    (d : ∀ i j : I, Decision (i = j))
    (F : I → Type) (i : I) (x y : F i)
    (h : existT F i x = existT F i y)
  : x = y.
Proof.
  pose (project := λ z : sigT F,
    match d i (projT1 z) with
    | inl p => eq_rect (projT1 z) F (projT2 z) i (eq_sym p)
    | inr _ => x
    end).
  pose proof (f_equal project h) as q.
  unfold project in q. cbn in q.
  destruct (d i i) as [p | n].
  - exact (native_transport_injective F i i (eq_sym p) x y q).
  - destruct (n eq_refl).
Defined.
