From Cats Require Export
  Cat.Monad.Core.
From Cats Require Import
  Cat.Adjunction.

Local Open Scope monad_scope.

(** * The Monad Induced by an Adjunction

    The right adjoint after the left adjoint is the endofunctor. The unit
    is the existing adjunction unit, and multiplication is the counit
    whiskered on both sides. Monad laws are consequences of naturality
    and the two triangle equations, without additional assumptions. *)

(** * 伴随诱导的 Monad

    底层自函子先作用左伴随，再作用右伴随。单位取已有伴随单位，乘法是余单位的
    双侧须化。Monad 定律由自然性及两条三角形方程导出，不增加假设。 *)

Section InducedMonad.
Context {C D : Cat}
  {F : Fct C D} {U : Fct D C}
  (A : F ⊣ U).

(** Reindex the whiskered counit to the ordinary composite source.
    Source and target functors have the same actions here; the naturality
    witness is reused without identifying their proof-bearing records. *)

(** 将须化后的余单位写在通常的复合来源上。此处来源、目标函子的作用相同，
    自然性见证直接复用，不等同含证明的函子记录。 *)

Program Definition AdjMonadMul
  : (U ∘F F) ∘F (U ∘F F) ⇒ U ∘F F
  :=
  {|nt X := (U ∘Nl (adj_counit A ∘Nr F)) X
  |}.
Next Obligation.
  exact (nat_naturality (U ∘Nl (adj_counit A ∘Nr F)) f).
Qed.

(** Every chosen ordinary adjunction supplies an actual monad. The first
    unit law uses the right triangle; the second uses the image of the
    left triangle. Associativity is counit naturality. *)

(** 每个选定普通伴随给出实际 Monad。第一条单位律使用右三角形，第二条使用
    左三角形的像，结合律就是余单位自然性。 *)

Program Definition AdjMonad
  : Monad C
  := MakeMonad (U ∘F F)
    {|monad_unit := adj_unit A
    ; monad_mul := AdjMonadMul
    ; isMonad :=
        {|monad_unit_l_component := _
        ; monad_unit_r_component := _
        ; monad_assoc_component := _
        |}
    |}.
Next Obligation. exact (adj_triangle_r A (F X)). Qed.
Next Obligation.
  change (fmap U (adj_counit A (F X))
      ∘ fmap U (fmap F (adj_unit A X))
    ≈ id).
  rewrite <- fmap_comp, (adj_triangle_l A X).
  apply fmap_id.
Qed.
Next Obligation.
  change (fmap U (adj_counit A (F X))
      ∘ fmap U (adj_counit A (F (U (F X))))
    ≈ fmap U (adj_counit A (F X))
      ∘ fmap U (fmap F (fmap U (adj_counit A (F X))))).
  rewrite <- !fmap_comp. apply fmap_proper.
  symmetry. exact (nat_naturality (adj_counit A)
    (adj_counit A (F X))).
Qed.

(** The multiplication computes to the image of a counit component. *)

(** 乘法计算为余单位分量的像。 *)

Lemma adj_monad_mul (X : C)
  : μ[AdjMonad] X ≈ fmap U (adj_counit A (F X)).
Proof. reflexivity. Qed.

End InducedMonad.
