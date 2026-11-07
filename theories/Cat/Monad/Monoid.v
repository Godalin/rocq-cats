From Cats Require Export
  Cat.Monad.Category
  Cat.Monoidal.Monoid
  Cat.Monoidal.Endomorphism.
From Cats Require Import
  Cat.Bicategory.Core
  Cat.Bicategory.Cat
  Cat.CatCat.

Local Open Scope monad_scope.
Local Open Scope monoidal_scope.

(** * The Monoid-Object Characterization of Monads

    The ordinary axioms and the monoid diagrams are equivalent for fixed
    data. The conversions preserve the endofunctor and both natural
    transformations by computation; law witnesses are never compared. *)

(** * Monad 的幺半群对象刻画

    对固定数据，通常公理与幺半群交换图表等价。双向转换通过计算保持自函子和
    两个自然变换，从不比较定律见证。 *)

(** For an arbitrary bicategory, the associator and unitors are essential
    parts of the monad laws, so the structural presentation is retained. *)

(** 任意双范畴中，结合子和单位子是 Monad 定律的必要组成，因此保留结构呈现。 *)

Definition BicatMonad (B : Bicat) (X : ObB B)
  : Type
  := MonoidObject (EndoMonoidal B X).

(** Composition is the tensor of endofunctors; the identity is its unit. *)

(** 复合是自函子的张量，恒等函子是其单位。 *)

Definition EndofunctorMonoidal (C : Cat)
  : MonoidalCategory (Fct C C)
  := EndoMonoidal CatBicat C.

(** Constructive equivalence of laws for the same [T], [η] and [μ]. The
    only extra factors in the monoid diagrams are canonical identities. *)

(** 同一组 [T]、[η]、[μ] 上定律的构造性等价；幺半群交换图表只额外含有
    规范恒等因子。 *)

Theorem monad_monoid_laws {C : Cat} (T : Functor C C)
    (η : IdF ⇒ T) (μ : T ∘F T ⇒ T)
  : is_monad T η μ ↔ is_monoid_object (EndofunctorMonoidal C) T η μ.
Proof.
  split; intros [Hu [Hv Ha]]; (split; [| split]); intros X.
  - change (μ X ∘ (η (T X) ∘ id) ≈ id).
    rewrite comp_id_r. apply Hu.
  - change (μ X ∘ (id ∘ fmap T (η X)) ≈ id).
    rewrite comp_id_l. apply Hv.
  - change (μ X ∘ (μ (T X) ∘ fmap T (fmap T id)) ≈
      (μ X ∘ (id ∘ fmap T (μ X))) ∘ id).
    rewrite !functor_id, !comp_id_l, !comp_id_r. apply Ha.
  - specialize (Hu X).
    change (μ X ∘ (η (T X) ∘ id) ≈ id) in Hu.
    rewrite comp_id_r in Hu. exact Hu.
  - specialize (Hv X).
    change (μ X ∘ (id ∘ fmap T (η X)) ≈ id) in Hv.
    rewrite comp_id_l in Hv. exact Hv.
  - specialize (Ha X).
    change (μ X ∘ (μ (T X) ∘ fmap T (fmap T id)) ≈
      (μ X ∘ (id ∘ fmap T (μ X))) ∘ id) in Ha.
    rewrite !functor_id, !comp_id_l, !comp_id_r in Ha. exact Ha.
Defined.

(** Regard an ordinary monad as a monoid, reusing the fixed-data theorem. *)

(** 复用固定数据上的定理，将普通 Monad 看作幺半群对象。 *)

Program Definition MonadMonoid {C : Cat} (M : Monad C)
  : MonoidObject (EndofunctorMonoidal C)
  :=
  {|MonoidCarrier := T[M]
  ; monoid_object_unit := η[M]
  ; monoid_object_mul := μ[M]
  |}.
Next Obligation.
  exact (fst (fst (monad_monoid_laws _ _ _) (monad_axioms M))).
Defined.
Next Obligation.
  exact (fst (snd (fst (monad_monoid_laws _ _ _) (monad_axioms M)))).
Defined.
Next Obligation.
  exact (snd (snd (fst (monad_monoid_laws _ _ _) (monad_axioms M)))).
Defined.

(** Recover the ordinary axioms from a monoid, preserving all its data. *)

(** 从幺半群对象恢复通常公理，保持全部数据。 *)

Program Definition MonoidMonad {C : Cat}
    (A : MonoidObject (EndofunctorMonoidal C))
  : Monad C
  :=
  {|MonadF := MonoidCarrier A
  ; monad_unit := e[A]
  ; monad_mul := m[A]
  ; monad_axioms := snd (monad_monoid_laws _ _ _) (monoid_object_laws A)
  |}.

(** The two independently stated preservation predicates coincide on the
    same natural transformation. Both directions retain the witnesses. *)

(** 两个独立陈述的保持性谓词在同一自然变换上一致；双向映射均保留见证。 *)

Theorem monad_monoid_hom {C : Cat} (M N : Monad C)
    (α : T[M] ⇒ T[N])
  : is_monad_hom M N α ↔ is_monoid_hom (MonadMonoid M) (MonadMonoid N) α.
Proof. split; intros H; exact H. Defined.

(** The structure conversion acts identically on underlying transformations. *)

(** 结构转换在底层自然变换上取恒等作用。 *)

Program Definition MonadMonoidF (C : Cat)
  : Functor (MonadCat C) (MonoidCat (EndofunctorMonoidal C))
  :=
  {|F0 := MonadMonoid
  ; F1 M N α := α
  |}.
Next Obligation. intros α β E. exact E. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Recover ordinary monads and the same underlying homomorphisms. *)

(** 恢复普通 Monad 及底层相同的同态。 *)

Program Definition MonoidMonadF (C : Cat)
  : Functor (MonoidCat (EndofunctorMonoidal C)) (MonadCat C)
  :=
  {|F0 := MonoidMonad
  ; F1 A B α := α
  |}.
Next Obligation. intros α β E. exact E. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** The Monad round trip has identity components: its operations are
    computationally unchanged, even though its law witnesses may differ. *)

(** Monad 往返比较的分量为恒等态射：运算的计算保持不变，定律见证则可以不同。 *)

Program Definition MonadMonoidRoundtripN (C : Cat)
  : (MonoidMonadF C ∘F MonadMonoidF C) ⇒ (@IdF (MonadCat C))
  :=
  {|nt M := monad_hom_id M
  |}.
Next Obligation.
  intros Z. cbn. rewrite comp_id_l, comp_id_r. reflexivity.
Defined.

(** The Monad round trip is naturally isomorphic to the identity. This
    specifies structural comparison without native equality of records. *)

(** Monad 往返自然同构于恒等函子；这给出结构比较，不使用记录原生相等。 *)

Definition monad_monoid_roundtrip_iso (C : Cat)
  : (MonoidMonadF C ∘F MonadMonoidF C) ≅N (@IdF (MonadCat C)).
Proof.
  exists (MonadMonoidRoundtripN C). intros M.
  exists (monad_hom_id M). split; intros X; apply comp_id_l.
Defined.

(** The monoid round trip also preserves carrier and operations, with
    identity homomorphisms as its natural comparison. *)

(** 幺半群往返也保持载体及运算，其自然比较由恒等同态组成。 *)

Program Definition MonoidMonadRoundtripN (C : Cat)
  : (MonadMonoidF C ∘F MonoidMonadF C) ⇒
      (@IdF (MonoidCat (EndofunctorMonoidal C)))
  :=
  {|nt A := monoid_hom_id A
  |}.
Next Obligation.
  intros Z. cbn. rewrite comp_id_l, comp_id_r. reflexivity.
Defined.

(** The monoid round trip is naturally isomorphic to the identity. *)

(** 幺半群往返自然同构于恒等函子。 *)

Definition monoid_monad_roundtrip_iso (C : Cat)
  : (MonadMonoidF C ∘F MonoidMonadF C) ≅N
      (@IdF (MonoidCat (EndofunctorMonoidal C))).
Proof.
  exists (MonoidMonadRoundtripN C). intros A.
  exists (monoid_hom_id A). split; intros X; apply comp_id_l.
Defined.

(** Ordinary monads are equivalent to monoid objects in the endofunctor
    monoidal category, on objects and fixed-base morphisms. *)

(** 普通 Monad 在对象及固定基底态射层面等价于自函子幺半范畴中的幺半群对象。 *)

Definition monad_monoid_equiv (C : Cat)
  : MonadCat C ≃C MonoidCat (EndofunctorMonoidal C)
  := (MonadMonoidF C; (MonoidMonadF C;
      (monad_monoid_roundtrip_iso C, monoid_monad_roundtrip_iso C))).
