From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Product.
From Cats Require Export Cat.Exponential.

(** * The Exponential Bifunctor

    Exponentiation is contravariant in its argument and covariant in its
    result. Only chosen products and exponentials are required. *)

(** * 指数双函子

    指数在参数上反变，在结果上协变；仅要求选定的积与指数对象。 *)

Section ExponentialBifunctor.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Change the argument by precomposition and the result by postcomposition,
    using the exponential universal property. *)

(** 通过指数泛性质，将参数预合成与结果后合成提升到指数对象之间。 *)

Definition exponential_dimap {X X' Y Y'} (u : Hom X' X) (v : Hom Y Y')
  : Hom (Y ^ X) (Y' ^ X')
  := ƛ (v ∘ eval ∘ (id × u)).

Notation "v '^' u" := (exponential_dimap u v)
  (at level 30, right associativity) : hom_scope.

(** Changing either map by its specified equality preserves the induced map. *)

(** 任一侧映射按指定相等改变时，诱导的指数映射仍相等。 *)

Global Instance exponential_dimap_proper {X X' Y Y'}
  : Proper (@HomEq[X', X] ==> @HomEq[Y, Y'] ==>
      @HomEq[Y ^ X, Y' ^ X']) exponential_dimap.
Proof.
  intros u u' Hu v v' Hv. unfold exponential_dimap.
  rewrite Hu, Hv. reflexivity.
Qed.

(** Evaluation computes the two-variable action. Contravariance in the
    argument is expressed by precomposition on the right-hand input. *)

(** 求值给出双变量作用的计算律；参数反变通过右侧输入上的预合成表达。 *)

Lemma exponential_dimap_eval {X X' Y Y'}
    (u : Hom X' X) (v : Hom Y Y')
  : eval ∘ ((v ^ u) × id) ≈ v ∘ eval ∘ (id × u).
Proof. apply exponential_β. Qed.

(** With the argument map fixed to identity, recover the existing covariant
    action on result objects. *)

(** 参数映射取恒等时，恢复已有的结果对象协变作用。 *)

Lemma exponential_dimap_id_r {X Y Y'} (v : Hom Y Y')
  : v ^ (@id X) ≈ exponential_map v.
Proof.
  unfold exponential_dimap, exponential_map.
  rewrite cross_id, comp_id_r. reflexivity.
Qed.

(** The two identity maps induce the identity on the exponential object. *)

(** 两侧恒等映射诱导指数对象上的恒等映射。 *)

Lemma exponential_dimap_id {X Y}
  : (@id Y) ^ (@id X) ≈ @id (Y ^ X).
Proof. rewrite exponential_dimap_id_r. apply exponential_map_id. Qed.

(** Uncurrying commutes with changing the argument and result objects. *)

(** 反柯里化与参数对象及结果对象的变换相容。 *)

Lemma exponential_uncurry_dimap {X X' Y Y' Z}
    (u : Hom X' X) (v : Hom Y Y') (g : Hom Z (Y ^ X))
  : uncurry ((v ^ u) ∘ g) ≈ v ∘ uncurry g ∘ (id × u).
Proof.
  rewrite exponential_uncurry_comp_r.
  unfold exponential_dimap. rewrite exponential_β. unfold uncurry.
  rewrite !comp_assoc, <- !cross_comp, !comp_id_l, !comp_id_r.
  reflexivity.
Qed.

(** Currying commutes with changing the argument and result objects. *)

(** 柯里化与参数对象及结果对象的变换相容。 *)

Lemma exponential_curry_dimap {X X' Y Y' Z}
    (u : Hom X' X) (v : Hom Y Y') (f : Hom (Z × X) Y)
  : ƛ (v ∘ f ∘ (id × u)) ≈ (v ^ u) ∘ ƛ f.
Proof.
  symmetry. apply exponential_curry_unique.
  change (uncurry ((v ^ u) ∘ ƛ f) ≈ v ∘ f ∘ (id × u)).
  rewrite exponential_uncurry_dimap, exponential_β. reflexivity.
Qed.

(** Composition reverses in the argument and preserves order in the result. *)

(** 复合在参数侧反向，在结果侧保持顺序。 *)

Lemma exponential_dimap_comp {X X' X'' Y Y' Y''}
    (u : Hom X' X) (u' : Hom X'' X')
    (v : Hom Y Y') (v' : Hom Y' Y'')
  : (v' ∘ v) ^ (u ∘ u') ≈ (v' ^ u') ∘ (v ^ u).
Proof.
  symmetry. apply exponential_curry_unique.
  change (uncurry ((v' ^ u') ∘ (v ^ u)) ≈
    (v' ∘ v) ∘ eval ∘ (id × (u ∘ u'))).
  rewrite exponential_uncurry_dimap.
  unfold exponential_dimap. rewrite exponential_β.
  rewrite !comp_assoc, <- cross_comp, comp_id_l. reflexivity.
Qed.

(** Application computes argument precomposition and result postcomposition
    in a shared context. *)

(** 在共同上下文中，应用按参数预合成和结果后合成计算。 *)

Lemma exponential_app_dimap {X X' Y Y' Z}
    (u : Hom X' X) (v : Hom Y Y')
    (g : Hom Z (Y ^ X)) (a : Hom Z X')
  : app ((v ^ u) ∘ g) a ≈ v ∘ app g (u ∘ a).
Proof.
  unfold app.
  transitivity ((eval ∘ ((v ^ u) × id)) ∘ ⟨g, a⟩).
  - rewrite comp_assoc, product_comp_l, comp_id_l. reflexivity.
  - rewrite exponential_dimap_eval, !comp_assoc,
      product_comp_l, comp_id_l. reflexivity.
Qed.

(** Bundle the two-variable action as a functor on the product category. *)

(** 将双变量作用组装为乘积范畴上的函子。 *)

Program Definition ExponentialBiF
  : Functor (C^op ×C C) C
  :=
  {|F0 p := (snd p ^ fst p)%ob
  ; F1 X Y f := (snd f ^ fst f)%hom
  |}.
Next Obligation.
  intros [u v] [u' v'] [Hu Hv]. apply exponential_dimap_proper; assumption.
Qed.
Next Obligation. apply exponential_dimap_id. Qed.
Next Obligation. apply exponential_dimap_comp. Qed.

(** Fix the result object to obtain contravariant exponentiation. *)

(** 固定结果对象，得到反变指数函子。 *)

Definition ExponentialContraF (Y : @Ob C)
  : Functor (C^op) C
  := π1F ExponentialBiF Y.

(** Fixing the argument gives the existing covariant exponential functor,
    compared by identity components and specified morphism equality. *)

(** 固定参数后，以恒等分量及指定态射相等比较双函子的截面与已有协变指数函子。 *)

Program Definition ExponentialFixedN (X : @Ob C)
  : π2F ExponentialBiF X ⇒ ExponentialF X
  :=
  {|nt Y := id
  |}.
Next Obligation.
  rewrite comp_id_l, comp_id_r. apply exponential_dimap_id_r.
Qed.

(** The comparison has invertible identity components; no equality of
    functor records or their law fields is required. *)

(** 比较的恒等分量可逆，不要求函子记录或其定律字段相等。 *)

Definition exponential_fixed_nat_iso (X : @Ob C)
  : π2F ExponentialBiF X ≅N ExponentialF X.
Proof.
  exists (ExponentialFixedN X). intros Y.
  exists id. split; apply comp_id_l.
Defined.

End ExponentialBifunctor.

Notation "v '^' u" := (exponential_dimap u v)
  (at level 30, right associativity) : hom_scope.
Notation "'(-^-)'" := ExponentialBiF : cat_scope.
Notation "'(' Y '^-)'" := (ExponentialContraF Y) : cat_scope.
