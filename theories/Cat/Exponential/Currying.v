From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Exponential.Core.

(** * Iterated Transposition *)

(** * 迭代转置 *)

Section IteratedCurrying.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Transpose two arguments, retaining the explicit permutation from
    [(Z × B) × A] to [Z × (A × B)]. *)

(** 转置两个参数，保留从 [(Z × B) × A] 到 [Z × (A × B)] 的显式置换。 *)

Definition exponential_curry_twice {A B Y Z : @Ob C}
    (f : Hom (Z × (A × B)) Y)
  : Hom Z ((Y ^ A) ^ B)
  := ƛ (ƛ (f ∘ (@product_exchange C HP Z B A).1)).

Notation "'ƛ₂' f" := (exponential_curry_twice f)
  (at level 35) : hom_scope.

(** Evaluate two arguments and return them to the product order. *)

(** 求值两个参数，并将其恢复到积的顺序。 *)

Definition exponential_uncurry_twice {A B Y Z : @Ob C}
    (g : Hom Z ((Y ^ A) ^ B))
  : Hom (Z × (A × B)) Y
  := uncurry (uncurry g) ∘ (@product_exchange C HP Z B A).2.1.

Notation "f '^♭₂'" := (exponential_uncurry_twice f)
  (at level 35) : hom_scope.

(** Iterated abstraction preserves specified arrow equality. *)

(** 迭代抽象保持指定箭头相等。 *)

Global Instance exponential_curry_twice_proper {A B Y Z : @Ob C}
  : Proper (@HomEq[Z × (A × B), Y] ==>
      @HomEq[Z, (Y ^ A) ^ B]) exponential_curry_twice.
Proof. intros f g H. unfold exponential_curry_twice. rewrite H. reflexivity. Qed.

(** Iterated evaluation preserves specified arrow equality. *)

(** 迭代求值保持指定箭头相等。 *)

Global Instance exponential_uncurry_twice_proper {A B Y Z : @Ob C}
  : Proper (@HomEq[Z, (Y ^ A) ^ B] ==>
      @HomEq[Z × (A × B), Y]) exponential_uncurry_twice.
Proof. intros f g H. unfold exponential_uncurry_twice. rewrite H. reflexivity. Qed.

(** Double evaluation cancels double abstraction. *)

(** 双重求值消去双重抽象。 *)

Lemma exponential_curry_twice_β {A B Y Z : @Ob C}
    (f : Hom (Z × (A × B)) Y)
  : (ƛ₂ f)^♭₂ ≈ f.
Proof.
  unfold exponential_curry_twice, exponential_uncurry_twice.
  rewrite !exponential_β, comp_assoc,
    (snd (@product_exchange C HP Z B A).2.2), comp_id_r. reflexivity.
Qed.

(** Double abstraction cancels double evaluation. *)

(** 双重抽象消去双重求值。 *)

Lemma exponential_curry_twice_η {A B Y Z : @Ob C}
    (g : Hom Z ((Y ^ A) ^ B))
  : ƛ₂ (g^♭₂) ≈ g.
Proof.
  unfold exponential_curry_twice, exponential_uncurry_twice.
  rewrite comp_assoc, (fst (@product_exchange C HP Z B A).2.2),
    comp_id_r, !exponential_η. reflexivity.
Qed.

(** Double evaluation detects equations between iterated exponential maps. *)

(** 双重求值检测迭代指数映射之间的等式。 *)

Lemma exponential_uncurry_twice_ext {A B Y Z : @Ob C}
    (f g : Hom Z ((Y ^ A) ^ B)) (H : f^♭₂ ≈ g^♭₂)
  : f ≈ g.
Proof.
  rewrite <- (exponential_curry_twice_η f),
    <- (exponential_curry_twice_η g), H. reflexivity.
Qed.

(** Double evaluation commutes with a change of context. *)

(** 双重求值与上下文变换交换。 *)

Lemma exponential_uncurry_twice_comp {A B Y Z W : @Ob C}
    (g : Hom Z ((Y ^ A) ^ B)) (σ : Hom W Z)
  : (g ∘ σ)^♭₂ ≈ g^♭₂ ∘ (σ × id).
Proof.
  unfold exponential_uncurry_twice.
  rewrite !exponential_uncurry_comp_r, comp_assoc,
    product_exchange_inv_natural, cross_id, <- comp_assoc. reflexivity.
Qed.

(** Flatten two exponential arguments into a product argument. *)

(** 将两个指数参数展平为一个积参数。 *)

Definition exponential_flatten {A B Y Z : @Ob C}
    (g : Hom Z ((Y ^ A) ^ B))
  : Hom Z (Y ^ (A × B))
  := ƛ (g^♭₂).

(** Expand a product argument into two exponential arguments. *)

(** 将积参数展开为两个指数参数。 *)

Definition exponential_expand {A B Y Z : @Ob C}
    (g : Hom Z (Y ^ (A × B)))
  : Hom Z ((Y ^ A) ^ B)
  := ƛ₂ (uncurry g).

(** Flattening preserves hom equality. *)

(** 展平保持 Hom 相等。 *)

Global Instance exponential_flatten_proper {A B Y Z : @Ob C}
  : Proper (@HomEq[Z, (Y ^ A) ^ B] ==> @HomEq[Z, Y ^ (A × B)])
      exponential_flatten.
Proof. intros f g H. unfold exponential_flatten. rewrite H. reflexivity. Qed.

(** Expanding preserves hom equality. *)

(** 展开保持 Hom 相等。 *)

Global Instance exponential_expand_proper {A B Y Z : @Ob C}
  : Proper (@HomEq[Z, Y ^ (A × B)] ==> @HomEq[Z, (Y ^ A) ^ B])
      exponential_expand.
Proof. intros f g H. unfold exponential_expand. rewrite H. reflexivity. Qed.

(** Expanding after flattening recovers the arrow. *)

(** 展平后展开恢复原箭头。 *)

Lemma exponential_flatten_β {A B Y Z : @Ob C}
    (g : Hom Z ((Y ^ A) ^ B))
  : exponential_expand (exponential_flatten g) ≈ g.
Proof.
  unfold exponential_expand, exponential_flatten.
  rewrite exponential_β. apply exponential_curry_twice_η.
Qed.

(** Flattening after expanding recovers the arrow. *)

(** 展开后展平恢复原箭头。 *)

Lemma exponential_flatten_η {A B Y Z : @Ob C}
    (g : Hom Z (Y ^ (A × B)))
  : exponential_flatten (exponential_expand g) ≈ g.
Proof.
  unfold exponential_expand, exponential_flatten.
  rewrite exponential_curry_twice_β. apply exponential_η.
Qed.

(** Flattening is natural in the context. *)

(** 展平在上下文上自然。 *)

Lemma exponential_flatten_comp {A B Y Z W : @Ob C}
    (g : Hom Z ((Y ^ A) ^ B)) (σ : Hom W Z)
  : exponential_flatten (g ∘ σ) ≈ exponential_flatten g ∘ σ.
Proof.
  unfold exponential_flatten. rewrite exponential_uncurry_twice_comp.
  apply exponential_curry_comp_r.
Qed.

(** Expanding is natural in the context. *)

(** 展开在上下文上自然。 *)

Lemma exponential_expand_comp {A B Y Z W : @Ob C}
    (g : Hom Z (Y ^ (A × B))) (σ : Hom W Z)
  : exponential_expand (g ∘ σ) ≈ exponential_expand g ∘ σ.
Proof.
  apply exponential_uncurry_twice_ext.
  unfold exponential_expand at 1.
  rewrite exponential_curry_twice_β, exponential_uncurry_twice_comp.
  unfold exponential_expand. rewrite exponential_curry_twice_β.
  apply exponential_uncurry_comp_r.
Qed.

(** The mutually inverse natural hom operations supply the iterated
    exponential isomorphism, with explicit computational arrows. *)

(** 互逆的自然 Hom 操作给出迭代指数同构，并保留显式可计算箭头。 *)

Definition exponential_iterated_iso (A B Y : @Ob C)
  : ((Y ^ A) ^ B) ≅ (Y ^ (A × B)).
Proof.
  exists (exponential_flatten id), (exponential_expand id).
  split; unfold is_linv_of, is_rinv_of.
  - rewrite <- exponential_expand_comp, comp_id_l.
    apply exponential_flatten_β.
  - rewrite <- exponential_flatten_comp, comp_id_l.
    apply exponential_flatten_η.
Defined.

(** The canonical isomorphism implements flattening on every hom-setoid. *)

(** 规范同构在每个 Hom 广集上实现展平。 *)

Lemma exponential_iterated_comp {A B Y Z : @Ob C}
    (g : Hom Z ((Y ^ A) ^ B))
  : (exponential_iterated_iso A B Y).1 ∘ g ≈ exponential_flatten g.
Proof. cbn. rewrite <- exponential_flatten_comp, comp_id_l. reflexivity. Qed.

(** The iterated comparison sends double abstraction to ordinary abstraction. *)

(** 迭代比较将双重抽象送到通常抽象。 *)

Lemma exponential_iterated_curry {A B Y Z : @Ob C}
    (f : Hom (Z × (A × B)) Y)
  : (exponential_iterated_iso A B Y).1 ∘ (ƛ₂ f) ≈ ƛ f.
Proof.
  rewrite exponential_iterated_comp. unfold exponential_flatten.
  rewrite exponential_curry_twice_β. reflexivity.
Qed.

(** Flattening commutes with a map of the result object. *)

(** 展平与结果对象上的映射交换。 *)

Lemma exponential_flatten_map {A B Y Y' Z : @Ob C}
    (f : Hom Y Y') (g : Hom Z ((Y ^ A) ^ B))
  : exponential_flatten
      (exponential_map (X := B) (exponential_map (X := A) f) ∘ g) ≈
      exponential_map (X := A × B) f ∘ exponential_flatten g.
Proof.
  unfold exponential_flatten, exponential_uncurry_twice.
  rewrite <- exponential_curry_comp_l. apply exponential_curry_proper.
  rewrite !exponential_uncurry_comp_l, comp_assoc. reflexivity.
Qed.

(** Natural transformation from iterated to product-argument exponentiation. *)

(** 从迭代指数到积参数指数的自然变换。 *)

Program Definition ExponentialIteratedN (A B : @Ob C)
  : ((-^ B) ∘F (-^ A)) ⇒ (-^ (A × B))
  :=
  {|nt Y := (exponential_iterated_iso A B Y).1
  |}.
Next Obligation.
  change ((exponential_iterated_iso A B Y).1 ∘
    exponential_map (X := B) (exponential_map (X := A) f) ≈
    exponential_map (X := A × B) f ∘ (exponential_iterated_iso A B X).1).
  rewrite exponential_iterated_comp.
  pose proof (exponential_flatten_map f
    (@Cats.Cat.Core.id C ((X ^ A) ^ B))) as H.
  rewrite comp_id_r in H. exact H.
Qed.

(** Iterated currying is a natural isomorphism in the result object. *)

(** 迭代柯里化在结果对象上为自然同构。 *)

Definition exponential_iterated_nat_iso (A B : @Ob C)
  : ((-^ B) ∘F (-^ A)) ≅N (-^ (A × B))
  := (ExponentialIteratedN A B; λ Y, (exponential_iterated_iso A B Y).2).

End IteratedCurrying.

Notation "'ƛ₂' f" := (exponential_curry_twice f)
  (at level 35) : hom_scope.
Notation "f '^♭₂'" := (exponential_uncurry_twice f)
  (at level 35) : hom_scope.
