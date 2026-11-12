From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Transport.
From Cats Require Export
  Cat.Exponential.Core.

(** * Internal Identities and Composition *)

(** * 内部恒等与复合 *)

(** Fix selected binary products and exponentials on a category. Develop
    internal identities, composition and evaluation; terminal objects are
    added only for the final unit diagrams. *)

(** 固定范畴上的选定二元积与指数，发展内部恒等、复合及求值；仅在最后的
    单位图中增加终对象。 *)

Section InternalHom.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Identity function in an arbitrary context. With a terminal context this
    is the internal identity [1 → X^X]; no terminal object is needed here. *)

(** 任意上下文中的恒等函数。在终上下文中它为内部恒等 [1 → X^X]；此处不需要
    终对象。 *)

Definition exponential_id (X : @Ob C) {W : @Ob C}
  : Hom W (X ^ X)
  := ƛ π2.

Notation "'idᴱ[' X ']'" := (exponential_id X) : hom_scope.

(** Internal composition is abstraction over two successive applications. *)

(** 内部复合为两次连续应用的抽象。 *)

Definition internal_comp (X Y Z : @Ob C)
  : Hom ((Z ^ Y) × (Y ^ X)) (Z ^ X)
  := ƛ (app (π1 ∘ π1) (app (π2 ∘ π1) π2)).

(** Compose exponential-valued arrows sharing the same context. *)

(** 复合共享上下文的指数值箭头。 *)

Definition exponential_comp {W X Y Z : @Ob C}
    (g : Hom W (Z ^ Y)) (f : Hom W (Y ^ X))
  : Hom W (Z ^ X)
  := internal_comp X Y Z ∘ ⟨g, f⟩.

Infix "∘ᴱ" := exponential_comp
  (at level 40, left associativity) : hom_scope.

(** Contextual composition preserves the specified equality of both maps. *)

(** 上下文复合保持两个映射的指定相等。 *)

Global Instance exponential_comp_proper {W X Y Z : @Ob C}
  : Proper (@HomEq[W, Z ^ Y] ==> @HomEq[W, Y ^ X] ==>
      @HomEq[W, Z ^ X]) exponential_comp.
Proof. intros g g' H f f' K. unfold exponential_comp. rewrite H, K. reflexivity. Qed.

(** Internal identities compute on arguments. *)

(** 内部恒等在参数上按预期计算。 *)

Lemma exponential_id_app {W X : @Ob C} (a : Hom W X)
  : app idᴱ[X] a ≈ a.
Proof. unfold exponential_id. rewrite exponential_app_β, product_β2. reflexivity. Qed.

(** Internal identities are invariant under context substitution. *)

(** 内部恒等在上下文替换下保持不变。 *)

Lemma exponential_id_comp {W V X : @Ob C} (σ : Hom V W)
  : (idᴱ[X] : Hom W (X ^ X)) ∘ σ ≈ idᴱ[X].
Proof.
  unfold exponential_id. rewrite <- exponential_curry_comp_r.
  apply exponential_curry_proper.
  rewrite cross_η, product_β2, comp_id_l. reflexivity.
Qed.

(** Application of internal composition computes as successive application. *)

(** 内部复合的应用计算为连续应用。 *)

Lemma exponential_comp_app {W X Y Z : @Ob C}
    (g : Hom W (Z ^ Y)) (f : Hom W (Y ^ X)) (a : Hom W X)
  : app (g ∘ᴱ f) a ≈ app g (app f a).
Proof.
  unfold exponential_comp, internal_comp.
  rewrite <- exponential_curry_comp_r, exponential_app_β.
  repeat first [rewrite exponential_app_comp | rewrite product_comp_l |
    rewrite product_comp_r | rewrite comp_assoc |
    rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r].
  reflexivity.
Qed.

(** Composition commutes with changing the shared context. *)

(** 复合与共享上下文的变换交换。 *)

Lemma exponential_comp_sub {W V X Y Z : @Ob C}
    (g : Hom W (Z ^ Y)) (f : Hom W (Y ^ X)) (σ : Hom V W)
  : (g ∘ᴱ f) ∘ σ ≈ (g ∘ σ) ∘ᴱ (f ∘ σ).
Proof. unfold exponential_comp. rewrite comp_assoc, product_comp_r. reflexivity. Qed.

(** Internal identity is a left unit in every context. *)

(** 内部恒等在每个上下文中为左单位。 *)

Lemma exponential_comp_id_l {W X Y : @Ob C} (f : Hom W (Y ^ X))
  : idᴱ[Y] ∘ᴱ f ≈ f.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app,
    exponential_comp_sub, exponential_comp_app, exponential_id_comp,
    exponential_id_app. reflexivity.
Qed.

(** Internal identity is a right unit in every context. *)

(** 内部恒等在每个上下文中为右单位。 *)

Lemma exponential_comp_id_r {W X Y : @Ob C} (f : Hom W (Y ^ X))
  : f ∘ᴱ idᴱ[X] ≈ f.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app,
    exponential_comp_sub, exponential_comp_app, exponential_id_comp,
    exponential_id_app. reflexivity.
Qed.

(** Associativity follows from the application equation and exponential
    extensionality, without equality of functions. *)

(** 结合律来自应用方程及指数外延性，不使用函数原生相等。 *)

Lemma exponential_comp_assoc {W X Y Z T : @Ob C}
    (h : Hom W (T ^ Z)) (g : Hom W (Z ^ Y)) (f : Hom W (Y ^ X))
  : (h ∘ᴱ g) ∘ᴱ f ≈ h ∘ᴱ (g ∘ᴱ f).
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app,
    !exponential_comp_sub, !exponential_comp_app. reflexivity.
Qed.

(** The internal arrow is its contextual composition on the two projections. *)

(** 内部箭头为两个投影的上下文复合。 *)

Lemma internal_comp_eq (X Y Z : @Ob C)
  : internal_comp X Y Z ≈ (π1 ∘ᴱ π2).
Proof. unfold exponential_comp. rewrite product_pair_η, comp_id_r. reflexivity. Qed.

(** Evaluating internal composition is successive evaluation, with the
    selected product associator accounting for the three inputs. *)

(** 内部复合的求值是连续求值，选定的积结合子处理三个输入的括号。 *)

Lemma internal_comp_eval (X Y Z : @Ob C)
  : (eval (X := X) (Y := Z)) ∘ (internal_comp X Y Z × id) ≈
      (eval (X := Y) (Y := Z)) ∘ (id × (eval (X := X) (Y := Y))) ∘
        (@product_assoc C HP (Z ^ Y) (Y ^ X) X).1.
Proof.
  change (uncurry (internal_comp X Y Z) ≈
    (eval (X := Y) (Y := Z)) ∘ (id × (eval (X := X) (Y := Y))) ∘
      (@product_assoc C HP (Z ^ Y) (Y ^ X) X).1).
  unfold internal_comp. rewrite exponential_β.
  unfold app, product_assoc. cbn [projT1].
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r].
  reflexivity.
Qed.

(** The internal composition diagram explicitly includes the associator. *)

(** 内部复合图显式包含结合同构。 *)

Lemma internal_comp_assoc (X Y Z T : @Ob C)
  : internal_comp X Y T ∘ (internal_comp Y Z T × id) ≈
      internal_comp X Z T ∘ (id × internal_comp X Y Z) ∘
        (@product_assoc C HP (T ^ Z) (Z ^ Y) (Y ^ X)).1.
Proof.
  rewrite (internal_comp_eq X Z T), (internal_comp_eq X Y T),
    !exponential_comp_sub.
  unfold product_assoc. cbn [projT1].
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r].
  rewrite (internal_comp_eq Y Z T), (internal_comp_eq X Y Z),
    !exponential_comp_sub.
  repeat first [rewrite product_comp_r | rewrite comp_assoc |
    rewrite product_β1 | rewrite product_β2].
  apply exponential_comp_assoc.
Qed.

(** The left unit diagram uses the projection unitor [1 × (Y^X) → Y^X]. *)

(** 左单位图使用投影单位同构 [1 × (Y^X) → Y^X]。 *)

Lemma internal_comp_id_l `{HT : !HasTerminal C} (X Y : @Ob C)
  : internal_comp X Y Y ∘ ((idᴱ[Y] : Hom 1 (Y ^ Y)) × id) ≈ π2.
Proof.
  rewrite internal_comp_eq, exponential_comp_sub.
  repeat first [rewrite cross_η | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l].
  rewrite exponential_id_comp. apply exponential_comp_id_l.
Qed.

(** The right unit diagram uses the projection unitor [(Y^X) × 1 → Y^X]. *)

(** 右单位图使用投影单位同构 [(Y^X) × 1 → Y^X]。 *)

Lemma internal_comp_id_r `{HT : !HasTerminal C} (X Y : @Ob C)
  : internal_comp X X Y ∘ (id × (idᴱ[X] : Hom 1 (X ^ X))) ≈ π1.
Proof.
  rewrite internal_comp_eq, exponential_comp_sub.
  repeat first [rewrite cross_η | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l].
  rewrite exponential_id_comp. apply exponential_comp_id_r.
Qed.

End InternalHom.

Notation "'idᴱ[' X ']'" := (exponential_id X) : hom_scope.
Infix "∘ᴱ" := exponential_comp
  (at level 40, left associativity) : hom_scope.
