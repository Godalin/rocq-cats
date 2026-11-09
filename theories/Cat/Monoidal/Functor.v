From Cats Require Export
  Cat.Monoidal.Core.

Local Open Scope monoidal_scope.

(** * Lax Monoidal Functors

    The unit comparison and tensorator point into the image of the source
    unit and tensor. Neither comparison is required to be invertible.
    Tensorial strength is separate structure, not implied by laxness.
    All coherence laws use the target category's designated equality. *)

(** * Lax Monoidal 函子

    单位比较及 tensorator 指向来源单位及张量的像，不要求任何比较可逆。
    张量强度是独立结构，不由 lax 性推出。全部相干律使用目标范畴的指定相等。 *)

(** A functor bundled with a lax structure, relative to the named monoidal
    structures [MC] and [MD]. Its unique coercion exposes the underlying
    functor, so clients can write [L X] and [fmap L f]. A natural
    transformation supplies the tensorator's naturality in both arguments.
    The three remaining
    diagrams retain the chosen associators and unitors explicitly.
    A strong monoidal functor would additionally require invertible
    comparisons; an oplax structure reverses both comparison maps. *)

(** 函子及其相对于具名幺半结构 [MC]、[MD] 的 lax 结构打包在一起；唯一的
    强制转换暴露底层函子，客户端可写 [L X]、[fmap L f]。
    自然变换提供 tensorator 在两个变量上的自然性，另外三幅交换图显式保留
    选定的结合子及单位子。Strong monoidal 函子还须比较可逆，oplax 结构则
    将两个比较映射反向。 *)

Class LaxMonoidalFunctor {C D : Cat}
    (MC : MonoidalCategory C) (MD : MonoidalCategory D)
  :=
  { LaxMonoidalF :> Functor C D
  ; lax_unit : Hom (I⊗[MD]) (LaxMonoidalF (I⊗[MC]))
  ; lax_tensorN : (tensorF MD ∘F (LaxMonoidalF ×F LaxMonoidalF)) ⇒
      (LaxMonoidalF ∘F tensorF MC)
  ; lax_unit_l (X : @Ob C)
    : fmap LaxMonoidalF (@tensor_unit_l C MC X) ∘
        lax_tensorN (I⊗[MC], X) ∘
        (@tensor_map D MD _ _ _ _ lax_unit id) ≈
        @tensor_unit_l D MD (LaxMonoidalF X)
  ; lax_unit_r (X : @Ob C)
    : fmap LaxMonoidalF (@tensor_unit_r C MC X) ∘
        lax_tensorN (X, I⊗[MC]) ∘
        (@tensor_map D MD _ _ _ _ id lax_unit) ≈
        @tensor_unit_r D MD (LaxMonoidalF X)
  ; lax_assoc (X Y Z : @Ob C)
    : fmap LaxMonoidalF (@tensor_assoc C MC X Y Z) ∘
        lax_tensorN (@tensor C MC X Y, Z) ∘
        (@tensor_map D MD _ _ _ _ (lax_tensorN (X, Y)) id) ≈
        lax_tensorN (X, @tensor C MC Y Z) ∘
        (@tensor_map D MD _ _ _ _ id (lax_tensorN (Y, Z))) ∘
        @tensor_assoc D MD
          (LaxMonoidalF X) (LaxMonoidalF Y) (LaxMonoidalF Z)
  }.

Arguments LaxMonoidalF {_ _ _ _} _.
Arguments lax_unit {_ _ _ _} _.
Arguments lax_tensorN {_ _ _ _} _.
Arguments lax_unit_l {_ _ _ _} _ _.
Arguments lax_unit_r {_ _ _ _} _ _.
Arguments lax_assoc {_ _ _ _} _ _ _ _.

Notation "'φ₀[' L ']'" := (lax_unit L) : monoidal_scope.
Notation "'φ₂[' L ';' X ';' Y ']'" := (lax_tensorN L (X, Y))
  : monoidal_scope.

(** Naturality of the tensorator as an operation-level rewrite. Explicit
    structures avoid ambiguity when [C] and [D] coincide. *)

(** 将 tensorator 的自然性写为运算层面的重写律；显式结构避免 [C] 与 [D]
    相同时的歧义。 *)

Lemma lax_tensor_natural {C D : Cat}
    {MC : MonoidalCategory C} {MD : MonoidalCategory D}
    (L : LaxMonoidalFunctor MC MD)
    {X X' Y Y' : @Ob C} (f : Hom X X') (g : Hom Y Y')
  : φ₂[L; X'; Y'] ∘ (@tensor_map D MD _ _ _ _ (fmap L f) (fmap L g)) ≈
      fmap L (@tensor_map C MC _ _ _ _ f g) ∘ φ₂[L; X; Y].
Proof.
  exact (nt_naturality (lax_tensorN L)
    (X := (X, Y)) (Y := (X', Y')) (f, g)).
Qed.

(** The identity tensorator has identity components even though its source
    and target functor records need not be equal. *)

(** 恒等 tensorator 的分量为恒等态射，不要求来源与目标函子记录相等。 *)

Program Definition IdLaxTensorN {C : Cat} (MC : MonoidalCategory C)
  : (tensorF MC ∘F (IdF ×F IdF)) ⇒ (IdF ∘F tensorF MC)
  :=
  {|nt p := _
  |}.
Next Obligation. destruct p as [X Y]. exact id. Defined.
Next Obligation.
  destruct X as [x y], Y as [x' y'], f as [f g]; cbn.
  rewrite comp_id_l, comp_id_r. reflexivity.
Defined.

(** Every monoidal structure gives an explicitly selected lax identity
    functor. Importing this module does not enable a chosen structure. *)

(** 每个幺半结构都给出须显式选择的 lax 恒等函子；导入本模块不会启用选定结构。 *)

Program Definition IdF_LaxMonoidalFunctor {C : Cat}
    (MC : MonoidalCategory C)
  : LaxMonoidalFunctor MC MC
  :=
  {|LaxMonoidalF := IdF
  ; lax_unit := id
  ; lax_tensorN := IdLaxTensorN MC
  |}.
Next Obligation.
  rewrite tensor_map_id, !comp_id_r. reflexivity.
Defined.
Next Obligation.
  rewrite tensor_map_id, !comp_id_r. reflexivity.
Defined.
Next Obligation.
  rewrite !tensor_map_id, !comp_id_r, !comp_id_l. reflexivity.
Defined.
