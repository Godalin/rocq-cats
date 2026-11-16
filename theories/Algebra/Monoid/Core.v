From Cats Require Export
  Algebra.Semigroup.Core.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with monoid.
Infix "⋅" := (@mul _ (hasMagma _))
  (at level 40, left associativity) : monoid_scope.
Notation "'(' x '⋅−)'" := (mul_l_resp x) : monoid_scope.
Notation "'(−⋅' y ')'" := (mul_r_resp y) : monoid_scope.
Local Open Scope monoid_scope.

(** * Monoids on Sets

    A monoid adds a unit to one selected semigroup. The inherited magma
    stores multiplication once, and all laws use the specified Type-valued
    setoid equality rather than native equality. *)

(** * 广集上的幺半群

    幺半群为一个选定半群增加单位元。继承的原群只保存一次乘法，所有定律
    使用指定的 Type 值广集相等，不要求原生相等。 *)

(** ** Units on a Fixed Semigroup

    Fix the selected multiplication and associativity first. Candidate unit
    laws and a chosen unit then extend exactly that semigroup; they do not
    select another multiplication on its carrier. *)

(** ** 固定半群上的单位元

    先固定选定乘法及结合律，再以候选单位律和选定单位元扩充恰好该半群，
    不在其载体上另选乘法。 *)

Section UnitExtension.
Context (SG : Semigroup).

(** A specified element is a two-sided unit for the selected semigroup. *)

(** 指定元素是选定半群的双侧单位元。 *)

Class IsMonoid (e : SG)
  :=
  { mul_unit_l x : e ⋅ x ≈S x
  ; mul_unit_r x : x ⋅ e ≈S x
  }.

(** Choose a unit on this exact parent, retaining its Type-valued laws. *)

(** 在恰好该父结构上选取单位元，并保留 Type 值定律。 *)

Class HasMonoid
  :=
  { monoid_unit : SG

  (** The laws refer to the stored element and the supplied semigroup. *)

  (** 定律指向保存的元素及给定半群。 *)

  ; isMonoid :: IsMonoid monoid_unit
  }.

End UnitExtension.

(** A complete monoid owns one semigroup and one chosen unit extension. *)

(** 完整幺半群拥有一个半群及一份选定单位扩充。 *)

Record Monoid@{u p l}
  :=
  { MonoidToSemigroup :> Semigroup@{u p l}
  ; hasMonoid :: HasMonoid MonoidToSemigroup
  }.

(** Pack a supplied semigroup and its chosen extension transparently. *)

(** 将给定半群及其选定扩充透明打包。 *)

Program Definition MonoidFromExtension (SG : Semigroup)
    (HM : HasMonoid SG)
  : Monoid
  :=
  {|MonoidToSemigroup := SG
  ; hasMonoid := HM
  |}.

(** The numeral reads the unit selected by the complete monoid. Raw
    fixed-parent clients use the same public field with their own evidence. *)

(** 数字记号读取完整幺半群选定的单位元；固定父结构客户端直接使用同一公开
    字段并传入自己的见证。 *)

Notation "1" := (@monoid_unit _ (hasMonoid _)) : monoid_scope.

(** Any two specified units of the same selected semigroup agree in its
    setoid equality. Their records and native carrier values need not agree. *)

(** 同一选定半群的任意两个指定单位元在其广集相等下相等，无须记录或载体值
    的原生相等。 *)

Lemma units_equiv (SG : Semigroup) (e f : SG)
    (He : IsMonoid SG e) (Hf : IsMonoid SG f)
  : e ≈S f.
Proof.
  transitivity (@mul _ (hasMagma SG) e f).
  - symmetry. exact (@mul_unit_r SG f Hf e).
  - exact (@mul_unit_l SG e He f).
Qed.

(** A left and a right inverse agree using only a chosen unit extension
    of the specified semigroup. *)

(** 左逆与右逆相等只需指定半群上的选定单位扩充。 *)

Lemma mul_extension_inv_unique (SG : Semigroup)
    (HM : HasMonoid SG) (x y z : SG)
    (Hy : @mul _ (hasMagma SG) y x ≈S @monoid_unit SG HM)
    (Hz : @mul _ (hasMagma SG) x z ≈S @monoid_unit SG HM)
  : y ≈S z.
Proof.
  transitivity (@mul _ (hasMagma SG) y (@mul _ (hasMagma SG) x z)).
  - rewrite Hz. symmetry. exact (@mul_unit_r SG _ (@isMonoid SG HM) y).
  - rewrite <- (@mul_assoc _ (isSemigroup SG)), Hy.
    exact (@mul_unit_l SG _ (@isMonoid SG HM) z).
Qed.

(** The complete monoid uses the inverse-uniqueness theorem for its
    stored extension. *)

(** 完整幺半群使用保存扩充的同一逆唯一性定理。 *)

Lemma mul_inv_unique {M : Monoid}
    (x y z : M) (Hy : y ⋅ x ≈S 1) (Hz : x ⋅ z ≈S 1)
  : y ≈S z.
Proof.
  exact (mul_extension_inv_unique (MonoidToSemigroup M)
    (hasMonoid M) x y z Hy Hz).
Qed.
