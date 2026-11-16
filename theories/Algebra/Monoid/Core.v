From Cats Require Export
  Algebra.Semigroup.Core.

Local Open Scope algebra_scope.

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
  { mul_unit : SG

  (** The laws refer to the stored element and the supplied semigroup. *)

  (** 定律指向保存的元素及给定半群。 *)

  ; isMonoid :: IsMonoid mul_unit
  }.

End UnitExtension.

(** Unit laws infer the parent and selected unit from the expression.
    Candidate comparisons can still supply their law witness by name. *)

(** 单位律从表达式推断父结构和选定单位元；比较候选时仍可按名称指定见证。 *)

Arguments mul_unit_l {SG e IsMonoid} x.
Arguments mul_unit_r {SG e IsMonoid} x.

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

(** The numeral reads the complete monoid's selected unit. Fixed-parent
    clients can use the transparent [MonoidFromExtension] view to specify
    their supplied choice. Ordinary expressions infer the monoid. *)

(** 数字记号读取完整幺半群选定的单位元。固定父结构客户端可用透明的
    [MonoidFromExtension] 视图指定给定选择；普通表达式会推断幺半群。 *)

Notation "1" := (@mul_unit _ (hasMonoid _)) : algebra_scope.

(** Any two specified units of the same selected semigroup agree in its
    setoid equality. Their records and native carrier values need not agree. *)

(** 同一选定半群的任意两个指定单位元在其广集相等下相等，无须记录或载体值
    的原生相等。 *)

Lemma units_equiv {SG : Semigroup} {e f : SG}
    `{He : !IsMonoid SG e} `{Hf : !IsMonoid SG f}
  : e ≈S f.
Proof.
  transitivity (e ⋅ f).
  - symmetry. rewrite mul_unit_r. reflexivity.
  - rewrite mul_unit_l. reflexivity.
Qed.

(** A left and a right inverse agree using only a chosen unit extension
    of the specified semigroup. *)

(** 左逆与右逆相等只需指定半群上的选定单位扩充。 *)

Lemma mul_extension_inv_unique (SG : Semigroup)
    (HM : HasMonoid SG) (x y z : SG)
    (Hy : (y ⋅ x) ≈S (1 : MonoidFromExtension SG HM))
    (Hz : (x ⋅ z) ≈S (1 : MonoidFromExtension SG HM))
  : y ≈S z.
Proof.
  transitivity (y ⋅ (x ⋅ z)).
  - rewrite Hz. symmetry.
    rewrite mul_unit_r. reflexivity.
  - rewrite <- mul_assoc, Hy.
    rewrite mul_unit_l. reflexivity.
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
