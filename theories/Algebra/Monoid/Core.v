From Cats Require Export
  Algebra.Semigroup.Core.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with monoid.
Infix "⋅" := magma_mul (at level 40, left associativity) : monoid_scope.
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
Context {M : SetC} (SG : Semigroup M).
Local Existing Instance SG.

(** A specified element is a two-sided unit for the selected semigroup. *)

(** 指定元素是选定半群的双侧单位元。 *)

Class IsMonoid (e : M)
  :=
  { monoid_unit_left x : e ⋅ x ≈S x
  ; monoid_unit_right x : x ⋅ e ≈S x
  }.

(** Choose a unit on this exact parent, retaining its Type-valued laws. *)

(** 在恰好该父结构上选取单位元，并保留 Type 值定律。 *)

Class HasMonoid
  :=
  { monoid_chosen_unit : M

  (** The laws refer to the stored element and the supplied semigroup. *)

  (** 定律指向保存的元素及给定半群。 *)

  ; isMonoid :: IsMonoid monoid_chosen_unit
  }.

End UnitExtension.

Arguments IsMonoid {_} _ _.
Arguments HasMonoid {_} _.

(** The existing fixed-setoid presentation stores one semigroup and one
    extension of that exact parent. Complete packed objects will be migrated
    separately; the unit and its laws are defined only in the extension. *)

(** 现有固定广集呈现保存一个半群及对恰好该父结构的一份扩充。完整结构包另批
    迁移；单位元及其定律仅在扩充中定义一次。 *)

Class Monoid@{u p l} (M : SetC@{u p})
  : Type@{l}
  :=
  { MonoidSG :> Semigroup@{l u p} M
  ; hasMonoid :: HasMonoid MonoidSG
  }.

Arguments MonoidSG {_} _.

(** Register the same parent for inherited instance search. *)

(** 将同一父结构注册到继承实例搜索。 *)

#[export] Existing Instance MonoidSG.

(** Present an explicitly supplied extension as the existing monoid
    interface, with transparent parent and unit projections. *)

(** 将显式给定的扩充呈现为现有幺半群接口，父结构与单位元投影均透明。 *)

Program Definition MonoidFromExtension {M : SetC} (SG : Semigroup M)
    (HM : HasMonoid SG)
  : Monoid M
  :=
  {|MonoidSG := SG
  ; hasMonoid := HM
  |}.

(** Read the unit from this monoid's stored extension explicitly. Another
    extension on the same semigroup cannot change its computational choice. *)

(** 显式读取此幺半群保存的扩充中的单位元。同一半群上的另一扩充不能改变该
    计算选择。 *)

Definition monoid_unit@{u p l} {M : SetC@{u p}}
    `{HM : !Monoid@{u p l} M}
  : M
  := @monoid_chosen_unit M (@MonoidSG M HM) (@hasMonoid M HM).

Arguments monoid_unit {M Monoid} : rename.

Notation "1" := monoid_unit : monoid_scope.

(** Recover the left unit law from the same stored evidence. *)

(** 从同一份保存的见证恢复左单位律。 *)

Definition monoid_unit_l@{u p l} {M : SetC@{u p}}
    `{HM : !Monoid@{u p l} M} (x : M)
  : 1 ⋅ x ≈S x
  := @monoid_unit_left M _ _ (@isMonoid M _ (@hasMonoid M HM)) x.

Arguments monoid_unit_l {M Monoid} x : rename.

(** Recover the right unit law without searching for another extension. *)

(** 恢复右单位律，不搜索另一份扩充。 *)

Definition monoid_unit_r@{u p l} {M : SetC@{u p}}
    `{HM : !Monoid@{u p l} M} (x : M)
  : x ⋅ 1 ≈S x
  := @monoid_unit_right M _ _ (@isMonoid M _ (@hasMonoid M HM)) x.

Arguments monoid_unit_r {M Monoid} x : rename.

(** Any two specified units of the same selected semigroup agree in its
    setoid equality. Their records and native carrier values need not agree. *)

(** 同一选定半群的任意两个指定单位元在其广集相等下相等，无须记录或载体值
    的原生相等。 *)

Lemma monoid_units_equiv {M : SetC} (SG : Semigroup M) (e f : M)
    (He : IsMonoid SG e) (Hf : IsMonoid SG f)
  : e ≈S f.
Proof.
  transitivity (@magma_mul M SG e f).
  - symmetry. exact (@monoid_unit_right M SG f Hf e).
  - exact (@monoid_unit_left M SG e He f).
Qed.

(** A left and a right inverse agree using only a chosen unit extension
    of the specified semigroup. *)

(** 左逆与右逆相等只需指定半群上的选定单位扩充。 *)

Lemma monoid_extension_inverse_unique {M : SetC} (SG : Semigroup M)
    (HM : HasMonoid SG) (x y z : M)
    (Hy : @magma_mul M SG y x ≈S @monoid_chosen_unit M SG HM)
    (Hz : @magma_mul M SG x z ≈S @monoid_chosen_unit M SG HM)
  : y ≈S z.
Proof.
  transitivity (@magma_mul M SG y (@magma_mul M SG x z)).
  - rewrite Hz. symmetry. exact (@monoid_unit_right M SG _ (@isMonoid M SG HM) y).
  - rewrite <- (@semigroup_assoc M SG), Hy.
    exact (@monoid_unit_left M SG _ (@isMonoid M SG HM) z).
Qed.

(** The fixed-setoid monoid view recovers the same inverse-uniqueness
    theorem from its stored extension. *)

(** 固定广集的幺半群视图从保存的扩充恢复同一逆唯一性定理。 *)

Lemma monoid_inverse_unique@{l u p} {M : SetC@{u p}}
    `{HM : !Monoid@{u p l} M}
    (x y z : M) (Hy : y ⋅ x ≈S 1) (Hz : x ⋅ z ≈S 1)
  : y ≈S z.
Proof.
  exact (monoid_extension_inverse_unique (@MonoidSG M HM)
    (@hasMonoid M HM) x y z Hy Hz).
Qed.
