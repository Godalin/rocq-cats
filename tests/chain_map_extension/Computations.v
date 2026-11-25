From Cats Require Import
  Cat.Extension.Chain
  Instance.Nat.Order
  Instance.Set.Nat
  Instance.Set.Core
  Cat.Core.
From Stdlib Require Import
  Lists.List.

Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Nine Actual Successor Edges

    Every edge is the existing successor map on natural numbers, rather
    than an identity. An extension adds a chosen value at zero and shifts
    the old function to positive inputs. This makes traversal order and
    the actual retained choices visible in ordinary computations. *)

(** * 九条实际后继边

    每条边是既有自然数后继映射，而非恒等。一次延拓在零处加入所选取值，并把
    原函数移到正输入；普通计算因此能看见行进顺序和实际保留的选择。 *)

Program Definition SuccessorChain (n : nat)
  : Chain SetCat n
  :=
  {|chain_vertex _ := NatS
  ; chain_edge _ := succ_resp
  |}.

Program Definition prepend_value (v : nat) (a : NatS →r NatS)
  : NatS →r NatS
  :=
  {|func x := match x with O => v | S k => a k end
  |}.

Definition successor_extension (v : nat)
  : is_extension_target (C := SetCat) succ_resp NatS.
Proof.
  intros a. exists (prepend_value v a). intros k. reflexivity.
Defined.

Definition edge_extensions (n b : nat)
  : ∀ k, is_extension_target (chain_edge (SuccessorChain n) k) NatS
  := λ k, successor_extension (b + fin_rank k).

Program Definition initial_map
  : NatS →r NatS
  :=
  {|func k := 1000 + k
  |}.

Definition last_position
  : Ordinal 9
  := fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺.

Definition nine_extension (b : nat)
  := chain_extension_target (SuccessorChain 9) NatS (edge_extensions 9 b)
      fin_first last_position (ordinal_from_first last_position) initial_map.

(** Later zero values appear first, and the old function survives after
    all nine nonidentity edges. *)

(** 较晚加入的零值位于前面，原函数在九条非恒等边之后仍然保留。 *)

Example nine_steps_compute
  : map (nine_extension 100).1 ([0;1;2;3;4;5;6;7;8;9;10;11]) =
      [108;107;106;105;104;103;102;101;100;1000;1001;1002].
Proof. vm_compute. reflexivity. Defined.

(** Independently selected new values remain computationally distinct. *)

(** 独立选择的新增取值仍在计算上不同。 *)

Example different_choices_compute
  : ((nine_extension 200).1 0, (nine_extension 200).1 9) = (208,1000).
Proof. vm_compute. reflexivity. Defined.

(** An interior interval visits only its three stored edges. *)

(** 内部区间只经过其中存储的三条边。 *)

Definition interior_extension
  := chain_extension_target (SuccessorChain 9) NatS (edge_extensions 9 100)
      (fin_first⁺⁺ : Ordinal 9) (fin_first⁺⁺⁺⁺⁺ : Ordinal 9)
      (ltac:(apply nat_le_of_le; cbn; repeat constructor)) initial_map.

Example interior_steps_compute
  : map interior_extension.1 ([0;1;2;3;4]) = [104;103;102;1000;1001].
Proof. vm_compute. reflexivity. Defined.

(** The empty interval keeps the original values and uses no edge. *)

(** 空区间保持原有取值，不使用边。 *)

Definition empty_extension
  := chain_extension_target (SuccessorChain 0) NatS (edge_extensions 0 100)
      fin_first fin_first (ordinal_from_first fin_first) initial_map.

Example empty_interval_computes
  : map empty_extension.1 ([0;1;9]) = [1000;1001;1009].
Proof. vm_compute. reflexivity. Defined.

Definition actual_nine_recovery (b : nat)
  := (nine_extension b).2.

Fail Definition choices_are_native_equal
  : (nine_extension 100).1 0 = (nine_extension 200).1 0
  := eq_refl.

(** ** A Nonextendible Edge

    The constant-zero edge identifies two old inputs. Extending the
    identity would have to recover both, an actual contradiction. *)

(** ** 不可延拓的边

    常零边等同两个原输入，若能延拓恒等映射则必须同时恢复它们，产生实际矛盾。 *)

Program Definition collapse_resp
  : NatS →r NatS
  :=
  {|func _ := 0
  |}.

Definition collapse_not_extension_target
  : ¬ is_extension_target (C := SetCat) collapse_resp NatS.
Proof.
  intros E. destruct (E id_resp) as [b H].
  assert (J : 0 = 1).
  { transitivity (b 0); [symmetry; exact (H 0) | exact (H 1)]. }
  discriminate J.
Defined.
