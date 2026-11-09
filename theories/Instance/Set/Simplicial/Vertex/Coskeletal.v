From Cats Require Export
  Instance.Set.Simplicial.Vertex.Sieve
  Instance.Set.Simplicial.Coskeletal.
From Stdlib Require Import
  Arith.PeanoNat.

Local Open Scope nat_scope.

(** * Coskeletality of Arbitrary Vertex Nerves

    Every boundary above dimension two contains all vertices, edges and
    triangles. General sieve descent therefore supplies its unique filler
    in any selected category, without a groupoid assumption. *)

(** * 任意顶点 nerve 的余骨架性

    严格高于二维的每个边界均包含全部顶点、边与三角形。因此一般筛下降在任意
    选定范畴中给出唯一填充，无需群胚假设。 *)

(** The chosen coskeletal structure uses native simplex sizes and specified
    equality. Importing this module does not enable the structure globally. *)

(** 选定余骨架结构使用原生单形大小及指定相等；导入本模块不会全局启用该结构。 *)

Program Definition vertex_IsCoskeletal@{u p +}
    {X : SetC} {C : Cat} (T : Functor (EqGpd X) C)
  : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⦂ Cosk[2]
  :=
  {|coskeletal_boundary_universal n b :=
      vertex_sieve_universal T (BoundarySieve (S (S (S n)))) b
        (boundary_low_member n 0 (Nat.le_0_l 2))
        (boundary_low_member n 1 (Nat.le_succ_diag_r 1))
        (boundary_low_member n 2 (Nat.le_refl 2))
  |}.
