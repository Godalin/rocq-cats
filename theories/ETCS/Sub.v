(** Import compatibility for the classifier interface, now independent of
    the additional ETCS axioms. New clients should import [Topos.Sub]. *)

(** 保留分类子接口的导入兼容性；该接口已独立于额外的 ETCS 公理。
    新客户端应导入 [Topos.Sub]。 *)

From Cats Require Export
  Topos.Sub.
