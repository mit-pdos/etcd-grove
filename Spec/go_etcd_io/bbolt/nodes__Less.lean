module
public import Proof.go_etcd_io.bbolt.NodeModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `s.Less(i, j)`: the first key of node `i` is below that of node `j`. It panics on a node
without inodes (the nodes `spill` sorts have some). -/
abbrev nodes.Less.spec : Prop :=
  ∀ (s : GoSlice) (xs : List Loc) (dq : DFrac) (i j : w64) (a b : Loc) (av bv : node) (qa qb : DFrac)
    (ia ib : List internal.common.Inode) (qia qib : DFrac) (ita itb : internal.common.Inode)
    (ka kb : List w8) (dka dkb : DFrac),
  0 ≤ sint.Z i → 0 ≤ sint.Z j → xs[sint.nat i]? = some a → xs[sint.nat j]? = some b →
  ia[0]? = some ita → ib[0]? = some itb →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦*{dq} xs ∗
      a ↦{qa} av ∗ av.inodes' ↦*{qia} ia ∗ ita.key' ↦*{dka} ka ∗
      b ↦{qb} bv ∗ bv.inodes' ↦*{qib} ib ∗ itb.key' ↦*{dkb} kb }}
    (App (App (Val (s @!! nodes.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (go.GoStringLt ka kb)); s ↦*{dq} xs ∗
      a ↦{qa} av ∗ av.inodes' ↦*{qia} ia ∗ ita.key' ↦*{dka} ka ∗
      b ↦{qb} bv ∗ bv.inodes' ↦*{qib} ib ∗ itb.key' ↦*{dkb} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
