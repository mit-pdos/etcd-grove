/-
`node.size` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U9a; used by U8 (`node.rebalance`), U9b (`Bucket.write`, `node.spill`). Proof:
`Proof/go_etcd_io/bbolt/node__size.lean` (a `sorry` until U9a).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.size()`: the page size the node needs (`insSize`: a header, and per inode an element and
its key's and value's lengths); only the slices' headers are read. -/
abbrev node.size.spec : Prop :=
  ∀ (n : Loc) (nv : node) (ins : List Inode) (dq dqi : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"size")) (Val #()))
  {{ RET #(W64 (insSize ins : Int)); n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}

end spec

end bbolt
end EtcdGrove
end Perennial
