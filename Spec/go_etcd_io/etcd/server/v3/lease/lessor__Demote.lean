/-
`(*lessor).Demote` (`server/lease/lessor.go`). The trust boundary. Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Demote()` (write-locked): sets every lease's expiry to `forever`, clears the checkpoint
heap and the expiry notifier, and closes `demotec` if set (and sets it to nil); it touches only
the lessor's memory under its lock. -/
abbrev lease.lessor.Demote.spec : Prop :=
  ∀ (lp : Loc) (γl : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Demote")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
