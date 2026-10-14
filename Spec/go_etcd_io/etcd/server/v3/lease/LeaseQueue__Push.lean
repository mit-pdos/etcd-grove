/-
`(*LeaseQueue).Push` (`server/lease/lease_queue.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
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

/-- `pq.Push(x)`, `x` an `*LeaseWithTime` item `p` the caller owns: appends it, its index the
queue's old length. -/
abbrev lease.LeaseQueue.Push.spec : Prop :=
  ∀ (qf : Loc) (s : GoSlice) (xs : List (Loc × w64)) (p : Loc) (id k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ qf ↦ s ∗
      queueAt s xs 1 ∗ lwtAt p id k 1 }}
    (App (Val (qf @!! go.GoType.PointerType LeaseQueue.ty @!! go!"Push"))
      (Val #(interface.mkOk (go.GoType.PointerType LeaseWithTime.ty) #p : GoInterface)))
  {{ RET #(); ∃ s' : GoSlice, qf ↦ s' ∗ queueAt s' (xs ++ [(p, id)]) 1 }}

end spec

end EtcdGrove
end Perennial
