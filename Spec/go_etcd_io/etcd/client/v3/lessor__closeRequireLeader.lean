/-
`(*lessor).closeRequireLeader()` (`client/v3/lease.go`; etcd#22087). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.closeRequireLeader()` (by `recvKeepAliveLoop` on `ErrNoLeader`), a safety spec: under
`l.mu`, it runs without a panic (no nil channel closed, no index out of range), closes a channel
only through the close right `R ch c` its subscription holds in the invariant (`lessor.closeOk`,
given for a context `c` that asks for a leader), so each channel at most once and only a channel
whose **own** subscriber's context asks for a leader, and it keeps the lessor's invariant
`lessor.muInv`, in which every kept channel stays paired with its own subscriber's context
(etcd#22081, fixed by etcd#22087: the compaction copies `ka.ctxs[i]`, not `ka.ctxs[newIdx]`).

What it does not say: the postcondition is `True`, so it does not say that the require-leader
channels *are* closed (a function doing nothing meets it), nor that a subscription leaves the map
only with its channel closed (a right can be dropped). Nor that every entry keeps a subscription:
etcd#22087 alone still compacts an entry all of whose subscriptions asked for a leader to none and
leaves it in the map (etcd#22094), so `lessor.muInv` here allows an empty entry. With etcd#22291 on
top, the invariant with non-emptiness holds too (`notes/pr-verify/etcd-22087.md`).

On `pr-verify/etcd-22291` the spec had the premise `□ ∀ ch c c', R ch c -∗ R ch c'` (a channel's
right does not depend on its context), standing for etcd#22081; with etcd#22087's fix it is gone. -/
abbrev lessor.closeRequireLeader.spec : Prop :=
  ∀ (l : Loc) (R : GoChan → GoInterface → IProp GF) (kl hl : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataRequireLeaderKey ↦□ kl ∗
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataHasLeader ↦□ hl ∗
      sync.isMutex (structFieldRef go_etcd_io.etcd.client.v3.lessor go!"mu" l)
        (lessor.muInv R l) ∗
      lessor.closeOk R kl hl }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
      go!"closeRequireLeader")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
