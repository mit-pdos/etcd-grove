/-
`(*lessor).closeRequireLeader()` (`client/v3/lease.go`; etcd#22291). Lean-first (no Rocq
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
given for a context `c` that asks for a leader), so each channel at most once, and it keeps the
lessor's invariant `lessor.muInv`, in particular that **every entry of `keepAlives` has a
subscription** (etcd#22094: an entry all of whose subscriptions asked for a leader is removed, not
left with none; the pinned code does not keep this).

What it does not say: the postcondition is `True`, so it does not say that the require-leader
channels *are* closed (a function doing nothing meets it), nor that a subscription leaves the map
only with its channel closed (a right can be dropped).

**The premise `R ch c -∗ R ch c'`** says a channel's right does not depend on its context: it is
the pinned code's bug `issues/etcd-lease-closerequireleader-ctx-misaligned.md` (etcd#22081), used
only where an entry with both kinds of subscriptions is compacted, which pairs a kept channel with
another subscription's context (`ka.ctxs[newIdx]`). With it, `closeOk`'s condition is about the
context stored at the channel's index, not the subscriber's own, so the spec does not exclude
closing a plain subscriber's channel at a later leader loss; a fix of etcd#22081 lets the spec drop
it. -/
abbrev lessor.closeRequireLeader.spec : Prop :=
  ∀ (l : Loc) (R : GoChan → GoInterface → IProp GF) (kl hl : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataRequireLeaderKey ↦□ kl ∗
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataHasLeader ↦□ hl ∗
      sync.isMutex (structFieldRef go_etcd_io.etcd.client.v3.lessor go!"mu" l)
        (lessor.muInv R l) ∗
      lessor.closeOk R kl hl ∗
      □ (∀ (ch : GoChan) (c c' : GoInterface), R ch c -∗ R ch c') }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
      go!"closeRequireLeader")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
