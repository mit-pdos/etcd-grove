/-
`(*raftNode).start(rh)` (raft.go): the `Ready` loop, in a new goroutine.
Lean-first (no Rocq counterpart); see `InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.start(rh)`, with the loop's ghost state at the node's delivered log `L`, the right to
close `done`, and a tick's resource as often as the ticker fires (see `decisions.md`, "The
server's raft wrapper": the ticks are unbounded). The goroutine hands each `Ready`'s committed
entries to `applyc` (`rnApP`), saves and appends its entries, sends its messages, and advances
the node; it stops (`onStop`) on `stopped`. The loop owns the ready handler's resource `R` (its
`updateCommittedIndex` closure's: the committed index's writer half, 2026-10-13, the request path's
unit 4c). -/
abbrev raftNode.start.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r rh : Loc) (L : List EntryModel) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗ isReadyHandler rh R ∗ R ∗ rnLoopTok γ L ∗ rnDoneTok γ r ∗
      □ (|==> E.T) }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"start")) (Val #rh))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
