/-
`updateCommittedIndex(ap, rh)` (`raft.go:357-368`): the batch's last committed entry's index (or its
snapshot's, if higher) into the ready handler's `updateCommittedIndex` (which stores it if higher).

**Users**: the loop (`raft.go:229`). **Proof sketch**: the entries' last `Index` (R1's `entriesRO`),
the snapshot's index (R1's `snapOpt`); both at most the delivered log's length (`committedLb`); the
handler's closure (`readyHandlerOk`) loads `s.committedIndex` and stores the larger
(`setCommittedIndex.spec` with `readyHandlerTok`'s `committedW`). **Changes**: over
`readyHandlerOk`. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

def updateCommittedIndex.spec : Prop :=
  ∀ (ap : Loc) (apv : go_etcd_io.etcd.server.v3.etcdserver.toApply) (rh s : Loc) (γ : Names)
    (f : Nat) (ents : List Raft.LogEntry) (so : Option Raft.Snapshot) (l : List Raft.LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ap ↦ apv ∗ Raft.entriesRO apv.entries' f ents ∗ Raft.snapOpt apv.snapshot' so ∗
      readyHandlerOk rh s γ ∗ readyHandlerTok rh ∗ Raft.committedLb γ.raft l ∗
      ⌜f + ents.length ≤ l.length + 1 ∧ ∀ sn, so = some sn → uint.nat sn.index ≤ l.length⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex)) (Val #ap))
      (Val #rh))
  {{ RET #(); ap ↦ apv ∗ readyHandlerTok rh }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
