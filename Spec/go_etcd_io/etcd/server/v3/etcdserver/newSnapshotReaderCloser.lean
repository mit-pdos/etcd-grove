/-
`newSnapshotReaderCloser(lg, snapshot)` (`snapshot_merge.go:56-80`): an `io.Pipe` whose writer a new
goroutine fills with the backend snapshot (`WriteTo`), then closes (with `WriteTo`'s error) and
closes the snapshot.

**Users**: `createMergedSnapshotMessage` (`snapshot_merge.go:39`). Snippet `snapshot.go`
(`ReqMergedSnapshot`).

**Proof sketch**: `io.Pipe()` (Perennial's/2e's `io` specs); `go func()` with the thread token
(kept until the goroutine ends: never returned, PRINCIPLES "a trusted statement never gives out a
counted resource it did not take"); `snapshot.WriteTo(pw)` (4a's: the image's bytes; an error is the
reader's having closed early); `pw.CloseWithError(err)`; `snapshot.Close()` (4a's: no error, so
`lg.Panic` is unreachable). The reader streams the image (`dbReader rc γ k`).

**Changes** from `specs-ref`'s spec (the backend's `Data`, `io.rcCloseOk`, the size bound): over
`beSnap`/`dbReader` (provisional, 4a's and 2e's). **Margin**: the logger's messages.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply
public import Spec.go_uber_org.zap.Api

set_option autoImplicit false

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

/-- **A reader of a backend snapshot's image**, filled by a goroutine. -/
def newSnapshotReaderCloser.spec : Prop :=
  ∀ (lg : Loc) (bs : GoInterface) (γ : Names) (k : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      Zap.isLogger lg ∗ beSnap bs γ k ∗ threadTok }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.newSnapshotReaderCloser)) (Val #lg))
      (Val #bs))
  {{ (rc : GoInterface), RET #rc; dbReader rc γ k }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
