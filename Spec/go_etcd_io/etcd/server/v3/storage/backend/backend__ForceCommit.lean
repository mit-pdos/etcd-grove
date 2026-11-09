/-
## `(*backend).ForceCommit()` (`backend.go:356-358`): translated

**Users.** mvcc (`kvstore.go:125, 160, 216, 289`, `kvstore_compaction.go:95`: the commit request
`storageReq`), the lessor (`lessor.go:834`), auth (`schema/auth.go:60`), alarms
(`schema/alarm.go:105`), the server (`v3_server.go:412`: after a lease checkpoint), 2d's
`snapshot` (`KV().Commit()`). Snippet `commit.go` (`ReqForceCommitDurable`).

**Proof sketch.** `batchTx.Commit()` (`batchTxBuffered.Commit.spec`).

**Changes** (from `specs-ref`'s `bkReq`): the per-call step `beReq` (the client's `X` to `Y` at the
commit, with the committed image), the history in the client's hands.

**Margin.** The step runs whether or not bbolt commits (nothing pending: the image is already the
last commit's, `beCommitted` holds of it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`b.ForceCommit()`**: the batch committed (the hooks run, the client's commit step and the
caller's per-call step at the commit). -/
def backend.ForceCommit.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q ∗ X ∗ beReq γ Pk X Y }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"ForceCommit")) (Val #()))
  {{ RET #(); beOpen γ q ∗ Y }}

end spec

end Backend
end EtcdGrove
end Perennial
