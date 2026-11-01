/-
`Snapshot` (the backend, `backend.go`; names only). `b.Snapshot()`: the batch transaction
committed (`b.batchTx.Commit()`), then, under `b.mu`'s reader side, a bbolt read transaction
begun (`b.db.Begin(false)`, `lg.Fatal` on an error) and a goroutine started that warns while the
snapshot stays open; the `*snapshot` returned. The trust boundary (D22 S-f, 2026-10-19; an axiom
in `Proof/go_etcd_io/etcd/server/v3/storage/backend/backend__Snapshot.lean`). Lean-first (no Rocq
counterpart); the vocabulary is `InvSnapshot.lean`.

The pre: the backend open (`bOpen`), one write-back's budget (`wbTok`, for the commit's `Unlock`,
as `batchTxBuffered.Commit`), and the caller's **observation** `Q` of what a commit leaves: a
resource `R` the caller holds through the call (given back) such that, whatever the batch lock's
client resource `W` and hooks' resource `Pk` are, `R` with them, the batch lock's quarter of the
readers' view, at a logical view the physical view `vd` is thin of (`viewAt`; question 2, option
(a), 2026-10-29: until then the quarter at `vd` itself), its half of the hook's own keys at `d` (`hkOwn`) and (D22,
2026-10-23: the backend over every bucket) its half of the tracked buckets at `r` (`rbOwn`) give
`Q vd d r`. The post: the snapshot open (`snapOpen`) over bbolt's committed data `D`, with
`Q (sData P D) (hkData P D) (rbData P D)`: `D` reads thin of the readers' (logical) view off the
hook's buckets (exactly as it, with nothing deletable: `viewAt_noDel`)
and holds the hook's own keys and the tracked buckets as they were when the last commit before
the read transaction began left them. For the server, `W` holds the store's view of the `Key`
bucket (`mvcc.writerRes`'s `bucketView`), `Pk` the consistent index's meta keys
(`batchLockInv`, `metaTM`), `R` the apply thread's half of the tracked buckets: `Q` can say the
key bucket is the store's log's, the stored index the apply thread's (D22 S-h) and the other
buckets the applied log's (`restModel`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `b.Snapshot()`: a snapshot of bbolt's committed data `D`, read as the caller's observation `Q`
says of every commit (see the file header). -/
abbrev backend.backend.Snapshot.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp) (R : IProp GF)
    (Q : VData → GMap (GoString × GoString) GoString → GMap GoString BktData → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ R ∗
      □ (∀ (vd : VData) (d : GMap (GoString × GoString) GoString) (r : GMap GoString BktData),
        R -∗ W -∗ Pk -∗ viewAt γ vd -∗ hkOwn γ d -∗ rbOwn γ r -∗ ⌜Q vd d r⌝) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : Data), RET #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp);
      snapOpen sp D ∗ bOpen γ qo ∗ R ∗ ⌜Q (sData P D) (hkData P D) (rbData P D)⌝ }}

end spec

end EtcdGrove
end Perennial
