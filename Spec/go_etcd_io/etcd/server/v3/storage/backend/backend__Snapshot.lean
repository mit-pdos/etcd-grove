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
buckets the applied log's (`restModel`). (2026-11-02, the merged snapshot's window) The post also
gives a reader's lower bound of the compaction keys' flag over `D` with an empty read buffer
(`fkRd`, what a commit gives the backend's readers, `batchTxBuffered.unsafeCommit`): with the
client's half at `0` (`fkOwn γ 0`, a store that does not compact), `D` has no compaction key
(`fkRd_abs`).

(F2, stage 3, 2026-11-03: the user's approved restatement, `notes/image-cmp-f2-plan.md`) The
observation is also handed the batch lock's halves of the backend's two exact ghosts: the physical
view of the non-hook buckets (`pvHalf`, at the observed `vd` itself) and the compaction keys'
values (`ckHalf` at `v`), and `Q` takes `v`: the post's `Q` is at `fkVals D`, the values `D` holds
at `Meta`'s compaction keys. Today's statement (without them) is the corollary
`backend.backend.Snapshot.spec_of_specF2` (`etcdserver/SnapSendBranch.lean`).

(2026-11-06, branch `begin-tok`, the user's approval: `notes/begin-tok-plan.md`, Q1/Q2/Q4) The pre
also takes the caller's `threadTok`: the snapshot's bbolt read transaction holds a reader slot of
bbolt's `mmaplock` until `snapshot.Close`, which gives the token back. The warning goroutine is a
live thread, paid by its own fork's fuel; net, the caller is out one token per open snapshot until
`Close` (`notes/axiom-review/begin-tok-restated.md`, A8). Under
`[ThreadBoundLe GF (2 ^ 29)]`, `bbolt.Open_kv`'s bound. Until then the pre took no token and a
proof could hold `2 ^ 30` open snapshots (`notes/axiom-review/backend-snapshot-begin.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Perennial.ProgramLogic.Bounds

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
says of every commit (see the file header); the caller's `threadTok` held until `snapshot.Close`. -/
abbrev backend.backend.Snapshot.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (qo : Qp)
    (R : IProp GF)
    (Q : VData → GMap (GoString × GoString) GoString → GMap GoString BktData → FkVals → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ threadTok ∗ R ∗
      □ (∀ (vd : VData) (d : GMap (GoString × GoString) GoString) (r : GMap GoString BktData)
          (v : FkVals),
        R -∗ W -∗ Pk -∗ viewAt γ vd -∗ pvHalf γ vd -∗ hkOwn γ d -∗ rbOwn γ r -∗ ckHalf γ v -∗
          ⌜Q vd d r v⌝) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : Data), RET #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp);
      snapOpen sp D ∗ bOpen γ qo ∗ R ∗ fkRd γ P (D, ⟨∅, W64 0⟩) ∗
      ⌜Q (sData P D) (hkData P D) (rbData P D) (fkVals D)⌝ }}

end spec

end EtcdGrove
end Perennial
