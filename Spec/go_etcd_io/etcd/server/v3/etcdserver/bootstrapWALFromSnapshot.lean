/-
`bootstrapWALFromSnapshot(cfg, snapshot, ci)` (`server/v3/etcdserver/bootstrap.go:600`, modified in
`etcd-io/etcd#22655`). Lean-first.

Opens the WAL from `snapshot` via `openWALFromSnapshot(cfg, snapshot)` and constructs a
`*bootstrappedWAL`:
- When `cfg.ForceNewCluster = false`, logs `"restarting local member"` and returns the unmodified
  `bootstrappedWAL` (`es0`, `hs0`), preserving `PlogWf (snapId sv) es0`.
- When `cfg.ForceNewCluster = true`, sets `bwal.st.Commit = new(max(oldCommitIndex,
  ci.ConsistentIndex()))` (`c1 := w64Max hs0.Commit' ciIdx`), truncates uncommitted WAL entries via
  `bwal.CommitedEntries()` (`es1 := es0.take (uint.Z c1 - uint.Z sv.Metadata'.Index').toNat`),
  fills any backend-ahead gap `walLastIndex sv es1 + 1 .. c1` with empty `EntryNormal` entries via
  `bwal.fillBackendAheadGap()` (`es2 := es1 ++ gapEntries hs0.Term' (walLastIndex sv es1) c1`),
  builds single-node configuration-change entries `ccEnts` at indices `c1 + 1 ..` via
  `bwal.NewConfigChangeEntries()`, appends and commits them via
  `bwal.AppendAndCommitEntries(entries)` (`es3 := es2 ++ ccEnts`), and returns `bwal` with
  `PlogWf (snapId sv) es3` established so `bwal.MemoryStorage()` will not panic with a gap in
  `MemoryStorage.Append`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBootWAL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.config go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

abbrev bootstrapWALFromSnapshot.spec : Prop :=
  ∀ (cfg : ServerConfig) (snapshot : Loc) (ci : ConsistentIndexer)
    (w st : Loc) (ents : GoSlice) (snap metaPtr : Loc)
    (hs0 : HardStateM) (es0 ccEnts : List EntryM) (sv : SnapshotM) (mv : snapshotMetadata)
    (ciIdx : w64),
  let c1 := w64Max hs0.Commit' ciIdx
  let es1 := es0.take (uint.Z c1 - uint.Z sv.Metadata'.Index').toNat
  let es2 := es1 ++ gapEntries hs0.Term' (walLastIndex sv es1) c1
  let es3 := es2 ++ ccEnts
  let hs3 := hsAfterAppend { hs0 with Commit' := c1 } es2 ccEnts
  let esFinal := if cfg.ForceNewCluster' then es3 else es0
  let hsFinal := if cfg.ForceNewCluster' then hs3 else hs0
  cfg.Logger' ≠ null →
  PlogWf (snapId sv) es0 →
  (cfg.ForceNewCluster' = true →
    uint.Z sv.Metadata'.Index' ≤ uint.Z c1 ∧
    (es1.length : Int) + (uint.Z c1 - uint.Z (walLastIndex sv es1)) + (ccEnts.length : Int) < 2 ^ 63 ∧
    uint.Z c1 + 1 + (ccEnts.length : Int) < 2 ^ 64) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "#Hopen" ∷ openWALFromSnapshotOk cfg snapshot w st ents snap metaPtr hs0 es0 sv mv ∗
      "#Hci" ∷ (⌜cfg.ForceNewCluster' = false⌝ ∨ ciConsistentIndexOk ci ciIdx) ∗
      "#Hcc" ∷ (⌜cfg.ForceNewCluster' = false⌝ ∨ bootConfChangeEntsOk sv es2 mv.nodeID' ccEnts) }}
    (App (App (App (Val (@! bootstrapWALFromSnapshot)) (Val #cfg)) (Val #snapshot)) (Val #ci))
  {{ (bwal : Loc), RET #bwal;
      ∃ entsFinal : GoSlice,
        bwal ↦ bootstrappedWAL.mk cfg.Logger' true w st entsFinal snap metaPtr ∗
        bootWalSaveOk w ∗
        hsPts st (DFrac.own 1) hsFinal ∗
        entsPts entsFinal (DFrac.own 1) esFinal ∗
        ownSliceCap Loc entsFinal (DFrac.own 1) ∗
        snapOptRO snap sv ∗
        metaPtr ↦ mv ∗
        ⌜PlogWf (snapId sv) esFinal⌝ }}

end spec

end EtcdGrove
end Perennial
