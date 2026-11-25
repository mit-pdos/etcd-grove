/-
`(*storage.storage).Save(st, ents)` (`server/storage/storage.go:84-88`; wal-link L2, 2026-11-17,
`notes/wal-link-scope.md` §2): the WAL's `Save` under the storage's read lock. Proved in
`Proof/.../storage/storage__Save.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI storage go_etcd_io.raft.v3
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]

/-- **`st.Save(s, ents)`** of the storage `p` over the WAL `w` (`storageOver`), with a reader token
(`storageRd`, given back): under `st.mux`'s read lock, `w.Save(s, ents)`, whose triple (`WAL.Save.spec`)
this is otherwise. -/
abbrev storage.storage.Save.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (p ss : Loc) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp)
    (hp : Loc) (hs : HardStateM) (sl : GoSlice) (esL : List Loc) (es : List EntryM) (sized : Bool)
    (Q : WalDur → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storageOver p w ss ∗ storageRd p w ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ ⌜walCov Sio ∨ q = 1⌝ ∗
      ⌜walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)⌝ ∗
      P.hsIn hp hs ∗ sl ↦*□ esL ∗ walEntsIn P esL es ∗ ⌜∀ e ∈ es, uint.nat e.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40⌝ ∗
      (⌜saveBatchBytes Mr es ≤ maxSaveBatch⌝ -∗
        AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
          <{ WalFs.walDiskAtI dir γ.inc { d with H := d.H ++ [(WalOpG.save hs es).toRaw] }, COMM Q d }>) }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ (err : GoInterface), RET #err; storageRd p w ∗
      ((⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir γ.inc (d.H.length + 1) ∗
          (⌜walMustSync (d.H.map WalOpG.toM) hs es⌝ -∗ WalFs.walSyncedLb dir γ.inc (d.H.length + 1))) ∨
      (⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ ∗ ∃ d : WalDur, Q d) ∨
      (⌜err ≠ GoInterface.nil ∧ maxSaveBatch < saveBatchBytes Mr es⌝ ∗ walOpenWS Sio P Mr w dir γ q)) }}

end spec

end EtcdGrove
end Perennial
