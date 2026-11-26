/-
`(*storage.storage).SaveSnap(snap)` (`server/storage/storage.go:59-70`; wal-link L2, 2026-11-17,
`notes/wal-link-scope.md` §2, §3.3): under the storage's read lock, the WAL's `SaveSnapshot` of a
`walpb.Snapshot` sharing raft's metadata cells and conf state. Proved in
`Proof/.../storage/storage__SaveSnap.lean`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.StorageRep
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshot

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

/-- **`st.SaveSnap(snap)`** of the storage `p` over the WAL `w`, with a reader token (given back):
`snap.Metadata` frozen at content `m` (raft's `metaRoC`), its `Index` and `Term` set; the record
`walpb.Snapshot{Index, Term, ConfState: GetConfState()}` shares them, so its bytes are protobuf-go's of
`metaWalC m`, which the premise asks to be the marshaller's of the model (`Mr.encSnap m.model`: the conf
state's content as the marshaller encodes it, `al` the history's presence bit; `notes/wal-link-scope.md` F2, discharged where `Mr` is fixed,
L3). Otherwise `WAL.SaveSnapshot.spec` (its `shared` state) at `m.model`, the conf state present iff `m`'s
is. -/
abbrev storage.storage.SaveSnap.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (p ss : Loc) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (q : Qp)
    (sn mp : Loc) (dq : DFrac) (m : SnapMetaC) (al sized : Bool) (Q : WalDur → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storageOver p w ss ∗ storageRd p w ∗
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp m ∗
      ⌜m.index.isSome ∧ m.term.isSome⌝ ∗ ⌜snapEnc (metaWalC m) = Mr.encSnap m.model al⌝ ∗
      WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ q ∗ ⌜walCov Sio ∨ q = 1⌝ ∗
      ⌜walCov Sio → DirFits dir ∧ ∀ b, Sio.path (child dir b)⌝ ∗
      ⌜m.model.Index' = W64 0 ∨ m.confState.isSome = true⌝ ∗ ⌜uint.nat m.model.Index' < 2 ^ 64 - 1⌝ ∗
      ⌜(Mr.encSnap m.model al).length < 2 ^ 40⌝ ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAtI dir γ.inc d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ WalFs.walDiskAtI dir γ.inc { d with H := d.H ++ [WalOpG.snap m.model al] }, COMM Q d }> }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"SaveSnap")) (Val #sn))
  {{ (err : GoInterface), RET #err; storageRd p w ∗ sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
      ((⌜err = GoInterface.nil⌝ ∗ walOpenWS Sio P Mr w dir γ q ∗ ∃ d : WalDur, Q d ∗
          WalFs.walLenLb w dir γ.inc (d.H.length + 1) ∗ WalFs.walSyncedLb dir γ.inc (d.H.length + 1)) ∨
      (⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ ∗ ∃ d : WalDur, Q d)) }}

end spec

end EtcdGrove
end Perennial
