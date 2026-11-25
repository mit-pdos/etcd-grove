/-
`(*wal.WAL).sync` as `Close` calls it, after closing the file pipeline (W10 of
`notes/wal-fsext-plan.md`): `WAL.sync.spec` (`WAL__sync.lean`) over `walHandleC`
(`CloseHandle.lean`). A hypothesis of `WAL.Close.wp_proof`, to be proved with `sync.spec`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseHandle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **`w.sync()` after `Close` closed the pipeline** (`sync.spec` over `walHandleC`: `sync` never
reads `w.fp`; the proof is `sync.spec`'s with the pipeline left out of the frame). `sync.spec`'s
docstring: `w.sync()` (S/wal.go:967-992) of a handle with every record of its history encoded
(`rest = 0`): the encoder's pending bytes flushed to the tail (`out ++ pend`, nothing pending; the
tail's size grown to cover them if they pass it), the tail fdatasynced: the history synced (`walSyncedLb
|H|`), the tail's resize window closed and every byte durable (the handle's `TailMetaS`: `OsMeta.synced`,
`durB`; `TailMetaS.of_sync` from `wp_osFsync`'s post; `Close`'s unregistration needs it for the WAL's
`TailSynced`, the W7-W12 log's sixth session). The window may be open before
(`TailMetaW`: a write past the preallocated size, W6 log, thirteenth session). *Error*: the handle lost but
the lock token (`walLockedTok`: `Close` returns before it unlocks, and `Create`'s cleanup must still merge
`nm.tmp`'s claim back, which needs a token excluding the free one; ledger 2026-11-14) and the names
fragment (`walNamesFrag nf`: `Create`'s pending registration, which its cleanup completes when nothing was
renamed; `notes/wal-units/create.md`), and the tail's open file and fd with the naming fact at them (the
handle before naming pins the file: `Create`'s deferred `f.Close()` closes it). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specC (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (j : Ino) (h : WalHS)
    (nmd : Loc → Roots → Qp → IProp GF) (nf : Option GoString),
  h.rest = 0 →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleC P Mr w dir j h TailMetaW nmd nf }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walHandleC P Mr w dir j
          { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) }
          TailMetaS nmd nf ∗
          WalFs.walSyncedLb dir h.inc h.H.length) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ fmtErrorOk err ∗ WalFs.walLockedTok ∗ WalFs.walNamesFrag nf ∗
        ∃ (f : Loc) (fd : w64) (name : GoString) (d : OsFd) (R : Roots) (q : Qp),
          nmd f R q ∗ os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d ∗ fdLocks fd d) }}

end spec

end EtcdGrove
end Perennial
