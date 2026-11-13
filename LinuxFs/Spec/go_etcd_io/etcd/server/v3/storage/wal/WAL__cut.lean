/-
`(*wal.WAL).cut` over `fsExt` (W2 of `notes/wal-fsext-plan.md`): the statement `Save` takes as a
hypothesis (W6), for W2 to prove or restate. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

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

/-- **`w.cut()`** (S/wal.go:875-965) of a handle with every record encoded (`rest = 0`): the tail
truncated at the encoder's offset and synced, a new segment named after the history's last index
started at the history's length (`cuts ++ [|H|]`), its headers (`Crc`, the metadata,
`State(w.state)`) encoded and synced, the directory fsynced; the history synced (`walSyncedLb
|H|`). The new handle's tail is the new segment (inode, ghost names and encoder offset fresh).
*Error*: the handle lost. The bound on the cuts: the pipeline's `count` is a Go `int`, and its
`count % 2` (the next file's name) is a signed remainder (`Pipe.lean`; the handle's pipeline has
received at most `h.cuts.length` files, `walPipeH`). The cuts below `|H|` and `|H|` a cut position
(`walCutPos`: after a `Save` that wrote a record): the new segment starts a new cut (`cutLay_abs`).
`w.state` the history's last hard state: the new segment's headers hold it (`cutHdrDs`). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (P : WalPbIn GF) (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS),
  h.rest = 0 → h.st = walLastHS (h.H.map WalOpG.toM) → h.cuts.length + 2 < 2 ^ 63 →
  (∀ b ∈ h.cuts, b < h.H.length) →
  walCutPos (h.H.map WalOpG.toM) h.H.length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"cut")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ h' : WalHS, walHandleIn P Mr w dir h' ∗
          ⌜h'.H = h.H ∧ h'.md = h.md ∧ h'.cuts = h.cuts ++ [h.H.length] ∧ h'.rest = 0 ∧ h'.st = h.st ∧
            h'.enti = h.enti ∧ h'.snapi = h.snapi⌝ ∗ WalFs.walSyncedLb dir h.H.length) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
