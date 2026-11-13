/-
`cut`'s first two steps on the old tail (W2 of `notes/wal-fsext-plan.md`, "W2 implementation log",
seventh session), hypotheses of `WAL.cut.wp_proof` until proved:
* `os.File.Truncate.specWalTail`: `f.Truncate(o0 + |out|)` of the crash-tracked tail at its write
  position: `os.File.Truncate.specAu` with the supply of updates built from `walInv` (the in-flight
  `SegFl` of `walTailsRes`, `CrashOk` across the resize; branch `wal-zte`). The tail's size becomes
  its write position (`walTailW` at `sz := o0 + |out|`).
* `WAL.sync.specCut`: `w.sync()` of a handle whose tail was so truncated, the page writer's pending
  bytes written past its size: the tail sized to its stream, synced. `WAL.sync.spec` at a handle
  with `sz = o0 + |out|` but for the size after the flush (`sz := |tailStream|`): its writer accepts
  the pending bytes past the size.
*Error*: the handle lost (as `sync.spec`'s). Lean-first.
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

/-- The handle after `cut`'s `sync`: everything flushed, the tail sized to its stream. -/
def cutSynced (h : WalHS) : WalHS :=
  { h with out := h.out ++ h.pend, pend := [], sz := h.o0 + h.out.length + h.pend.length }

/-- **The WAL tail's truncate at its write position** (see the file header). -/
abbrev os.File.Truncate.specWalTail (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat)
    (out : List w8),
  o0 + out.length ≤ sz →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walTailW (W := W) f fd name dir γ i H md cuts o0 sz out }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate"))
      (Val #(W64 (o0 + out.length))))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ walTailW f fd name dir γ i H md cuts o0 (o0 + out.length) out) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

/-- **`w.sync()` after `cut`'s truncate** (see the file header). -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCut (P : WalPbIn GF) (Mr : WalMarshal) :
    Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (h : WalHS),
  h.rest = 0 → h.sz = h.o0 + h.out.length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walHandleIn P Mr w dir h }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"sync")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗
          walHandleIn P Mr w dir (cutSynced h) ∗
          WalFs.walSyncedLb dir h.H.length) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
