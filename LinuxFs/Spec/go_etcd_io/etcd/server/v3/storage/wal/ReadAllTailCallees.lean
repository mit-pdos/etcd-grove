/-
**`ReadAll`'s `fileutil.ZeroToEnd(w.tail().File)`** (S/wal.go:626; W3/W5 of `notes/wal-fsext-plan.md`,
twenty-third session): a hypothesis of `WAL.ReadAll.wp_proof` until `ZeroToEnd`'s instance on the WAL's
registered tail is proved (I3b, branch `wal-tc14`; its intended statement, `wal-tc13`'s design). The
tail registered (`walTailW`, its offset at its write position `o0 = |tailStream|`, nothing written by
this handle, exact: `TailMeta`); on success the same tail, in a resize window (`TailMetaW`: the
truncate to `o0` and the `fallocate` back to the old size, which a crash may leave half done), its
size at least `o0`; on an error the tail is lost (as `os.File.Truncate.specWalTail`'s). That the bytes
from `o0` on are zeros is the invariant's (the tail record, `TailZeros`), not this triple's. Lean-first.
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

/-- **`ZeroToEnd` of the WAL's registered tail at its write position** (see the file header). -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.specWalTail (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat),
  o0 ≤ sz → o0 = (tailStream Mr H md cuts).length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walTailW (W := W) f fd name dir γ i H md cuts o0 sz [] }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd)) (Val #f))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ sz' : Nat, ⌜o0 ≤ sz'⌝ ∗
        walTailW f fd name dir γ i H md cuts o0 sz' [] TailMetaW) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
