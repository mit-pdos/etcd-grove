/-
**`ReadAll`'s `fileutil.ZeroToEnd(w.tail().File)` and `fileutil.Fdatasync(w.tail().File)`** (S/wal.go:626-
634; W3/W5 of `notes/wal-fsext-plan.md`, twenty-fifth session): hypotheses of `WAL.ReadAll.wp_proof` until
their instances on the WAL's pending tail are proved (I3b, `wal-tc17`'s intended statements, W1 log,
twenty-seventh session; the fdatasync's pending form is `wal-tc18`'s). The tail registered, not yet zeroed
(`walTailP`, the pending token, its offset at its write position `o0 = |tailStream|`, nothing written by
this handle, `TailMetaR`; until P6 item 2 also the length word at `o0` zero, which a torn `Save`'s pending
run of entry records at `o0` does not have: the invariant's `RepOld` and `tailStop` give what it gave);
`ZeroToEnd`'s success: the token of kind `false`, `TailMetaZ`, every byte from `o0` on zero-valued, its size
at least `o0`; the fdatasync's success: the key back (`walLentRes_unpend`), the tail exact (`walTailW …
TailMeta`), the history synced. On an error the tail comes back (W4c U5, fifth session: `walTailPE`, the file's offset
unknown and the reader's stop at `o0` (`TailMetaE`'s `PendStop`), after `ZeroToEnd`'s; `walTailP` unchanged after the fdatasync's),
for `Close` to sync and put back (`WAL.Close.spec` (state `failed`)). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseHandle
public import Proof.syscall.Base

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

/-- **`ZeroToEnd` of the WAL's registered, not yet zeroed tail at its write position** (see the file
header; `wal-tc17`'s intended statement, W1 log, twenty-seventh session): the pending tail (`walTailP`,
the token of kind `true`) with `TailMetaR` (P6 item 2: no zero length word at `o0` assumed); on success the token of kind
`false`, `TailMetaZ` and every byte from `o0` on zero-valued, the size unchanged. Proved
(`ZeroToEnd.wp_specWalTail`, `ZteWalTail.lean`, over `ZeroToEnd.specAu`; `wal-tc19`, which added
`isPkgInit errors` to the pre, `sz' = sz` to the post, and made `TailMetaZ` the cache fact, not `TailZ`). On an error the tail as `walTailPE` (W4c U5, fifth session). -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.specWalTail (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz k : Nat),
  o0 ≤ sz → o0 = (tailStream Mr H md cuts).length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      walTailP (W := W) f fd name dir γ i H md cuts o0 sz [] k true TailMetaR }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd)) (Val #f))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ sz' : Nat, ⌜o0 ≤ sz' ∧ sz' = sz⌝ ∗
        walTailP f fd name dir γ i H md cuts o0 sz' [] k false
          (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0)) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ walTailPE (W := W) Mr f fd name dir γ i H md cuts o0 k) }}

/-- **`fileutil.Fdatasync` of the zeroed pending tail** (`wal-tc18`'s pending form): the window closed
and the zeros durable, the key back (`walLentRes_unpend` at its commit), the tail exact and synced
(`walTailW … TailMetaS`, every byte durable: W4c U5, fifth session, for `Close`'s put-back of a failed
`ReadAll`'s tail) and the history synced; on an error the tail as it was (W4c U5, fifth session). Proved (`Fdatasync.wp_specWalPend`,
`FdatasyncPend.lean`, over `os.File.Fd.spec`; `wal-tc20`). -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.specWalPend (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz k : Nat),
  o0 = (tailStream Mr H md cuts).length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗
      walTailP (W := W) f fd name dir γ i H md cuts o0 sz [] k false
        (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0) ∗
      walCutFrag (W := W) none }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
  {{ (e : w64), RET #(errnoErr e); walCutFrag (W := W) none ∗
      ((⌜e = 0⌝ ∗ walTailW (W := W) f fd name dir γ i H md cuts o0 sz [] TailMetaS ∗
          WalFs.walSyncedLb (W := W) dir H.length) ∨
        (⌜e ≠ 0⌝ ∗ walTailP (W := W) f fd name dir γ i H md cuts o0 sz [] k false
          (fun m bs => TailMetaZ m bs ∧ ∀ b x, o0 ≤ b → bs[b]? = some x → x.1 = 0))) }}

end spec

end EtcdGrove
end Perennial
