/-
**`fileutil.Fdatasync(w.tail().File)` of the tail a failed `ZeroToEnd` left** (`Close`'s `w.sync()` of a failed
`ReadAll`'s handle, `WAL.sync.specLentE`; unit `synclent`): the tail lent by the token of kind `false`
(`walTailPE`: the file's offset unknown, `TailMetaE`, the reader's stop at `o0` (`PendStop`), a resize window maybe
open). On success the tail synced and still lent, the token's recorded `|old|` the synced layout's (some
`k'`; `walInvBody_syncPE`: `syncLay_anyE`'s layout, F-Z or `TailPend`), the program's halves exact
(`TailMetaR`), every byte durable, the zeros known from the size on; on an error the tail as it was.
Proved (`Fdatasync.wp_specWalLentE`, `FdatasyncLentE.lean`, over `os.File.Fd.spec`). Lean-first.
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

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.specWalLentE (Mr : WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r : GoString) (f : Loc) (fd : w64) (name dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 k : Nat),
  o0 = (tailStream Mr H md cuts).length →
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walTailPE (W := W) Mr f fd name dir γ i H md cuts o0 k ∗
      walCutFrag (W := W) none }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync)) (Val #f))
  {{ (e : w64), RET #(errnoErr e); walCutFrag (W := W) none ∗
      ((⌜e = 0⌝ ∗ os.ownFile f fd name (DFrac.own 1) ∗
          (∃ (rd : Bool) (lo lk : Option Bool), osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗
            fdLocksW fd ⟨i, rd, true, lo, lk⟩) ∗
          (∃ o' : w64, os.ownOff f o') ∗ (∃ k' : Nat, walLentTokB (W := W) dir γ k' false) ∗
          ∃ (m : OsMeta) (bs : List ByteG),
            osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
            ⌜TailMetaR m bs ∧ (∀ z, m.zf = some z → m.size ≤ z) ∧ ∀ y ∈ bs, y = Fs.durB y.1⌝ ∗
            tailVar (W := W) γ ((H, md, cuts, o0, i, none) : TailG)) ∨
        (⌜e ≠ 0⌝ ∗ walTailPE (W := W) Mr f fd name dir γ i H md cuts o0 k)) }}

end spec

end EtcdGrove
end Perennial
