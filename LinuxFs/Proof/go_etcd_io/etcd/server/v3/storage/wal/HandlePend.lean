/- Lean-first (no Rocq counterpart).

# The tail `ReadAll` registers, lent to the invariant (I3b, `wal-tc17`)

`ReadAll` registers the tail a crash (or a `Close`) left without F-Z (`walTailsRes_registerPend`): the
holder gets the pending token `walPendTok dir γ |old|` in place of the key, until the fdatasync after
`ZeroToEnd` (`walLentRes_unpend`). Its handle's tail is `walTailP`, `walTailW` with the token of the
tail lent (`walLentTokB dir γ k p`) for the key.

* `TailMetaR`: what `ReadAll` knows of the tail it registers (`TailMeta` without `TailZ`/`PastZ`).
* `TailMetaZ`: the tail after `ZeroToEnd` (all its bytes, no mappings, the page cache known zero to the
  end of the size's page).
* `walTailP`: the handle's tail, lent.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

/-- **What `ReadAll` knows of a tail it registers, not yet zeroed**: all its bytes, no mappings, no
resize window open on it (a crash leaves it with its size); not `TailZ` (zeros known past the size)
nor `PastZ` (nothing but zeros known past `hi`), which the fdatasync after `ZeroToEnd` gives
(`TailZ.synced`, `PastZ.synced`). -/
def TailMetaR (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ m.lo = m.size ∧ m.hi = m.size

/-- **The tail after `ZeroToEnd`** (until the fdatasync after it): all its bytes, no mappings, and the
page cache known zero from the size to the end of its page (`ZeroToEnd.specAu`'s `pageEnd m.size ≤ m'.cz`),
which is what the fdatasync needs for `TailZ` of the synced `OsMeta` (`TailZ.synced_of`; `PastZ` of a synced
`OsMeta` holds). Not `TailZ` itself (`wal-tc19`; the `wal-tc17` form had `TailMetaW` without `PastZ`): a
crashed or synced tail may not know the candidates of its last page past the size, and `ZeroToEnd` does
not make them known. Its window (`lo`, `hi`) is the handle's `LoWr` and the invariant's. -/
def TailMetaZ (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ Fs.pageEnd m.size ≤ max m.size m.cz

theorem TailMeta.tailMetaR {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMeta m bs) : TailMetaR m bs :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem TailMetaR.loWr {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMetaR m bs) (wr : Nat) :
    LoWr m wr :=
  .inl ⟨h.2.2.1, h.2.2.2⟩

theorem TailMetaW.tailMetaZ {m : Fs.OsMeta} {bs : List Fs.ByteG} (h : TailMetaW m bs) :
    TailMetaZ m bs :=
  ⟨h.1, h.2.1, h.2.2.1.pageEnd_size⟩

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The handle's tail, lent to the invariant**: `walTailW` with the token of the tail lent,
`walLentTokB dir γ k p` (`|old| = k`; `p = true` registered, not yet zeroed, `walPendTok`, from the
registration; `p = false` once `ZeroToEnd`'s first step has recorded the zero length word at the write
position, `walLentRes_pendStop`), in place of the key; `tm` (default `TailMetaR`) what the program
knows of the tail's `OsMeta` and bytes. -/
def walTailP (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName) (i : Ino)
    (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (k : Nat) (p : Bool) (tm : Fs.OsMeta → List Fs.ByteG → Prop := TailMetaR) : IProp GF :=
  letI := walAllG (W := W)
  iprop(os.ownFile f fd name (DFrac.own 1) ∗ (∃ rd : Bool, osFd fd (DFrac.own 1) ⟨i, rd, true⟩) ∗
    os.ownOff f (W64 (o0 + out.length)) ∗ walLentTokB (W := W) dir γ k p ∗
    ∃ (m : OsMeta) (bs : List ByteG),
    osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
    ⌜m.size = sz ∧ tm m bs ∧ sz < 2 ^ 62 ∧ 0 ≤ fd.toInt ∧ LoWr m (o0 + out.length)⌝ ∗
    ghostVar γ (1 : Qp).half ((H, md, cuts, o0 + out.length, i, none) : TailG))

end handle

end WalFs
end EtcdGrove
end Perennial

end
