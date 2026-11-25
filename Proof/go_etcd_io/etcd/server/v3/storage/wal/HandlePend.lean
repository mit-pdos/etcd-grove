/- Lean-first (no Rocq counterpart).

# The tail `ReadAll` registers, lent to the invariant (I3b, `wal-tc17`)

`ReadAll` registers the tail a crash (or a `Close`) left without F-Z (`walTailsRes_registerPend`): the
holder gets the pending token `walPendTok dir γ |old|` in place of the key, until the fdatasync after
`ZeroToEnd` (`walLentRes_unpend`). Its handle's tail is `walTailP`, `walTailW` with the token of the
tail lent (`walLentTokB dir γ k p`) for the key.

* `TailMetaR`: what `ReadAll` knows of the tail it registers (`TailMeta` without `TailZ`/`PastZ`).
* `TailMetaZ`: the tail after `ZeroToEnd` (all its bytes, no mappings, the page cache known zero to the
  end of the size's page).
* `walTailP`: the handle's tail, lent; its description locked (`fdLocksW`: unit `closefailed`, so that a failed
  `Close` hands the lock to `Repair`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashPend

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

/-- **The tail after a failed `ZeroToEnd`** (W4c U5, fifth session; `ZeroToEnd.specWalTail`'s error arm):
all its bytes, no mappings, at least `o0` long, and the reader, from `o0` at the chain value `c`, accepts
a run of entry records, then nothing (`PendStop`: nothing changed or a truncate announced that did not
land, the values `ReadAll`'s reader stopped on; or the truncate landed: no bytes past `o0`, or the
growth's zeros). Until P6 item 2 the length word at `o0` zero, which a torn `Save`'s pending run does not
have. Whether a resize window is open is not known. -/
def TailMetaE [GooseExts] (Mr : WalMarshal) (c : w32) (o0 : Nat) (m : Fs.OsMeta) (bs : List Fs.ByteG) : Prop :=
  bs.length = m.size ∧ m.maps = ∅ ∧ o0 ≤ m.size ∧ PendStop walCodec Mr (bs.map (·.1)) o0 c

/-- `bs.take o0 ++ ys` read from `o0` is `ys`, and the values of `ys` are those of `bs` from `o0` on, or
all zero: the reader's stop on `bs` at `o0` is kept (`pendStop_congr`, `pendStop_zeroWord`). -/
theorem pendStop_of_vals [GooseExts] {Mr : WalMarshal} {c : w32} (bs ys : List Fs.ByteG) (o0 : Nat)
    (ho : o0 ≤ bs.length)
    (hv : ys.map Prod.fst = (bs.drop o0).map Prod.fst ∨ ∀ y ∈ ys, y.1 = 0)
    (h : PendStop walCodec Mr (bs.map (·.1)) o0 c) :
    PendStop walCodec Mr ((bs.take o0 ++ ys).map (·.1)) o0 c := by
  have hd : ((bs.take o0 ++ ys).map (·.1)).drop o0 = ys.map Prod.fst := by
    rw [List.map_append, List.drop_append_of_le_length (by simp; omega)]
    simp [ho]
  rcases hv with hv | hv
  · refine pendStop_congr ?_ (by simp; omega) (by simp; omega) h
    rw [hd, hv, List.map_drop]
  · apply pendStop_zeroWord
    intro j _
    have e := congrArg (fun l => l.getD j 0) hd
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at e
    rw [List.getD_eq_getElem?_getD, e, List.getElem?_map]
    cases hy : ys[j]? with
    | none => rfl
    | some y => exact hv y (List.mem_of_getElem? hy)

/-- The length word of the bytes `bs.take o0 ++ ys` at `o0` is `ys`'s first eight values. -/
theorem lenWord_app_take (bs ys : List Fs.ByteG) (o0 : Nat) (ho : o0 ≤ bs.length) (j : Nat) :
    ((bs.take o0 ++ ys).getD (o0 + j) (0, [])).1 = (ys.getD j (0, [])).1 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
    Nat.min_eq_left ho, Nat.add_sub_cancel_left]

/-- The values of `ys` are those of `bs` from `o0` on, or all zero: then its length word is zero where
`bs`'s at `o0` is. -/
theorem lenWord_of_vals (bs ys : List Fs.ByteG) (o0 : Nat)
    (hv : ys.map Prod.fst = (bs.drop o0).map Prod.fst ∨ ∀ y ∈ ys, y.1 = 0)
    (hz : ∀ j, j < 8 → (bs.getD (o0 + j) (0, [])).1 = 0) (j : Nat) (hj : j < 8) :
    (ys.getD j (0, [])).1 = 0 := by
  rcases hv with hv | hv
  · have h1 : (ys.getD j (0, [])).1 = (ys.map Prod.fst).getD j 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases ys[j]? <;> rfl
    have h2 : ((bs.drop o0).map Prod.fst).getD j 0 = (bs.getD (o0 + j) (0, [])).1 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_drop]
      cases bs[o0 + j]? <;> rfl
    rw [h1, hv, h2]; exact hz j hj
  · rw [List.getD_eq_getElem?_getD]
    cases h : ys[j]? with
    | none => rfl
    | some y => exact hv y (List.mem_of_getElem? h)

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
  iprop(os.ownFile f fd name (DFrac.own 1) ∗ (∃ (rd : Bool) (lo lk : Option Bool), osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗
    fdLocksW fd ⟨i, rd, true, lo, lk⟩) ∗
    os.ownOff f (W64 (o0 + out.length)) ∗ walLentTokB (W := W) dir γ k p ∗
    ∃ (m : OsMeta) (bs : List ByteG),
    osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
    ⌜m.size = sz ∧ tm m bs ∧ sz < 2 ^ 62 ∧ 0 ≤ fd.toInt ∧ LoWr m (o0 + out.length)⌝ ∗
    ghostVar γ (1 : Qp).half ((H, md, cuts, o0 + out.length, i, none) : TailG))

/-- **The handle's tail after a failed `ZeroToEnd`** (W4c U5, fifth session): `walTailP` with the lent
token of kind `false` (`ZeroToEnd`'s first step), the file's offset unknown, `TailMetaE Mr (tailCrc …) o0`. `Close`
(`WAL.Close.spec` (state `failed`)) syncs it and puts it back. -/
def walTailPE (Mr : WalMarshal) (f : Loc) (fd : w64) (name : GoString) (dir : GoString) (γ : GName)
    (i : Ino) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (o0 : Nat) (k : Nat) : IProp GF :=
  letI := walAllG (W := W)
  iprop(os.ownFile f fd name (DFrac.own 1) ∗ (∃ (rd : Bool) (lo lk : Option Bool), osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗
    fdLocksW fd ⟨i, rd, true, lo, lk⟩) ∗
    (∃ o' : w64, os.ownOff f o') ∗ walLentTokB (W := W) dir γ k false ∗
    ∃ (m : OsMeta) (bs : List ByteG),
    osMeta i (DFrac.own (1 : Qp).half) m ∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ∗
    ⌜0 ≤ fd.toInt ∧ TailMetaE Mr (tailCrc Mr H md cuts) o0 m bs⌝ ∗
    ghostVar γ (1 : Qp).half ((H, md, cuts, o0, i, none) : TailG))

end handle

end WalFs
end EtcdGrove
end Perennial

end
