/- Lean-first (no Rocq counterpart).

# The truncate's first step from a pending tail (I3b, `wal-tc18`; pure)

`ZeroToEnd`'s truncate at the write position of the tail `ReadAll` registered, once the lent token
says F-Z or `TailPend` (`walLentRes_pendStop`, `TailZK.zp`): its first step's crash condition is
`crashOkA_tailPend` when the tail is pending (nothing written past the start's frames, the length word
at `wr` zero), `tailCrashStep_rzStart` (F-Z) otherwise.

* `rzSeg_zf`: the announced tail's known zeros past its bytes, from the start's `TcZ`;
* `tailPend_tailLay`: `TailPend` of a layout with its last segment and write position replaced, the
  write position kept;
* `tailCrashStep_rzStartP`: the pending first step's crash condition;
* `rzStart_pureP`: `rzStart_pure` under F-Z or (`TailPend` and `|S| = wr`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSupPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashPend

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **The announced tail's known zeros are past its bytes** (the start's `TcZ`: `zf` at least the
size; `announce` only raises it). -/
theorem rzSeg_zf {g0 : SegG} {tr : Bool} {tg n : Nat} (hlen : g0.bs.length = g0.om.size)
    (htcz : g0.om.TcZ) : ∀ z, (rzSeg g0 tr tg n).om.zf = some z → (rzSeg g0 tr tg n).bs.length ≤ z := by
  intro z hz
  rw [rzSeg_length, hlen]
  simp only [rzSeg, rzMeta, OsMeta.announce, Option.map_eq_some_iff] at hz
  obtain ⟨z0, hz0, rfl⟩ := hz
  have := htcz.1 z0 hz0
  split <;> omega

/-- `TailPend` depends on `old`, `z0` and `wr` only. -/
theorem tailPend_tailLay {lay : WalLay} {pre : List SegG} {g : SegG} (h : TailPend lay) :
    TailPend (tailLay lay pre g lay.wr) := h

/-- **The pending tail's truncate start is a crash step** (`crashOkA_tailPend`). -/
theorem tailCrashStep_rzStartP {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {ents : Ents} {cl : List Claim} {k : Nat} {pre : List SegG} {g0 : SegG} {n : Nat}
    (habs : WalAbsD C Mr d lay ents)
    (habs' : WalAbsD C Mr d (tailLay lay pre (rzSeg g0 true lay.wr n) lay.wr) ents)
    (hP : TailPend lay) (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [g0])
    (hlen : g0.bs.length = g0.om.size) (htcz : g0.om.TcZ) :
    TailCrashStep C Mr d lay pre g0 (rzSeg g0 true lay.wr n) lay.wr cl k := by
  intro alt halt hok
  have hnd' : ((tailLay lay pre (rzSeg g0 true lay.wr n) lay.wr).segs.map (·.ino)).Nodup := by
    have e : (tailLay lay pre (rzSeg g0 true lay.wr n) lay.wr).segs.map (·.ino) = lay.segs.map (·.ino) := by
      rw [hs]; simp [tailLay, rzSeg]
    rw [e]; exact hnd
  exact crashOkA_tailPend habs habs' (tailPend_tailLay hP) hS hnd' hs rfl rfl rfl rfl rfl rfl rfl
    (fun z hz => by rw [hlen]; exact htcz.1 z hz) (rzSeg_zf hlen htcz) halt hok

/-- **The truncate's first step at the write position, F-Z or pending**: `rzStart_pure` with `TailZeros
lay ∨ (TailPend lay ∧ |S| = wr)` in place of F-Z. -/
theorem rzStart_pureP {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {k : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (habs : ∃ ents, WalAbsD C Mr d lay ents)
    (hcut : g0.om.cut = none)
    (hZP : TailZeros lay ∨ (TailPend lay ∧ (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr))
    (hB : TailBound C Mr d lay) (hk : 0 < k)
    (htcz : g0.om.TcZ) (hlo : ¬ SegExact g0 → g0.om.lo ≤ lay.wr) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n K c) := by
  rcases hZP with hZ | ⟨hP, hS⟩
  · exact rzStart_pure hC hW hd hl hs habs hcut hZ hB hk htcz hlo
  obtain ⟨ents, habs⟩ := habs
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  obtain ⟨hsz, -, -, hhi, -⟩ := habs.metas g0 (by rw [hs]; simp)
  obtain ⟨-, -, -, hwb, -⟩ := habs.lastWin g0 (by rw [hs]; simp)
  have habs' : ∀ ents', WalAbsD C Mr d lay ents' →
      WalAbsD C Mr d (tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr) ents' := fun ents' h =>
    walAbsD_rzStart h hs (Nat.le_refl _) (Nat.min_le_right _ _) (by omega)
      (segBytesX_rzSeg hk (by omega) hsz.symm (by omega) htcz.1)
  have hstep := tailCrashStep_rzStartP (cl := cl) (k := n) habs (habs' ents habs) hP hS hnd hs
    hsz.symm htcz
  exact ⟨walsOk_tailA hW hd hl hs rfl (by simp [rzSeg, hcut]) habs' hstep,
    fun K c h => dirKeysOk_tailA hd hl hstep h⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
