/- Lean-first (no Rocq counterpart).

# `Repair`'s truncate past the write position, to the end of a pending run (P6, E4; pure)

`Repair` truncates its registered tail at the decoder's last offset (repair.go:86), the end of the frames
it read. Since the torn-`Save` fix those may end in a pending run (entry records no state record follows,
`walRepairFile`'s `es`), past the stream's end `wr`: the truncate's target `tg` is then in `[wr, size]`, the
bytes `[wr, tg)` (the run, the durable image's) kept below the window's new least crash size `min lo tg`.

* `winHead_of_last`: `WinHead` of a new last segment from the old one's, its `lo` no larger and its
  candidates below it kept (an exact old tail: `ByteOk`'s stamp-0 candidate; `WinHead`'s third arm).
* `winHead_rzSeg`, `walAbsD_rzStartT`: the truncate's start at `tg ≥ wr` (`walAbsD_rzStartH`).
* `walAbsD_rzLandT`: its landing at `tg` (`walAbsD_rzLand` at `wr`, generalized).
* `repOld_rzLandT`: `RepOld` across the landing at `tg`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashRep
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RzLand

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- A resize's step keeps every candidate. -/
theorem RzCands.mem {rz : List Nat} {cs cs' : Cands} (h : RzCands rz cs cs') {q : w8 × Nat}
    (hq : q ∈ cs) : q ∈ cs' := by
  rcases h with rfl | ⟨n, -, -, rfl⟩
  · exact hq
  · exact List.mem_append_left _ hq

/-- **`WinHead` of a new last segment `g` from the old one's `g1`** (see the file header). -/
theorem winHead_of_last {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g1 g : SegG} {lay' : WalLay}
    (habs : WalAbsD C Mr d lay ents) (hg1 : lay.segs.getLast? = some g1) (hw : lay'.wr = lay.wr)
    (hlo : g.om.lo ≤ g1.om.lo)
    (hX : ∀ b, b < (segBytesX g).length → b < g.om.lo →
      b < (segBytesX g1).length ∧
        ∀ q, q ∈ ((segBytesX g1).getD b (0, [])).2 → q ∈ ((segBytesX g).getD b (0, [])).2) :
    WinHead lay' g := by
  intro b hb1 hb2
  rw [hw] at hb1
  by_cases hl : g.om.lo ≤ b
  · exact .inl hl
  right
  obtain ⟨hb1', hq⟩ := hX b hb2 (by omega)
  by_cases hx : SegExact g1
  · have hbl : b < g1.bs.length := by have := hx.1; omega
    obtain ⟨-, -, -, -, hbytes, -⟩ := (habs.last g1 hg1).1 hx
    obtain ⟨q, hqm, hq0⟩ := (hbytes b (g1.bs[b]'hbl) (List.getElem?_eq_getElem hbl)).head0
    refine .inr ⟨q, hq q ?_, hq0⟩
    rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl,
      Option.getD_some]
    exact hqm
  · rcases habs.winHead g1 hg1 hx b hb1 hb1' with h | ⟨s, hs⟩ | ⟨q, hqm, hq0⟩
    · omega
    · exact .inl ⟨s, hq _ hs⟩
    · exact .inr ⟨q, hq q hqm, hq0⟩

/-- **`WinHead` of the truncate's announced tail at any target**, from the old tail's. -/
theorem winHead_rzSeg {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {tg n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hX : (segBytesX (rzSeg g0 true tg n)).length = (segBytesX g0).length ∧
      ∀ b, b < (segBytesX g0).length → RzCands (rzSeg g0 true tg n).om.rz
        ((segBytesX g0).getD b (0, [])).2 ((segBytesX (rzSeg g0 true tg n)).getD b (0, [])).2) :
    WinHead (tailLay lay pre (rzSeg g0 true tg n) lay.wr) (rzSeg g0 true tg n) := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  refine winHead_of_last habs hg0 rfl (by simp only [rzSeg, rzMeta_lo]; omega) (fun b hb _ => ?_)
  have hb' : b < (segBytesX g0).length := by rw [← hX.1]; exact hb
  exact ⟨hb', fun q hq => (hX.2 b hb').mem hq⟩

/-- **The truncate's start at a target at or past `wr`** keeps the static relation
(`walAbsD_rzStartH` with `winHead_rzSeg`). -/
theorem walAbsD_rzStartT {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {tg n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hwr : lay.wr ≤ tg) (htg : tg ≤ g0.om.hi)
    (hX : (segBytesX (rzSeg g0 true tg n)).length = (segBytesX g0).length ∧
      ∀ b, b < (segBytesX g0).length → RzCands (rzSeg g0 true tg n).om.rz
        ((segBytesX g0).getD b (0, [])).2 ((segBytesX (rzSeg g0 true tg n)).getD b (0, [])).2) :
    WalAbsD C Mr d (tailLay lay pre (rzSeg g0 true tg n) lay.wr) ents :=
  walAbsD_rzStartH habs hs hwr (winHead_rzSeg habs hs hX) htg hX

/-- **The landing at a target `tg ∈ [wr, size]` keeps the static relation** (`walAbsD_rzLand`, there at
`tg = wr`): the bytes below `tg` kept (from `wr` on zero given F-Z, the in-flight tail's), `WinHead`
from the in-flight tail's (the same candidates, `segBytesX_rzLand`). -/
theorem walAbsD_rzLandT {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {tg n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [rzSeg g0 true tg n])
    (hlen : g0.bs.length = g0.om.size) (hwt : lay.wr ≤ tg) (htg : tg ≤ g0.om.size)
    (hcut : g0.om.cut = none) (hhi : g0.om.size ≤ g0.om.hi) :
    WalAbsD C Mr d (tailLay lay pre (rzLand g0 tg n) lay.wr) ents := by
  have hg1 : lay.segs.getLast? = some (rzSeg g0 true tg n) := by rw [hs]; simp
  have hl1 := rzSeg_length g0 true tg n
  have hl2 := rzLand_length (n := n) htg hlen
  have hW := habs.lastWin _ hg1
  obtain ⟨hso, hwS, hbo, hwo, hB, hz0, hzS, hzZ, hWC⟩ := hW
  have hmin : min g0.om.size tg = tg := Nat.min_eq_right htg
  have hX := segBytesX_rzLand (n := n) htg hlen hhi
  have hXl : (segBytesX (rzLand g0 tg n)).length = (segBytesX (rzSeg g0 true tg n)).length := by
    have := congrArg List.length hX; simpa using this
  refine walAbsD_win habs hs rfl rfl ?_ ⟨fun hx => ?_, fun _ => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show (rsPost true g0.om tg tg).size = _; rw [hl2]; rfl
    · show (rsPost true g0.om tg tg).cut = none
      simp only [rsPost, OsMeta.announce, OsMeta.touch_cut, hcut]
    · show min g0.om.lo tg ≤ _; rw [hl2]; omega
    · show _ ≤ max g0.om.hi tg; rw [hl2]; omega
  · -- exact after the landing: nothing was cut off, the in-flight tail exact
    have h1 : min g0.om.lo tg = tg := by have := hx.1; rw [hl2] at this; exact this
    have h2 : max g0.om.hi tg = tg := by have := hx.2; rw [hl2] at this; exact this
    have hsz : g0.om.size = tg := by
      obtain ⟨-, -, -, hhi', -⟩ := habs.metas _ (List.mem_of_getLast? hg1)
      rw [hl1] at hhi'
      change _ ≤ max g0.om.hi tg at hhi'; omega
    have hex1 : SegExact (rzSeg g0 true tg n) :=
      ⟨by show min g0.om.lo tg = _; rw [hl1]; omega,
       by show max g0.om.hi tg = _; rw [hl1]; omega⟩
    have hbs : (rzLand g0 tg n).bs = (rzSeg g0 true tg n).bs := by
      simp only [rzLand, rzSeg, hmin]
      rw [List.drop_eq_nil_of_le (by omega)]; simp [rsAnn]
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := (habs.last _ hg1).1 hex1
    refine ⟨k1, k2, ?_, k4, fun b x hb => k5 b x (by rw [← hbs]; exact hb), k6, k7, k8⟩
    rw [hbs]; exact k3
  · refine ⟨⟨hso, hwS, by simp only [tailLay]; omega, by simp only [tailLay]; omega,
      fun b x hb hbw => ?_, hz0, hzS, hzZ, ?_⟩, ?_, fun hZ b x hb hx => ?_, ?_, ?_,
      fun b x hb hlb hbw => ?_⟩
    · simp only [tailLay] at hbw ⊢
      have hbw' : b < tg := by
        have : (rzLand g0 tg n).om.lo = min g0.om.lo tg := rfl
        omega
      rw [rzLand_getElem? htg hlen hbw'] at hb
      exact hB b x hb hbw
    · refine hWC.same (by show max g0.om.hi tg ≤ max g0.om.hi tg; exact Nat.le_refl _)
        (by rw [hl2]; show tg ≤ max g0.om.hi tg; omega) (Nat.le_of_eq hXl.symm)
        (fun b _ => getD_snd_of_map hX b) (fun s hs => ?_)
      simpa [rzLand, rzSeg, rzMeta] using hs
    · refine winHead_of_last habs hg1 rfl
        (by show min g0.om.lo tg ≤ min g0.om.lo tg; exact Nat.le_refl _) (fun b hb _ => ?_)
      refine ⟨by omega, fun q hq => ?_⟩
      rw [getD_snd_of_map hX b]; exact hq
    · have hbt : b < tg := by
        have := (List.getElem?_eq_some_iff.1 hx).1
        rw [hl2] at this; exact this
      rw [rzLand_getElem? htg hlen hbt] at hx
      simp only [tailLay] at hb
      exact habs.zeroPast _ hg1 hZ b x hb hx
    · have := habs.oldHi_any _ hg1
      simp only [rzSeg, rzMeta_hi] at this
      show lay.old.length ≤ max g0.om.hi tg; omega
    · have h := habs.winLo_any _ hg1; exact h
    · simp only [tailLay] at hbw ⊢
      rw [rzLand_getElem? htg hlen (by omega)] at hb
      have h := habs.winLo_any _ hg1
      unfold WinLo at h
      have : (rzLand g0 tg n).om.lo = min g0.om.lo tg := rfl
      have : (rzSeg g0 true tg n).om.lo = min g0.om.lo tg := rfl
      exact habs.lowW _ hg1 b x hb hbw (by omega) (fun s hs => by simpa [rzLand, rzSeg, rzMeta] using hs)

/-- **`RepOld` across the truncate's landing at `tg`** (`segBytesX_rzLand`: the same candidates). -/
theorem repOld_rzLandT {lay : WalLay} {pre : List SegG} {g0 : SegG} {tg n : Nat}
    (hs : lay.segs = pre ++ [rzSeg g0 true tg n]) (hR : RepOld lay)
    (hlen : g0.bs.length = g0.om.size) (htg : tg ≤ g0.om.size) (hhi : g0.om.size ≤ g0.om.hi) :
    RepOld (tailLay lay pre (rzLand g0 tg n) lay.wr) :=
  repOld_sameCands hs rfl hR (segBytesX_rzLand htg hlen hhi)

/-- **The truncate's start at `tg ∈ [wr, size]` from a `RepOld` tail is a crash step**
(`tailCrashStep_rzStartR` at `tg`). -/
theorem tailCrashStep_rzStartRT {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {ents : Ents} {cl : List Claim} {k : Nat} {pre : List SegG} {g0 : SegG} {tg n : Nat}
    (habs : WalAbsD C Mr d lay ents)
    (habs' : WalAbsD C Mr d (tailLay lay pre (rzSeg g0 true tg n) lay.wr) ents)
    (hR : RepOld lay) (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [g0])
    (hlen : g0.bs.length = g0.om.size) (htcz : g0.om.TcZ) (hn : 0 < n) (htg : tg ≤ g0.om.size) :
    TailCrashStep C Mr d lay pre g0 (rzSeg g0 true tg n) lay.wr cl k := by
  intro alt halt hok
  have hnd' : ((tailLay lay pre (rzSeg g0 true tg n) lay.wr).segs.map (·.ino)).Nodup := by
    have e : (tailLay lay pre (rzSeg g0 true tg n) lay.wr).segs.map (·.ino) = lay.segs.map (·.ino) := by
      rw [hs]; simp [tailLay, rzSeg]
    rw [e]; exact hnd
  obtain ⟨-, -, -, hhi, -⟩ := habs.metas g0 (by rw [hs]; simp)
  obtain ⟨hXl, hXc⟩ := segBytesX_rzSeg (tg := tg) hn htg hlen (by omega) htcz.1
  have hR' := repOld_rzCands hs rfl hR hXl hXc
  exact crashOkA_tailRep hC habs habs' hR' hS hnd' hs rfl rfl rfl rfl rfl rfl rfl
    (fun z hz => by rw [hlen]; exact htcz.1 z hz) (rzSeg_zf hlen htcz) halt hok

/-- **The truncate's first step at `tg ∈ [wr, size]` from a `RepOld` tail** (`rzStart_pureR`'s `RepOld`
branch at `tg`), `RepOld` kept. -/
theorem rzStart_pureRT {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {k tg : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (habs : ∃ ents, WalAbsD C Mr d lay ents)
    (hcut : g0.om.cut = none) (hR : RepOld lay)
    (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr) (hk : 0 < k)
    (htcz : g0.om.TcZ) (hwt : lay.wr ≤ tg) (htg : tg ≤ g0.om.size) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzSeg g0 true tg k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzSeg g0 true tg k) lay.wr]> Ls) cl n K c) ∧
      RepOld (tailLay lay pre (rzSeg g0 true tg k) lay.wr) := by
  obtain ⟨ents, habs⟩ := habs
  obtain ⟨hsz, -, -, hhi, -⟩ := habs.metas g0 (by rw [hs]; simp)
  have hX := segBytesX_rzSeg (tg := tg) hk htg hsz.symm (by omega) htcz.1
  have habs' : ∀ ents', WalAbsD C Mr d lay ents' →
      WalAbsD C Mr d (tailLay lay pre (rzSeg g0 true tg k) lay.wr) ents' := fun ents' h =>
    walAbsD_rzStartT h hs hwt (by omega) hX
  have hstep : TailCrashStepF C Mr d lay pre g0 (rzSeg g0 true tg k) lay.wr cl n := by
    intro e0 hF hndF
    have hF' := walAbsD_full_tail habs hF (habs' ents habs) hs rfl rfl hndF rfl rfl (Nat.le_refl _)
    rw [← tailLay_unpurge] at hF'
    exact tailCrashStep_rzStartRT (cl := cl) (k := n) hC hF hF' ((repOld_unpurge _ habs.nonempty).2 hR)
      hS hndF (by simp [hs]) hsz.symm htcz hk htg
  exact ⟨walsOk_tailA hW hd hl hs rfl rfl (by simp [rzSeg, hcut]) habs' hstep,
    fun K c h => dirKeysOk_tailA hW hd hl hstep h, repOld_rzCands hs rfl hR hX.1 hX.2⟩

/-- **The truncate's landing at `tg ∈ [wr, size]`** (`rzLand_pure` at `tg`). -/
theorem rzLand_pureT {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {k tg : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [rzSeg g0 true tg k])
    (hlen : g0.bs.length = g0.om.size) (hwt : lay.wr ≤ tg) (htg : tg ≤ g0.om.size)
    (hhi : g0.om.size ≤ g0.om.hi) (hcut : g0.om.cut = none) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzLand g0 tg k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzLand g0 tg k) lay.wr]> Ls) cl n K c) := by
  have hstep : TailCrashStepF C Mr d lay pre (rzSeg g0 true tg k) (rzLand g0 tg k) lay.wr cl n :=
    fun e0 hF hndF => tailCrashStep_rzLand (C := C) (Mr := Mr) (cl := cl) (k := n) hndF (by simp [hs])
      hlen htg hhi
  refine ⟨walsOk_tailA hW hd hl hs rfl rfl ?_
    (fun ents h => walAbsD_rzLandT h hs hlen hwt htg hcut hhi) hstep,
    fun K c h => dirKeysOk_tailA hW hd hl hstep h⟩
  simp [rzLand, rsPostK, rsPost, OsMeta.announce, hcut]

end pure

end WalFs
end EtcdGrove
end Perennial

end
