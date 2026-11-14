/- Lean-first (no Rocq counterpart).

# A truncate's landing on the tail (I3b, `wal-tc8`; pure)

`cut` truncates the tail at its write position `wr` (`os.File.Truncate.specWalTail`). Its first step
leaves the tail as `rzSeg g0 true wr n` (`walAbsD_rzStart`, `crashOkA_rzStart`); the second, landed,
leaves it as `rzLand g0 wr n` (the bytes below `wr`, the `OsMeta` `rsPostK true true`). Here the
invariant's pure parts across the landing, from the in-flight layout (the invariant keeps only the
current layout's facts):

* `walAbsD_rzLand`: the static relation (a window with `|bs| = wr`, or exact if nothing was cut off and
  no window was open);
* `crashOkA_rzLand`: the crash condition (`crashOkA_same`: the landed tail's crashes are the in-flight
  one's, `fileCrashedR_rsPostK_rz`; its candidates the same, `segBytesX_rzLand`; the stamps the same).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.WinCrashW
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashTakeSeg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

theorem rzLand_length {g0 : SegG} {tg n : Nat} (htg : tg ≤ g0.om.size)
    (hlen : g0.bs.length = g0.om.size) : (rzLand g0 tg n).bs.length = tg := by
  simp only [rzLand, List.length_take]; omega

theorem rzLand_getElem? {g0 : SegG} {tg n b : Nat} (htg : tg ≤ g0.om.size)
    (hlen : g0.bs.length = g0.om.size) (hb : b < tg) :
    (rzLand g0 tg n).bs[b]? = (rzSeg g0 true tg n).bs[b]? := by
  rw [rzSeg_getElem?_lt hlen (by omega)]
  simp only [rzLand]
  rw [List.getElem?_take, if_pos hb]

/-- Two byte lists with the same candidates, position by position. -/
theorem getD_snd_of_map {l1 l2 : List ByteG} (h : l1.map (·.2) = l2.map (·.2)) (b : Nat) :
    (l1.getD b (0, [])).2 = (l2.getD b (0, [])).2 := by
  have := congrArg (fun l => l[b]?) h
  simp only [List.getElem?_map] at this
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases h1 : l1[b]? <;> cases h2 : l2[b]? <;> simp_all

/-- **The landing keeps the static relation** (from the in-flight layout): the tail's bytes those
below `wr`, a window open (exact only if nothing was cut off and the in-flight tail is exact). -/
theorem walAbsD_rzLand {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [rzSeg g0 true lay.wr n])
    (hlen : g0.bs.length = g0.om.size) (hwr : lay.wr ≤ g0.om.size) (hcut : g0.om.cut = none)
    (hhi : g0.om.size ≤ g0.om.hi) :
    WalAbsD C Mr d (tailLay lay pre (rzLand g0 lay.wr n) lay.wr) ents := by
  have hg1 : lay.segs.getLast? = some (rzSeg g0 true lay.wr n) := by rw [hs]; simp
  have hl1 := rzSeg_length g0 true lay.wr n
  have hl2 := rzLand_length (n := n) hwr hlen
  have hW := habs.lastWin _ hg1
  obtain ⟨hso, hwS, hbo, hwo, hB, hz0, hzS, hzZ, hWC⟩ := hW
  have hmin : min g0.om.size lay.wr = lay.wr := Nat.min_eq_right hwr
  refine walAbsD_win habs hs rfl rfl ?_ ⟨fun hx => ?_, fun _ => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show (rsPost true g0.om lay.wr lay.wr).size = _; rw [hl2]; rfl
    · show (rsPost true g0.om lay.wr lay.wr).cut = none
      simp only [rsPost, OsMeta.announce, OsMeta.touch_cut, hcut]
    · show min g0.om.lo lay.wr ≤ _; rw [hl2]; omega
    · show _ ≤ max g0.om.hi lay.wr; rw [hl2]; omega
  · -- exact after the landing: nothing was cut off, the in-flight tail exact
    have h1 : min g0.om.lo lay.wr = lay.wr := by have := hx.1; rw [hl2] at this; exact this
    have h2 : max g0.om.hi lay.wr = lay.wr := by have := hx.2; rw [hl2] at this; exact this
    have hsz : g0.om.size = lay.wr := by
      obtain ⟨-, -, -, hhi, -⟩ := habs.metas _ (List.mem_of_getLast? hg1)
      rw [hl1] at hhi
      change _ ≤ max g0.om.hi lay.wr at hhi; omega
    have hex1 : SegExact (rzSeg g0 true lay.wr n) :=
      ⟨by show min g0.om.lo lay.wr = _; rw [hl1]; omega,
       by show max g0.om.hi lay.wr = _; rw [hl1]; omega⟩
    have hbs : (rzLand g0 lay.wr n).bs = (rzSeg g0 true lay.wr n).bs := by
      simp only [rzLand, rzSeg, hmin]
      rw [List.drop_eq_nil_of_le (by omega)]; simp [rsAnn]
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := (habs.last _ hg1).1 hex1
    refine ⟨k1, k2, ?_, k4, fun b x hb => k5 b x (by rw [← hbs]; exact hb), k6, k7, k8⟩
    rw [hbs]; exact k3
  · refine ⟨⟨hso, hwS, by simp only [tailLay]; omega, by simp only [tailLay]; omega,
      fun b x hb hbw => ?_, hz0, hzS, hzZ, ?_⟩, ?_⟩
    · simp only [tailLay] at hbw ⊢
      rw [rzLand_getElem? hwr hlen hbw] at hb
      exact hB b x hb hbw
    · have hX := segBytesX_rzLand (n := n) hwr hlen hhi
      have hXl : (segBytesX (rzLand g0 lay.wr n)).length = (segBytesX (rzSeg g0 true lay.wr n)).length := by
        have := congrArg List.length hX; simpa using this
      refine hWC.same (by show max g0.om.hi lay.wr ≤ max g0.om.hi lay.wr; exact Nat.le_refl _)
        (by rw [hl2]; show lay.wr ≤ max g0.om.hi lay.wr; omega) (Nat.le_of_eq hXl.symm)
        (fun b _ => getD_snd_of_map hX b) (fun s hs => ?_)
      simpa [rzLand, rzSeg, rzMeta] using hs
    · show min g0.om.lo lay.wr ≤ lay.wr; omega

/-- **The landing keeps the crash condition** (from the in-flight layout, `crashOkA_same`). -/
theorem crashOkA_rzLand {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {alt : Option WalLay} {cl : List Claim} {k : Nat}
    {pre : List SegG} {g0 : SegG} {tg n : Nat}
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [rzSeg g0 true tg n])
    (hlen : g0.bs.length = g0.om.size) (htg : tg ≤ g0.om.size) (hhi : g0.om.size ≤ g0.om.hi)
    (hok : CrashOkA C Mr d lay alt cl k) :
    CrashOkA C Mr d (tailLay lay pre (rzLand g0 tg n) lay.wr) alt cl k := by
  have hX := segBytesX_rzLand (n := n) htg hlen hhi
  have hXl : (segBytesX (rzLand g0 tg n)).length = (segBytesX (rzSeg g0 true tg n)).length := by
    have := congrArg List.length hX; simpa using this
  have hmin : min g0.om.size tg = tg := Nat.min_eq_right htg
  refine crashOkA_same hnd hs rfl rfl rfl rfl rfl rfl rfl (fun fo h => ?_) (Nat.le_of_eq hXl.symm)
    (fun b hb => ?_) (fun s hs => ?_) hok
  · have h' := fileCrashedR_rsPostK_rz (m := g0.om) (tg := tg) (n := n) (xs := g0.bs.drop tg)
      (ys := g0.bs.take tg) htg (by simp; omega) (by simp; omega) h
    simp only [rzSeg, hmin]; exact h'
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    have e1 : ((segBytesX (rzLand g0 tg n))[b]?).map (·.2) =
        ((segBytesX (rzSeg g0 true tg n))[b]?).map (·.2) := by
      rw [← List.getElem?_map, ← List.getElem?_map, hX]
    rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem (by omega)] at e1 ⊢
    simp only [Option.map_some, Option.some.injEq] at e1
    exact e1
  · simp only [rzLand, rsPostK_rz, cond_true]
    simpa [rzSeg, rzMeta] using hs

end pure

end WalFs
end EtcdGrove
end Perennial

end
