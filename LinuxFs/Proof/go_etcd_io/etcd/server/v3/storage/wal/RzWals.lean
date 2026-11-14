/- Lean-first (no Rocq counterpart).

# The invariant's pure parts across a step on the tail, the crash step given (I3b, `wal-tc8`; pure)

`walsOk_tail`/`dirKeysOk_tail` (`TailStepPure.lean`, `TailAcc.lean`) derive the new layout's crash
condition from an exact tail of unchanged length (`crashOkA_tail`). A resize's steps change the
length or open a window; their crash steps are `crashOkA_rzStart` (`WinCrashW.lean`) and
`crashOkA_rzLand` (`RzLand.lean`). Here the same transports over any crash step (`TailCrashStep`):

* `crashOkW_tailA`, `walsOk_tailA`, `dirKeysOk_tailA`;
* `walsOk_rzStart`/`dirKeysOk_rzStart` and `walsOk_rzLand`/`dirKeysOk_rzLand`: the truncate's two steps
  at the write position (`os.File.Truncate.specWalTail`'s supply).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzLand
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **A step on the tail `g0` to `g` keeps the crash condition** (for any alternative layout that
does not hold the tail). -/
def TailCrashStep (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (pre : List SegG)
    (g0 g : SegG) (wr' : Nat) (cl : List Claim) (n : Nat) : Prop :=
  ∀ alt : Option WalLay, (∀ la, alt = some la → ∀ g' ∈ la.segs, g'.ino ≠ g0.ino) →
    CrashOkA C Mr d lay alt cl n → CrashOkA C Mr d (tailLay lay pre g wr') alt cl n

theorem crashOkW_tailA {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {pre : List SegG} {g0 g : SegG} {wr' : Nat} {cl : List Claim} {n : Nat}
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [g0])
    (hstep : TailCrashStep C Mr d lay pre g0 g wr' cl n)
    (hok : CrashOkW C Mr d lay cl n) : CrashOkW C Mr d (tailLay lay pre g wr') cl n := by
  obtain ⟨alt, halt, hA⟩ := hok
  have hpre : ∀ lay0, alt = some lay0 → lay0.segs <+: pre := by
    intro lay0 h
    obtain ⟨-, -, -, -, hp, hlt⟩ := halt lay0 h
    rw [hs] at hp hlt
    obtain ⟨t, ht⟩ := hp
    cases t with
    | nil => rw [List.append_nil] at ht; rw [ht] at hlt; omega
    | cons c t =>
      refine ⟨(c :: t).dropLast, ?_⟩
      have := congrArg List.dropLast ht
      rwa [List.dropLast_append_of_ne_nil (List.cons_ne_nil c t),
        List.dropLast_append_of_ne_nil (List.cons_ne_nil g0 []), List.dropLast_singleton,
        List.append_nil] at this
  refine ⟨alt, fun lay0 h => ?_, hstep alt ?_ hA⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := halt lay0 h
    have hp := hpre lay0 h
    refine ⟨h1, h2, h3, h4, hp.trans (List.prefix_append _ _), ?_⟩
    have := hp.length_le; simp [tailLay]; omega
  · intro la h g' hg' he
    have hg'p : g' ∈ pre := (hpre la h).subset hg'
    rw [hs, List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 g'.ino (List.mem_map_of_mem hg'p) g0.ino (by simp) he

/-- **`WalsOk` with a WAL's tail replaced, the crash step given.** -/
theorem walsOk_tailA {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino) (hcut : g.om.cut = none)
    (habs' : ∀ ents, WalAbsD C Mr d lay ents → WalAbsD C Mr d (tailLay lay pre g wr') ents)
    (hstep : TailCrashStep C Mr d lay pre g0 g wr' cl n) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre g wr']> Ls) cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
  have hsub : ∀ dir' lay', (<[dir := tailLay lay pre g wr']> Ls) !! dir' = some lay' →
      ∃ lay1, Ls !! dir' = some lay1 ∧ (lay'.segs.map (·.ino)).Sublist (lay1.segs.map (·.ino)) := by
    intro dir' lay' h
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at h; cases h
      refine ⟨lay, hl, ?_⟩
      rw [hs]; simp [tailLay, hino]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
      exact ⟨lay', h, List.Sublist.refl _⟩
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn => ?_, segsAll_nodup_sub h3 hsub, fun g' hg' => ?_, h5, h6⟩
  · by_cases e : dir' = dir
    · subst e
      rw [hd] at hd'; cases hd'
      obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := h1 dir' d hd
      have e : lay1 = lay := by rw [hl] at hl1; exact (Option.some.inj hl1).symm
      rw [e] at hjr hnm hc habs hcr
      have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 h3).1 dir' lay hl
      exact ⟨tailLay lay pre g wr', nm, hj, GMap.lookup_insert _ _ _, hA, hjr, hnm, hc, habs' _ habs,
        crashOkW_tailA hnd hs hstep hcr⟩
    · obtain ⟨lay1, nm, hj, hl1, rest⟩ := h1 dir' d' hd'
      exact ⟨lay1, nm, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · have e : dir' ≠ dir := by rintro rfl; rw [hd] at hn; cases hn
    rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact h2 dir' hn
  · obtain ⟨dir', lay', hl', hg''⟩ := segsAll_mem hg'
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      simp only [tailLay, List.mem_append, List.mem_singleton] at hg''
      rcases hg'' with hg'' | rfl
      · exact h4 g' (mem_segsAll hl (by rw [hs]; exact List.mem_append_left _ hg''))
      · exact hcut
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h4 g' (mem_segsAll hl' hg'')

/-- **The directory keys with a tail replaced, the crash step given.** -/
theorem dirKeysOk_tailA {C : WalCodec} {Mr : WalMarshal} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hstep : TailCrashStep C Mr d lay pre g0 g wr' cl n)
    (h : DirKeysOk C Mr jr s Ls cl n K c) :
    DirKeysOk C Mr jr s (<[dir := tailLay lay pre g wr']> Ls) cl n K c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun dir' j X hk => ?_, fun dir' d' lay' hd' hl' hc => ?_, h3.insert hl rfl⟩
  · obtain ⟨lay1, hj, hl1, rest⟩ := h1 dir' j X hk
    by_cases e : dir' = dir
    · subst e; rw [hl] at hl1; cases hl1
      exact ⟨tailLay lay pre g wr', hj, GMap.lookup_insert _ _ _, rest⟩
    · exact ⟨lay1, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      rw [hd] at hd'; cases hd'
      exact hstep none (fun la h => by cases h) (h2 dir' d lay hd hl hc)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h2 dir' d' lay' hd' hl' hc

/-! ## The truncate at the write position -/

/-- **The truncate's first step is a crash step** (`crashOkA_rzStart`), a window's least crash size at
most the write position (`hlo`: the handle's, through `os.truncSup`'s `P`; W6 log, twenty-second
session). -/
theorem tailCrashStep_rzStart {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {ents : Ents} {cl : List Claim} {k : Nat} {pre : List SegG} {g0 : SegG} {n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hZ : TailZeros lay) (hB : TailBound C Mr d lay)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [g0])
    (hn : 0 < n) (htcz : g0.om.TcZ) (hlo : ¬ SegExact g0 → g0.om.lo ≤ lay.wr) :
    TailCrashStep C Mr d lay pre g0 (rzSeg g0 true lay.wr n) lay.wr cl k := by
  intro alt halt hok
  exact crashOkA_rzStart hC habs hZ hB hnd hs htcz.1 hn
    (fun hx => ⟨hlo hx, htcz⟩) halt hok

/-- **The truncate's landing is a crash step** (`crashOkA_rzLand`), from the in-flight layout. -/
theorem tailCrashStep_rzLand {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {cl : List Claim} {k : Nat} {pre : List SegG} {g0 : SegG} {tg n : Nat}
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [rzSeg g0 true tg n])
    (hlen : g0.bs.length = g0.om.size) (htg : tg ≤ g0.om.size) (hhi : g0.om.size ≤ g0.om.hi) :
    TailCrashStep C Mr d lay pre (rzSeg g0 true tg n) (rzLand g0 tg n) lay.wr cl k :=
  fun _ _ hok => crashOkA_rzLand hnd hs hlen htg hhi hok

end pure

end WalFs
end EtcdGrove
end Perennial

end
