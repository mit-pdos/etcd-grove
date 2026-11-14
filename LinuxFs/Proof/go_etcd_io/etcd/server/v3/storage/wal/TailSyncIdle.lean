/- Lean-first (no Rocq counterpart).

# The fdatasync of an idle tail (the W7-W12 log of `notes/wal-fsext-plan.md`, sixth session)

`Close` of a handle that never registered its WAL's tail (`WAL.Close.specOpening`: `Open`'s handle
before `ReadAll`) runs `sync()`, whose `fileutil.Fdatasync(w.tail().File)` needs the whole of the
tail's `OsMeta` and bytes: the program's halves joined with the invariant's at a step. The WAL is idle
(`TailIdle`, `walTailsRes`'s `WalTailIdle`), so its tail is synced already (`TailSynced`: every byte
durable, zeros known only past its end): the step changes nothing the invariant says but the
segment's `OsMeta` (`OsMeta.synced`), the layout becoming `syncLay lay pre g0` (its bytes unchanged,
`so := wr`), the WAL state unchanged.

* `walAbsD_syncIdle`: the static relation of the WAL `d` itself (no mark raised) with `syncLay`.
* `fileCrashedR_unsync`: a crash of the synced tail is one of the tail before (its bytes durable, its
  size exact, zeros known only past its end).
* `crashOk_syncIdle`, `walsOk_syncIdle`, `dirKeysOk_syncIdle`, `tailIdle_syncIdle`: the invariant's
  pure parts at the new layout.
* `walInvBody_syncIdle`: the step on the invariant's body, from the WAL's key, the program's half of
  its directory's claim, the empty program half of the tails' authority and the lock token's pending
  cut flag. It gives the WAL's last segment `g0` and tells its inode by the claim's names
  (`walInos hj.cur = lay.segs.map ino`): the program's file is the tail if it is at the last `.wal`
  name of the claim.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- Every byte durable: the bytes after a sync are the same. -/
theorem map_durB_of_dur {bs : List ByteG} (h : ∀ y ∈ bs, y = durB y.1) :
    bs.map (fun y => durB y.1) = bs :=
  (List.map_congr_left (fun y hy => (h y hy).symm)).trans (List.map_id' bs)

/-- **The static relation after an idle tail's fdatasync**: the WAL itself (no mark raised: every
synced frame was below `so ≤ wr` already). -/
theorem walAbsD_syncIdle {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (h : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hex : SegExact g0) (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    WalAbsD C Mr d (syncLay lay pre g0) ents := by
  have h' := walAbsD_sync h hs hex htail
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hso : lay.so ≤ lay.wr :=
    (h.lastEx (fun g hg => by rw [hg0] at hg; cases hg; exact hex) g0 hg0).1
  exact ⟨h'.names, h'.cuts, h'.nameBound, h'.cut, h'.metas, h'.intact, h'.last,
    ⟨h.synced.1, Nat.le_trans h.synced.2 hso⟩, h.lastSynced, h'.fit, h'.tailStop, h'.nonempty, h'.cutPos, h'.seqName⟩

/-- **A crash of the synced tail is one of the tail before** (see the file header). -/
theorem fileCrashedR_unsync {g : SegG} {fo : Option Fs.OsFile} (hsz : g.om.size = g.bs.length)
    (hex : SegExact g) (hdur : ∀ y ∈ g.bs, y = durB y.1)
    (hzf : ∀ z, g.om.zf = some z → g.bs.length ≤ z)
    (h : FileCrashedR (syncTail g).om [(0, DFrac.own (1 : Qp).half, (syncTail g).bs)] fo) :
    FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] fo := by
  have hbs : (syncTail g).bs = g.bs := map_durB_of_dur hdur
  rw [hbs] at h
  intro f' hf'
  obtain ⟨himg, hlo, hhi, hrun, -, -⟩ := h f' hf'
  have hlo' : (syncTail g).om.lo = g.om.size := rfl
  have hhi' : (syncTail g).om.hi = g.om.size := rfl
  have hsz' : f'.size = g.bs.length := by omega
  refine ⟨himg, by rw [hex.1]; omega, by rw [hex.2]; omega, ?_, ?_, ?_⟩
  · intro r hr k hk hks
    rcases hrun r hr k hk hks with h1 | ⟨h1, h2⟩
    · exact .inl h1
    · exact .inr ⟨by rw [hex.1]; omega, h2⟩
  · intro z hz b hzb hb
    have := hzf z hz; omega
  · intro b c hb _ hb2
    omega

/-- **The crash condition after an idle tail's fdatasync** (see the file header): every image of the
new layout is one of the old, the layouts having the same directory, cuts and inodes. -/
theorem crashOk_syncIdle {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {cl : List Claim} {n : Nat} {pre : List SegG} {g0 : SegG}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0]) (hex : SegExact g0)
    (hsy : TailSynced lay) (hnd : (lay.segs.map (·.ino)).Nodup) (hok : CrashOk C Mr d lay cl n) :
    CrashOk C Mr d (syncLay lay pre g0) cl n := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hTE : TailExact lay := fun g hg => by rw [hg0] at hg; cases hg; exact hex
  have hsz0 := (habs.metas g0 (List.mem_of_getLast? hg0)).1
  have hinos : (syncLay lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) := by
    rw [hs]; simp [syncLay, syncTail]
  have hpre : ∀ g' ∈ pre, g'.ino ≠ g0.ino := by
    intro g' hg' he
    rw [hs, List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 _ (List.mem_map_of_mem hg') _ (by simp) he
  -- every segment's bytes durable
  have hdurAll : ∀ g' ∈ lay.segs, ∀ y ∈ g'.bs, y = durB y.1 := by
    intro g' hg'
    have hg'' := hg'
    rw [hs, List.mem_append, List.mem_singleton] at hg''
    rcases hg'' with hgp | rfl
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem hgp
      have hk' : lay.segs[k]? = some g' := by
        rw [hs, List.getElem?_append_left ((List.getElem?_eq_some_iff.1 hk).1)]; exact hk
      have hkl : k + 1 < lay.segs.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1; rw [hs]; simp; omega
      rw [habs.intact k g' hkl hk']; intro y hy; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
    · exact (hsy g' hg0).1
  intro m' fo hr hf hnmd hw
  have hf0 : ∀ g' ∈ lay.segs, FileCrashedR g'.om [(0, DFrac.own (1 : Qp).half, g'.bs)] (fo g'.ino) := by
    intro g' hg'
    rw [hs, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hf g' (by simp [syncLay, hg'])
    · exact fileCrashedR_unsync hsz0 hex (hsy g' hg0).1 (hsy g' hg0).2
        (hf (syncTail g') (by simp [syncLay]))
  have hn0 : ∀ g' ∈ lay.segs, g'.ino ∈ walInos (entsOf m' lay.j) → (fo g'.ino).isSome := by
    intro g' hg' hnd'
    rw [hs, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hnmd g' (by simp [syncLay, hg']) hnd'
    · exact hnmd (syncTail g') (by simp [syncLay]) hnd'
  have hw0 : W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay)
      (segRzOf lay) := by
    apply w1G_durable
    intro i bs hbs
    obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some_ex
      (fun g1 hg1 => Nat.le_of_eq (habs.metasEx hTE g1 hg1).2.2.2) hbs
    refine ⟨hdurAll g' hg', ?_⟩
    cases hfg : fo g'.ino with
    | none => right; simp [imgOf]
    | some f' =>
      left
      have hm := habs.metasEx hTE g' hg'
      have hfc := hf0 g' hg'
      rw [hfg] at hfc
      simp only [imgOf, Option.map_some, Option.getD_some]
      exact img_durable hfc (hdurAll g' hg') hm.2.2.1 hm.2.2.2
  exact crashTo_congr_lay (lay := lay) (lay' := syncLay lay pre g0) rfl rfl rfl rfl rfl hinos
    (hok m' fo hr hf0 hn0 hw0)

/-- **The idle tail after its fdatasync is idle** (`TailIdle` at `syncLay`). -/
theorem tailIdle_syncIdle {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hid : TailIdle C Mr d lay) : TailIdle C Mr d (syncLay lay pre g0) := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hsz0 := (habs.metas g0 (List.mem_of_getLast? hg0)).1
  have hg : (syncLay lay pre g0).segs.getLast? = some (syncTail g0) := by simp [syncLay]
  refine ⟨fun g hg' => ?_, hid.2.1, fun g hg' => ?_, rfl, fun g hg' => ?_⟩
  · rw [hg] at hg'; cases hg'
    simp [SegExact, syncTail, OsMeta.synced, hsz0]
  rotate_left
  · rw [hg] at hg'; cases hg'
    simpa [syncTail, OsMeta.synced] using hid.maps g0 hg0
  · rw [hg] at hg'; cases hg'
    refine ⟨fun y hy => ?_, fun z hz => ?_⟩
    · simp only [syncTail, List.mem_map] at hy
      obtain ⟨x, -, rfl⟩ := hy; rfl
    · simp only [syncTail, OsMeta.synced, Option.some.injEq] at hz
      subst hz
      simp only [syncTail, List.length_map]
      rw [← hsz0]
      show g0.om.size ≤ g0.om.syncZ
      unfold OsMeta.syncZ; have := le_pageEnd g0.om.size; split <;> omega

/-- **`WalsOk` after an idle tail's fdatasync** (the WAL state unchanged). -/
theorem walsOk_syncIdle {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hid : TailIdle C Mr d lay) (hok : CrashOk C Mr d lay cl n) :
    WalsOk C Mr R jr s (<[dir := syncLay lay pre g0]> Ls) cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hex : SegExact g0 := hid.1 g0 hg0
  have hsub : ∀ dir' lay', (<[dir := syncLay lay pre g0]> Ls) !! dir' = some lay' →
      ∃ lay1, Ls !! dir' = some lay1 ∧ (lay'.segs.map (·.ino)).Sublist (lay1.segs.map (·.ino)) := by
    intro dir' lay' h
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at h; cases h
      exact ⟨lay, hl, by rw [syncLay_inos lay pre g0 hs]; exact List.Sublist.refl _⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
      exact ⟨lay', h, List.Sublist.refl _⟩
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn => ?_, segsAll_nodup_sub h3 hsub, fun g' hg' => ?_, h5, h6⟩
  · by_cases e : dir' = dir
    · subst e
      rw [hd] at hd'; cases hd'
      obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, -⟩ := h1 dir' d hd
      have e : lay1 = lay := by rw [hl] at hl1; exact (Option.some.inj hl1).symm
      rw [e] at hjr hnm hc habs
      have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 h3).1 dir' lay hl
      exact ⟨syncLay lay pre g0, nm, hj, GMap.lookup_insert _ _ _, hA, hjr, hnm, hc,
        walAbsD_syncIdle habs hs hex hid.2.1,
        ⟨none, (fun _ h => nomatch h), (crashOkA_none_iff _ _ _ _ _ _).2
          (crashOk_syncIdle habs hs hex hid.synced hnd hok)⟩⟩
    · obtain ⟨lay1, nm, hj, hl1, rest⟩ := h1 dir' d' hd'
      exact ⟨lay1, nm, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · have e : dir' ≠ dir := by rintro rfl; rw [hd] at hn; cases hn
    rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact h2 dir' hn
  · obtain ⟨dir', lay', hl', hg''⟩ := segsAll_mem hg'
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      simp only [syncLay, List.mem_append, List.mem_singleton] at hg''
      rcases hg'' with hg'' | rfl
      · exact h4 g' (mem_segsAll hl (by rw [hs]; exact List.mem_append_left _ hg''))
      · exact h4 g0 (mem_segsAll hl (by rw [hs]; simp))
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h4 g' (mem_segsAll hl' hg'')

/-- **The directory keys after an idle tail's fdatasync**, no cut pending. -/
theorem dirKeysOk_syncIdle {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hid : TailIdle C Mr d lay)
    (h : DirKeysOk C Mr jr s Ls cl n K none) :
    DirKeysOk C Mr jr s (<[dir := syncLay lay pre g0]> Ls) cl n K none := by
  obtain ⟨h1, h2, h3⟩ := h
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  refine ⟨fun dir' j X hk => ?_, fun dir' d' lay' hd' hl' hc => ?_, h3.insert hl rfl⟩
  · obtain ⟨lay1, hj, hl1, rest⟩ := h1 dir' j X hk
    by_cases e : dir' = dir
    · subst e; rw [hl] at hl1; cases hl1
      exact ⟨syncLay lay pre g0, hj, GMap.lookup_insert _ _ _, rest⟩
    · exact ⟨lay1, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      rw [hd] at hd'; cases hd'
      obtain ⟨lay1, nm1, hj1, hl1, -, -, -, -, habs, -⟩ := hW.1 dir' d hd
      rw [hl] at hl1; cases hl1
      have hnd : (lay.segs.map (·.ino)).Nodup :=
        ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir' lay hl
      have hok := (crashOkA_none_iff _ _ _ _ _ _).1 (h2 dir' d lay hd hl (by simp))
      exact (crashOkA_none_iff _ _ _ _ _ _).2
        (crashOk_syncIdle habs hs (hid.1 g0 hg0) hid.synced hnd hok)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h2 dir' d' lay' hd' hl' hc

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The invariant's half of a claim of `cl` agrees with a half the program holds. -/
theorem osClaims_agree (cl : List Claim) (c : Claim) (hc : c ∈ cl) (h0 : NamesH) :
    osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) h0 ⊢
      ⌜h0 = c.2.2⌝ ∗ osClaims L (cl.map (fun c => (c, DFrac.own (1 : Qp).half))) ∗
        osNames (L := L) c.1 c.2.1 (DFrac.own (1 : Qp).half) h0 := by
  have hmem : (c, DFrac.own (1 : Qp).half) ∈ cl.map (fun c => (c, DFrac.own (1 : Qp).half)) :=
    List.mem_map_of_mem hc
  unfold osClaims
  iintro ⟨H, Hn⟩
  icases (BigSepL.bigSepL_mem_acc (Φ := fun c : Claim × DFrac =>
    osNames (L := L) c.1.1 c.1.2.1 c.2 c.1.2.2) hmem) $$ H with ⟨Hc, H⟩
  icases osNames_agree (L := L) c.1 c.2.1 _ _ h0 c.2.2 $$ Hn Hc with %he
  iframe Hn
  isplitr
  · ipureintro; exact he
  iapply H $$ Hc

/-- **An idle tail's fdatasync on the invariant** (see the file header): from the WAL's key, the
program's half of its directory's claim, the empty program half of the tails' authority and the lock
token's pending-cut flag, the WAL's layout (the segments `pre` then the tail `g0`, whose inodes the
claim's `.wal` names give in order) and the invariant's half of the tail; given back, the synced tail
(`segRes (syncTail g0)`, the step's outcome) or the tail unchanged (a failed sync). -/
theorem walInvBody_syncIdle (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) ∅ -∗ walCutFrag (W := W) none -∗
      ∃ (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜lay.segs = pre ++ [g0] ∧ walInos hj0.cur = lay.segs.map (·.ino) ∧
          g0.om.size = g0.bs.length⌝ ∗
        segRes (L := L) g0 ∗ walDirKey (W := W) dir j X ∗
        osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗
        walTailsFrag (W := W) ∅ ∗ walCutFrag (W := W) none ∗
        ((segRes (L := L) (syncTail g0) -∗ walInvBody (L := L) (W := W) C Mr R jr r s) ∧
         (segRes (L := L) g0 -∗ walInvBody (L := L) (W := W) C Mr R jr r s)) := by
  letI := walAllG (W := W)
  iintro Hb Hk Hn Hf Hcf
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walCut_agree cp none $$ Hcp Hcf with %Hcpe
  subst Hcpe
  icases walDirKey_lookup K dir j X $$ Hdk Hk with %hK
  obtain ⟨lay, hj, hl, hlj, -, -, hOnce, -, hOther⟩ := Hdko.1 dir j X hK
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [HW.2.1 dir h] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay1, nm, hj', hl1, -, -, -, hWDC, habs, -⟩ := HW.1 dir d hd
  rw [hl] at hl1; cases hl1
  have hjj : hj' = hj := by
    obtain ⟨X', hX', hmem, -⟩ := hWDC
    by_cases hc : (lay.j, NameSet.except X', hj') = (j, NameSet.except X, hj)
    · simp only [Prod.mk.injEq] at hc; exact hc.2.2
    · exact absurd (exceptMem_dotWal hX') (hOther _ hmem hc hlj go!".wal" walNameP_dotWal)
  subst hjj
  obtain ⟨l1, l2, hcl, -, -⟩ := hOnce
  icases osClaims_agree (L := L) cl (j, NameSet.except X, hj') (by rw [hcl]; simp) hj0 $$ [Hcl Hn] with
    ⟨%h0, Hcl, Hn⟩
  · iframe Hcl Hn
  -- the WAL is idle: no tail registered, nothing in flight
  iunfold walTailsRes at Htl
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  icases walTails_agree (W := W) T ∅ $$ HTa Hf with %hT
  subst hT
  have hF : F = ∅ := (GMap.lookup_empty_iff F).1 (TailsOnly.none_of_empty HTo)
  subst hF
  have hid : TailIdle C Mr d lay := HTi dir d lay (GMap.lookup_empty _) hd hl
  obtain ⟨pre, g0, hs⟩ : ∃ pre g0, lay.segs = pre ++ [g0] := by
    rcases List.eq_nil_or_concat lay.segs with h | ⟨pre, g0, h⟩
    · exact absurd h habs.nonempty
    · exact ⟨pre, g0, by rw [h, List.concat_eq_append]⟩
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hok : CrashOk C Mr d lay cl n :=
    (crashOkA_none_iff _ _ _ _ _ _).1 (Hdko.2.1 dir d lay hd hl (by simp))
  icases (laysResF_del (L := L) ∅ Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  rw [hs]
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hsegs with ⟨Hpre, Hlast⟩
  icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hlast with Hlast
  have he0 : ∀ i : Ino, (∅ : GMap Ino SegFl) !! i = none := fun i => GMap.lookup_empty i
  iexists lay, pre, g0
  isplitr
  · ipureintro
    exact ⟨hs, by rw [h0]; exact habs.names.1, (habs.metas g0 (List.mem_of_getLast? hg0)).1⟩
  isplitl [Hlast]
  · unfold segResF; rw [he0]; iexact Hlast
  iframe Hk Hn Hf Hcf
  isplit
  · -- synced
    iintro Hseg
    iexists (<[dir := syncLay lay pre g0]> Ls), cl, n, ∅
    iframe Hg Hcl Hcm HCR
    isplitr
    · ipureintro; exact Har
    isplitl [Hpre Hseg Hrest]
    · iapply (laysResF_map (L := L) ∅ _).2
      iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
        iprop([∗list] g ∈ lay.segs, segResF (L := L) ∅ g))).2
      isplitl [Hpre Hseg]
      · simp only [syncLay]
        iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
        iframe Hpre
        iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
        unfold segResF
        rw [he0]
        iexact Hseg
      · iapply (laysResF_map (L := L) ∅ _).1 $$ Hrest
    isplitr
    · ipureintro; exact walsOk_syncIdle HW hd hl hs hid hok
    isplitr
    · ipureintro; exact HWC
    isplitl [HTa HL]
    · unfold walTailsRes
      iexists ∅
      ihave HL := walLentRes_insert_same (W := W) ∅ Ls dir lay (syncLay lay pre g0) hl rfl id Or.inr
        (fun _ => id) (fun h => absurd (GMap.lookup_empty _) h) $$ HL
      iframe HTa HL
      isplitr
      · ipureintro; intro i hi; exact absurd (he0 i) hi
      isplitr
      · ipureintro
        intro k d' lay' _ hd' hl'
        by_cases e : k = dir
        · subst e
          rw [GMap.lookup_insert] at hl'; cases hl'
          rw [hd] at hd'; cases hd'
          exact tailIdle_syncIdle habs hs hid
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
          exact HTi k d' lay' (GMap.lookup_empty _) hd' hl'
      iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · ipureintro; exact Hab
    isplitr
    · ipureintro; exact walsNamed_relay hl hs rfl rfl rfl rfl HNm
    isplitl [Hpk]
    · iapply walParked_relay Ls cl dir lay (syncLay lay pre g0) pre g0 (syncTail g0) hl hs rfl rfl
        rfl (by simp [syncTail]) $$ Hpk
    isplitl [Hdk Hcp]
    · iexists K, none
      iframe Hdk Hcp
      ipureintro
      exact dirKeysOk_syncIdle HW hd hl hs hid Hdko
    isplitr
    · ipureintro; exact walsAt_insert hl rfl rfl HAt
    isplitl [Hnms]
    · iapply walNamesRes_insert _ _ _ _ _ _ (syncLay lay pre g0) hl rfl rfl $$ Hnms
    ipureintro; exact Hbd
  · -- the sync failed: everything back
    iintro Hlast
    iexists Ls, cl, n, ∅
    iframe Hg Hcl Hcm HCR Hpk Hnms
    isplitr
    · ipureintro; exact Har
    isplitl [Hpre Hlast Hrest]
    · iapply (laysResF_del (L := L) ∅ Ls dir lay hl).2
      iframe Hrest
      rw [hs]
      iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
      iframe Hpre
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      unfold segResF; rw [he0]; iexact Hlast
    isplitr
    · ipureintro; exact HW
    isplitr
    · ipureintro; exact HWC
    isplitl [HTa HTm HL]
    · unfold walTailsRes
      iexists ∅
      iframe HTa HTm HL
      ipureintro; exact ⟨HTo, HTi⟩
    isplitr
    · ipureintro; exact Hab
    isplitr
    · ipureintro; exact HNm
    isplitl [Hdk Hcp]
    · iexists K, none
      iframe Hdk Hcp
      ipureintro; exact Hdko
    ipureintro; exact ⟨HAt, Hbd⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
