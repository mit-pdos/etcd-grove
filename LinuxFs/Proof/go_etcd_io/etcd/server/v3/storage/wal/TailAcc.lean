/- Lean-first (no Rocq counterpart).

# The open handle's access to its tail in `walInv` (W6; `notes/wal-fsext-plan.md`, "W6 implementation log")

`walInvBody_tail`: with the handle's key to its tail record (`walTailKey dir γ`) and its half of the
record, the invariant's contents give the WAL `d` of `dir`, its layout `lay` (the segments `pre`
then the tail `g0`), the tail's part (`segResF`, idle or with a write in flight) and the other half
of the record, which agrees with the handle's; and they are given back with the tail replaced by
any `g` and the write position by any `wr'`, the writes in flight changed on the tail only, as long
as the static relation holds of the new layout (`walsOk_tail`, `TailStepPure.lean`, does the rest).
The caller lends its half of the tail's `OsMeta` while the tail is idle (`tailHeld`): with the
invariant's half, it shows the tail out of the parked state (`walParkedIn_of_halves`), so that a
change may start on it (gap B: a change in flight only on a segment out).

Also `osBytes_agree` (two runs of a file's bytes of the same length agree) and `osN_sub_nwal`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailStepPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAuLemmas
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Parked

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The extension's invariants are outside the WAL invariant's namespace. -/
theorem osN_sub_nwal : (↑osN : CoPset) ⊆ (⊤ : CoPset) \ ↑walN := by
  have h1 : (↑walN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h1 p ⟨hn, hp⟩⟩

section pure
variable [GooseExts]

/-- `SegsNamed` reads the segments only through their names and inodes. -/
theorem segsNamed_congr {segs segs' : List SegG} {ents : Ents}
    (h : ∀ g' ∈ segs', ∃ g ∈ segs, g.name = g'.name ∧ g.ino = g'.ino) (hs : SegsNamed segs ents) :
    SegsNamed segs' ents := by
  refine ⟨fun g' hg' => ?_, hs.2⟩
  obtain ⟨g, hg, hn, hi⟩ := h g' hg'
  rw [← hn, ← hi]; exact hs.1 g hg

theorem segsNamedC_congr {segs segs' : List SegG} {ents : Ents}
    (h : ∀ g' ∈ segs', ∃ g ∈ segs, g.name = g'.name ∧ g.ino = g'.ino)
    (h' : ∀ g ∈ segs, ∃ g' ∈ segs', g'.ino = g.ino) (hs : SegsNamedC segs ents) :
    SegsNamedC segs' ents := by
  refine ⟨fun g' hg' => ?_, hs.2.1, fun i hi => ?_⟩
  · obtain ⟨g, hg, hn, hi⟩ := h g' hg'
    rw [← hn, ← hi]; exact hs.1 g hg
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (hs.2.2 i hi)
    obtain ⟨g', hg', e⟩ := h' g hg
    exact List.mem_map.2 ⟨g', hg', e⟩

/-- **`WalsNamed` with a tail replaced** by one of the same name and inode. -/
theorem walsNamed_tail {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {lay : WalLay} {pre : List SegG} {g0 g : SegG} {wr' : Nat} (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hname : g.name = g0.name) (hino : g.ino = g0.ino)
    (h : WalsNamed Ls cl n) : WalsNamed (<[dir := tailLay lay pre g wr']> Ls) cl n := by
  intro dir' lay' hl'
  by_cases e : dir' = dir
  · subst e
    rw [GMap.lookup_insert] at hl'; cases hl'
    have hsub : ∀ x ∈ (tailLay lay pre g wr').segs, ∃ y ∈ lay.segs, y.name = x.name ∧ y.ino = x.ino := by
      intro x hx
      simp only [tailLay, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ⟨x, by rw [hs]; exact List.mem_append_left _ hx, rfl, rfl⟩
      · exact ⟨g0, by rw [hs]; simp, hname.symm, hino.symm⟩
    have hsub' : ∀ y ∈ lay.segs, ∃ x ∈ (tailLay lay pre g wr').segs, x.ino = y.ino := by
      intro y hy
      rw [hs] at hy
      simp only [tailLay, List.mem_append, List.mem_singleton] at hy ⊢
      rcases hy with hy | rfl
      · exact ⟨y, Or.inl hy, rfl⟩
      · exact ⟨g, Or.inr rfl, hino⟩
    obtain ⟨h1, h2⟩ := h dir' lay hl
    exact ⟨fun hj hw => segsNamed_congr hsub (h1 hj hw),
      fun m' hr => segsNamedC_congr hsub hsub' (h2 m' hr)⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
    exact h dir' lay' hl'

/-- A WAL directory's claims are the same with a tail replaced (the directory kept). -/
theorem walDirClaimOf_tail {Ls : GMap GoString WalLay} {dir : GoString} {lay : WalLay}
    {pre : List SegG} {g : SegG} {wr' : Nat} (hl : Ls !! dir = some lay) (c : Claim) :
    WalDirClaimOf (<[dir := tailLay lay pre g wr']> Ls) c ↔ WalDirClaimOf Ls c := by
  constructor
  · rintro ⟨dir', lay', hl', hj, hX⟩
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      exact ⟨dir', lay, hl, hj, hX⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact ⟨dir', lay', hl', hj, hX⟩
  · rintro ⟨dir', lay', hl', hj, hX⟩
    by_cases e : dir' = dir
    · subst e
      rw [hl] at hl'; cases hl'
      exact ⟨dir', tailLay lay pre g wr', GMap.lookup_insert _ _ _, hj, hX⟩
    · exact ⟨dir', lay', by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl', hj, hX⟩

/-- **The directory keys with a tail replaced** (the tail step's crash condition, `crashOkA_tail`,
with no alternative). -/
theorem dirKeysOk_tail {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino)
    (hlen : g.bs.length = g0.bs.length) (hzf : (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧ SegExact g0 ∧ SegExact g)
    (hZ : TailZeros lay) (hB : TailBound C Mr d lay)
    (habs' : ∀ ents, WalAbsD C Mr d lay ents → WalAbsD C Mr d (tailLay lay pre g wr') ents)
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
      obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hcl, habs, hcr⟩ := hW.1 dir' d hd
      rw [hl] at hl1; cases hl1
      have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir' lay hl
      have hnd' : ((tailLay lay pre g wr').segs.map (·.ino)).Nodup := by
        rw [hs] at hnd; simpa [tailLay, hino] using hnd
      exact crashOkA_tail hC habs (habs' _ habs) hZ hB hnd' hs rfl hino rfl rfl rfl rfl rfl hlen hzf
        (fun la h => by cases h) (h2 dir' d lay hd hl hc)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h2 dir' d' lay' hd' hl' hc

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **Two runs of a file's bytes from the same offset, of the same length, agree.** -/
theorem osBytes_agree (i : Ino) (dq1 dq2 : DFrac) :
    ∀ (off : Nat) (xs ys : List ByteG), xs.length = ys.length →
    ⊢ osBytes (L := L) i off dq1 xs -∗ osBytes (L := L) i off dq2 ys -∗ ⌜xs = ys⌝
  | _, [], [], _ => by iintro - -; ipureintro; rfl
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | off, x :: xs, y :: ys, h => by
    unfold osBytes
    iintro Hx Hy
    icases (bytesG_cons _ _ _ _ _ _).1 $$ Hx with ⟨Hx, Hxs⟩
    icases (bytesG_cons _ _ _ _ _ _).1 $$ Hy with ⟨Hy, Hys⟩
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hx Hy with %Hv
    ihave %Hr := osBytes_agree i dq1 dq2 (off + 1) xs ys (by simpa using h) $$ [Hxs] [Hys]
    · unfold osBytes; iexact Hxs
    · unfold osBytes; iexact Hys
    ipureintro; rw [Hv.2, Hr]

/-- **A half of a tail record** (`walTailsRes`'s, with the WAL's camera). -/
def tailVar (γ : GName) (tg : TailG) : IProp GF :=
  letI := walAllG (W := W)
  ghostVar γ (1 : Qp).half tg

/-- The tails' authority knows a handle's key. -/
theorem walTailKey_lookup (T : GMap GoString GName) (dir : GoString) (γ : GName) :
    ⊢ walTailsAuth (W := W) T -∗ walTailKey (W := W) dir γ -∗ ⌜T !! dir = some γ⌝ := by
  letI := walAllG (W := W)
  unfold walTailsAuth walTailKey
  exact ghost_map_lookup

/-- The segments' parts, the layout of `dir` apart. -/
theorem laysResF_del (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) (dir : GoString) (lay : WalLay)
    (hl : Ls !! dir = some lay) :
    laysResF (L := L) F Ls ⊣⊢ ([∗list] g ∈ lay.segs, segResF (L := L) F g) ∗
      laysResF (L := L) F (Iris.Std.delete Ls dir) := by
  refine (laysResF_map (L := L) F Ls).trans ?_
  refine (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, segResF (L := L) F g)) hl).trans ?_
  exact sep_congr .rfl (laysResF_map (L := L) F _).symm

/-- The segments of every layout, layout by layout (any `Φ`). -/
theorem segsAll_sep_map (Φ : SegG → IProp GF) (Ls : GMap GoString WalLay) :
    ([∗list] g ∈ segsAll Ls, Φ g) ⊣⊢ [∗map] _dir ↦ lay ∈ Ls, [∗list] g ∈ lay.segs, Φ g := by
  unfold segsAll
  rw [BigSepL.bigSepL_flatMap (PROP := IProp GF)]
  exact (BigSepM.bigSepM_toList (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] g ∈ lay.segs, Φ g)) (m := Ls)).symm

/-- **A resource per segment, with a tail replaced** (`Φ g0 ⊢ Φ g`). -/
theorem segsAll_sep_tail (Φ : SegG → IProp GF) (Ls : GMap GoString WalLay) (dir : GoString)
    (lay : WalLay) (pre : List SegG) (g0 g : SegG) (wr' : Nat) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hΦ : Φ g0 ⊢ Φ g) :
    ([∗list] x ∈ segsAll Ls, Φ x) ⊢
      [∗list] x ∈ segsAll (<[dir := tailLay lay pre g wr']> Ls), Φ x := by
  refine (segsAll_sep_map Φ Ls).1.trans ?_
  refine (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] x ∈ lay.segs, Φ x)) hl).1.trans ?_
  refine Entails.trans ?_ (segsAll_sep_map Φ _).2
  refine Entails.trans ?_ (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] x ∈ lay.segs, Φ x))).2
  refine sep_mono ?_ .rfl
  simp only [tailLay]
  rw [hs]
  refine (BigSepL.bigSepL_append (PROP := IProp GF)).1.trans ?_
  refine Entails.trans ?_ (BigSepL.bigSepL_append (PROP := IProp GF)).2
  refine sep_mono .rfl ?_
  refine (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ x => Φ x)).1.trans ?_
  exact hΦ.trans (BigSepL.bigSepL_singleton (PROP := IProp GF) (Φ := fun _ x => Φ x)).2

/-- **The caller's half of its tail's `OsMeta` while the tail is idle** (`walInvBody_tail`'s loan):
nothing with a change in flight (the change's token holds it). -/
def tailHeld (tg : TailG) (m : OsMeta) : IProp GF :=
  match tg.2.2.2.2.2 with
  | none => osMeta (L := L) tg.2.2.2.2.1 (DFrac.own (1 : Qp).half) m
  | some _ => emp

/-- **The tail is out of the parked state** (gap B): with a change in flight on it by the invariant's
fact, idle by the caller's half and the invariant's. -/
theorem walParkedIn_tail (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (g0 : SegG) (hg0 : g0 ∈ segsAll Ls) (tg : TailG) (m : OsMeta)
    (htg : tg.2.2.2.2.1 = g0.ino ∧ tg.2.2.2.2.2 = F !! g0.ino) :
    walParked (L := L) (W := W) Ls cl F ∗ segResF (L := L) F g0 ∗ tailHeld (L := L) tg m ⊢
      walParkedIn (L := L) (W := W) Ls cl F g0.ino ∗ segResF (L := L) F g0 ∗ tailHeld (L := L) tg m := by
  cases hF : F !! g0.ino with
  | some fl =>
    iintro ⟨Hp, Hs, Hh⟩
    iframe Hs Hh
    iapply walParkedIn_of_fl (L := L) Ls cl F g0.ino (by rw [hF]; simp) $$ Hp
  | none =>
    have e1 : segResF (L := L) F g0 = segRes (L := L) g0 := by unfold segResF; rw [hF]
    have e2 : tailHeld (L := L) tg m = osMeta (L := L) g0.ino (DFrac.own (1 : Qp).half) m := by
      unfold tailHeld; rw [htg.2, hF]; dsimp only; rw [htg.1]
    rw [e1, e2]
    unfold segRes
    iintro ⟨Hp, ⟨Hm, Hb⟩, Hh⟩
    icases walParkedIn_of_halves (L := L) Ls cl F g0 hg0 g0.om m $$ [Hp Hm Hh] with ⟨Hp, Hm, Hh⟩
    · iframe Hp Hm Hh
    iframe Hp Hm Hb Hh

/-- **The parked halves with a tail replaced** by one of the same inode and length, the changes in
flight changed on the tail only, which is out. -/
theorem walParked_tail (Ls : GMap GoString WalLay) (cl : List Claim) (F F' : GMap Ino SegFl)
    (dir : GoString) (lay : WalLay)
    (pre : List SegG) (g0 g : SegG) (wr' : Nat) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino) (hlen : g.bs.length = g0.bs.length)
    (hF : ∀ i, i ≠ g0.ino → F' !! i = F !! i) :
    walParkedIn (L := L) (W := W) Ls cl F g0.ino ⊢
      walParked (L := L) (W := W) (<[dir := tailLay lay pre g wr']> Ls) cl F' := by
  unfold walParkedIn walParked
  iintro ⟨%b, %o, Ha, Hoa, %hp, Hs, Hc, Ht, Hw⟩
  iexists b, o
  iframe Ha Hoa
  isplitr
  · ipureintro
    intro i hi
    by_cases he : i = g0.ino
    · rw [he]; exact hp.2
    · rw [hF i he] at hi; exact hp.1 i hi
  isplitl [Hs]
  · iapply segsAll_sep_tail (fun x => iprop(if x.ino ∈ o.O then emp else segResP (L := L) x)) Ls dir
      lay pre g0 g wr' hl hs ?_ $$ Hs
    rw [hino]
    split
    · exact .rfl
    · unfold segResP
      rw [hino, hlen]
  isplitl [Hc]
  · iapply BigSepL.bigSepL_mono (fun {k c} _ => ?_) $$ Hc
    have e : ParkedClaim (<[dir := tailLay lay pre g wr']> Ls) o.D c ↔ ParkedClaim Ls o.D c := by
      unfold ParkedClaim; rw [walDirClaimOf_tail hl c]
    simp only [propext e]
    exact .rfl
  isplitl [Ht]
  · iapply walTmpParked_insert Ls o.T dir lay (tailLay lay pre g wr') hl rfl $$ Ht
  · iapply walOthersL_mono (fun c _ hc => ⟨(walDirClaimOf_tail hl c).1 hc, rfl⟩) $$ Hw

/-- **The tail's access** (see the file header): the caller lends its half of the tail's `OsMeta`
while the tail is idle (`tailHeld`, given back). -/
theorem walInvBody_tail (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName) (tg : TailG) (m : OsMeta) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗ tailHeld (L := L) tg m -∗
      ∃ (F : GMap Ino SegFl) (d : WalDur) (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ lay.segs = pre ++ [g0] ∧ tg = tailG d lay g0.ino (F !! g0.ino) ∧
          (∃ ents, WalAbsD C Mr d lay ents) ∧ g0.om.cut = none⌝ ∗
        segResF (L := L) F g0 ∗ walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗
        tailVar (W := W) γ tg ∗ tailHeld (L := L) tg m ∗
        (∀ (g : SegG) (wr' : Nat) (F' : GMap Ino SegFl),
          ⌜g.ino = g0.ino ∧ g.om.cut = none ∧ g.bs.length = g0.bs.length ∧
            ((∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧ SegExact g0 ∧ SegExact g) ∧
            (∀ ents, WalAbsD C Mr d lay ents → WalAbsD C Mr d (tailLay lay pre g wr') ents) ∧
            (∀ i, i ≠ g0.ino → F' !! i = F !! i) ∧ g.name = g0.name⌝ -∗
          segResF (L := L) F' g -∗
          tailVar (W := W) γ (tailG d (tailLay lay pre g wr') g.ino (F' !! g.ino)) -∗
          walInvBody (L := L) (W := W) C Mr R jr r s) := by
  letI := walAllG (W := W)
  unfold tailVar
  iintro Hb Hk Hv Hh
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  icases walLentRes_zeros T Ls dir γ $$ Hk HL with ⟨%HZk, Hk, HL⟩
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  obtain ⟨hd, hl, hg, -, hB⟩ := hp
  have hZ : TailZeros lay := HZk lay (by rw [HT]; simp) hl
  obtain ⟨pre, hs⟩ := List.getLast?_eq_some_iff.1 hg
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  obtain ⟨hW1, hW2, hW3, hW4, hW5, hW6⟩ := HW
  obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := hW1 dir d hd
  rw [hl] at hl1; cases hl1
  have hnd := (segsAll_nodup_iff Ls).1 hW3
  have hg0m : g0 ∈ lay.segs := by rw [hs]; simp
  have hcut0 : g0.om.cut = none := hW4 g0 (mem_segsAll hl hg0m)
  icases (laysResF_del (L := L) F Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  rw [hs]
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hsegs with ⟨Hpre, Hlast⟩
  icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hlast with Hlast
  -- the tail is out of the parked state (gap B)
  icases walParkedIn_tail (L := L) Ls cl F g0 (mem_segsAll hl hg0m) tg m
    (by rw [Htg]; exact ⟨rfl, rfl⟩) $$ [Hpk Hlast Hh] with ⟨Hpk, Hlast, Hh⟩
  · iframe Hpk Hlast Hh
  iexists F, d, lay, pre, g0
  isplitr
  · ipureintro; exact ⟨hd, hs, Htg, ⟨_, habs⟩, hcut0⟩
  iframe Hh
  rw [Htg]
  iframe Hlast Hk Hv Hv'
  iintro %g %wr' %F' %hp Hseg Hvn
  obtain ⟨hino, hcut, hlen, hzf, habs', hF', hname⟩ := hp
  -- the other segments' parts, unchanged
  have hpre_ne : ∀ g' ∈ pre, g'.ino ≠ g0.ino := by
    intro g' hg' he
    have h := hnd.1 dir lay hl
    rw [hs, List.map_append, List.nodup_append] at h
    exact h.2.2 g'.ino (List.mem_map_of_mem hg') g0.ino (by simp) he
  have hrest_ne : ∀ g' ∈ segsAll (Iris.Std.delete Ls dir), g'.ino ≠ g0.ino := by
    intro g' hg' he
    obtain ⟨dir', lay', hl', hg''⟩ := segsAll_mem hg'
    change GMap.delete dir Ls !! dir' = some lay' at hl'
    have hne : dir' ≠ dir := by rintro rfl; rw [GMap.lookup_delete_eq] at hl'; cases hl'
    have hl'' : Ls !! dir' = some lay' := by rwa [GMap.lookup_delete_ne _ (Ne.symm hne)] at hl'
    exact hnd.2 dir' dir lay' lay hne hl'' hl g' hg'' g0 hg0m he
  ihave Hrest := laysResF_congr (L := L) F F' _ (fun g' hg' => hF' _ (hrest_ne g' hg')) $$ Hrest
  ihave Hpre : [∗list] g' ∈ pre, segResF (L := L) F' g' $$ [Hpre]
  · iapply BigSepL.bigSepL_mono (fun {k g'} hk => ?_) $$ Hpre
    have e := hF' _ (hpre_ne g' (List.mem_of_getElem? hk))
    unfold segResF; rw [e]
  iexists (<[dir := tailLay lay pre g wr']> Ls), cl, n, F'
  iframe Hg Hcl Hn HCR
  isplitr
  · ipureintro; exact Har
  isplitl [Hpre Hseg Hrest]
  · iapply (laysResF_map (L := L) F' _).2
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
      iprop([∗list] g ∈ lay.segs, segResF (L := L) F' g))).2
    isplitl [Hpre Hseg]
    · simp only [tailLay]
      iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
      iframe Hpre
      iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      iexact Hseg
    · iapply (laysResF_map (L := L) F' _).1 $$ Hrest
  isplitr
  · ipureintro
    exact walsOk_tail hC ⟨hW1, hW2, hW3, hW4, hW5, hW6⟩ hd hl hs hino hcut hlen hzf hZ hB habs'
  isplitr
  · ipureintro; exact HWC
  isplitl [HTa HTm Hvn HL]
  · iexists T
    ihave HL := walLentRes_insert_same (W := W) T Ls dir lay (tailLay lay pre g wr') hl rfl id
      (fun _ => Or.inl hZ) (fun h => absurd h (by rw [HT]; simp)) (fun _ _ => Or.inl hZ) $$ HL
    iframe HTa HL
    isplitr
    · ipureintro
      exact HTo.insert HT hl hg (by simp [tailLay]) (fun i hi =>
        if e : i = g0.ino then Or.inl (e.trans hino.symm) else Or.inr ⟨by rwa [hF' i e] at hi, e⟩)
    isplitr
    · ipureintro
      exact HTi.of_reg dir (fun h => by rw [HT] at h; cases h) (fun _ _ => rfl)
        (fun k hk => GMap.lookup_insert_ne _ _ (Ne.symm hk))
    iapply (BigSepM.bigSepM_delete (Φ := fun (k : GoString) (γ' : GName) =>
      iprop(∃ (d' : WalDur) (la : WalLay) (g' : SegG),
        ⌜s.wal !! k = some d' ∧ (<[dir := tailLay lay pre g wr']> Ls) !! k = some la ∧
          la.segs.getLast? = some g' ∧ TailZ0 la ∧ TailBound C Mr d' la⌝ ∗
        ghostVar γ' (1 : Qp).half (tailG d' la g'.ino (F' !! g'.ino)))) HT).2
    isplitl [Hvn]
    · iexists d, (tailLay lay pre g wr'), g
      iframe Hvn
      ipureintro
      exact ⟨hd, GMap.lookup_insert _ _ _, by simp [tailLay], Or.inl hZ, hB⟩
    · iapply BigSepM.bigSepM_mono (fun {k γ'} hk => ?_) $$ HTm
      have hne : k ≠ dir := by
        change GMap.delete dir T !! k = some γ' at hk
        rintro rfl; rw [GMap.lookup_delete_eq] at hk; cases hk
      iintro ⟨%d', %lay', %g', %hp', Hv''⟩
      obtain ⟨hd', hl', hg', hZ', hB'⟩ := hp'
      have hg'm : g' ∈ lay'.segs := List.mem_of_getLast? hg'
      have he : F' !! g'.ino = F !! g'.ino :=
        hF' _ (hnd.2 k dir lay' lay hne hl' hl g' hg'm g0 hg0m)
      iexists d', lay', g'
      rw [he]
      iframe Hv''
      ipureintro
      exact ⟨hd', by rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hl', hg', hZ', hB'⟩
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact walsNamed_tail hl hs hname hino HNm
  isplitl [Hpk]
  · iapply walParked_tail Ls cl F F' dir lay pre g0 g wr' hl hs hino hlen hF' $$ Hpk
  isplitl [Hdk Hcp]
  · iexists K, cp
    iframe Hdk Hcp
    ipureintro
    exact dirKeysOk_tail hC ⟨hW1, hW2, hW3, hW4, hW5, hW6⟩ hd hl hs hino hlen hzf hZ hB habs' Hdko
  isplitr
  · ipureintro
    exact walsAt_insert hl rfl rfl HAt
  isplitl [Hnms]
  · iapply walNamesRes_insert _ _ _ _ _ _ (tailLay lay pre g wr') hl rfl rfl $$ Hnms
  ipureintro; exact Hbd

end iris

end WalFs
end EtcdGrove
end Perennial

end
