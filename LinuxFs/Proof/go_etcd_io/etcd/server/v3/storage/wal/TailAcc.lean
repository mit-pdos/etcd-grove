/- Lean-first (no Rocq counterpart).

# The open handle's access to its tail in `walInv` (W6; `notes/wal-fsext-plan.md`, "W6 implementation log")

`walInvBody_tail`: with the handle's key to its tail record (`walTailKey dir γ`) and its half of the
record, the invariant's contents give the WAL `d` of `dir`, its layout `lay` (the segments `pre`
then the tail `g0`), the tail's part (`segResF`, idle or with a write in flight) and the other half
of the record, which agrees with the handle's; and they are given back with the tail replaced by
any `g` and the write position by any `wr'`, the writes in flight changed on the tail only, as long
as the static relation holds of the new layout (`walsOk_tail`, `TailStepPure.lean`, does the rest).

Also `osBytes_agree` (two runs of a file's bytes of the same length agree) and `osN_sub_nwal`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailStepPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAuLemmas

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
    (h : ∀ g' ∈ segs', ∃ g ∈ segs, g.name = g'.name ∧ g.ino = g'.ino) (hs : SegsNamedC segs ents) :
    SegsNamedC segs' ents := by
  refine ⟨fun g' hg' => ?_, hs.2⟩
  obtain ⟨g, hg, hn, hi⟩ := h g' hg'
  rw [← hn, ← hi]; exact hs.1 g hg

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
    obtain ⟨h1, h2⟩ := h dir' lay hl
    exact ⟨fun hj hw => segsNamed_congr hsub (h1 hj hw),
      fun m' hr => segsNamedC_congr hsub (h2 m' hr)⟩
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

/-- **The parked halves with a tail replaced** by one of the same inode and length. -/
theorem walParked_tail (Ls : GMap GoString WalLay) (cl : List Claim) (dir : GoString) (lay : WalLay)
    (pre : List SegG) (g0 g : SegG) (wr' : Nat) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino) (hlen : g.bs.length = g0.bs.length) :
    walParked (L := L) (W := W) Ls cl ⊢
      walParked (L := L) (W := W) (<[dir := tailLay lay pre g wr']> Ls) cl := by
  unfold walParked
  iintro ⟨%b, %O, %D, Ha, %hb, Hs, Hc⟩
  iexists b, O, D
  iframe Ha
  isplitr
  · ipureintro; exact hb
  isplitl [Hs]
  · iapply segsAll_sep_tail (fun x => iprop(if x.ino ∈ O then emp else segResP (L := L) x)) Ls dir
      lay pre g0 g wr' hl hs ?_ $$ Hs
    rw [hino]
    split
    · exact .rfl
    · unfold segResP
      rw [hino, hlen]
  · iapply BigSepL.bigSepL_mono (fun {k c} _ => ?_) $$ Hc
    have e : ParkedClaim (<[dir := tailLay lay pre g wr']> Ls) D c ↔ ParkedClaim Ls D c := by
      unfold ParkedClaim; rw [walDirClaimOf_tail hl c]
    simp only [propext e]
    exact .rfl

/-- **The tail's access** (see the file header). -/
theorem walInvBody_tail (C : WalCodec) (hC : C.Ok) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗
      ∃ (F : GMap Ino SegFl) (d : WalDur) (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ lay.segs = pre ++ [g0] ∧ tg = tailG d lay g0.ino (F !! g0.ino) ∧
          (∃ ents, WalAbsD C Mr d lay ents) ∧ g0.om.cut = none⌝ ∗
        segResF (L := L) F g0 ∗ walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗
        tailVar (W := W) γ tg ∗
        (∀ (g : SegG) (wr' : Nat) (F' : GMap Ino SegFl),
          ⌜g.ino = g0.ino ∧ g.om.cut = none ∧ g.bs.length = g0.bs.length ∧
            (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧
            (∀ ents, WalAbsD C Mr d lay ents → WalAbsD C Mr d (tailLay lay pre g wr') ents) ∧
            (∀ i, i ≠ g0.ino → F' !! i = F !! i) ∧ g.name = g0.name⌝ -∗
          segResF (L := L) F' g -∗
          tailVar (W := W) γ (tailG d (tailLay lay pre g wr') g.ino (F' !! g.ino)) -∗
          walInvBody (L := L) (W := W) C Mr R jr r s) := by
  letI := walAllG (W := W)
  unfold tailVar
  iintro Hb Hk Hv
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk⟩
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, HTm⟩
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  obtain ⟨hd, hl, hg, hZ, hB⟩ := hp
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
  iexists F, d, lay, pre, g0
  isplitr
  · ipureintro; exact ⟨hd, hs, Htg, ⟨_, habs⟩, hcut0⟩
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
  isplitl [HTa HTm Hvn]
  · iexists T
    iframe HTa
    iapply (BigSepM.bigSepM_delete (Φ := fun (k : GoString) (γ' : GName) =>
      iprop(∃ (d' : WalDur) (la : WalLay) (g' : SegG),
        ⌜s.wal !! k = some d' ∧ (<[dir := tailLay lay pre g wr']> Ls) !! k = some la ∧
          la.segs.getLast? = some g' ∧ TailZeros la ∧ TailBound C Mr d' la⌝ ∗
        ghostVar γ' (1 : Qp).half (tailG d' la g'.ino (F' !! g'.ino)))) HT).2
    isplitl [Hvn]
    · iexists d, (tailLay lay pre g wr'), g
      iframe Hvn
      ipureintro
      exact ⟨hd, GMap.lookup_insert _ _ _, by simp [tailLay], hZ, hB⟩
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
  iapply walParked_tail Ls cl dir lay pre g0 g wr' hl hs hino hlen $$ Hpk

end iris

end WalFs
end EtcdGrove
end Perennial

end
