/- Lean-first (no Rocq counterpart).

# The tail's access across a resize window (I3b; `notes/wal-fsext-plan.md`, I3b log, `wal-tc2`)

`walInvBody_tailW`: `walInvBody_tail` (`TailAcc.lean`) whose continuation takes the new invariant's
pure parts (`WalsOk` of the new layout, and `DirKeysOk` carried) from the caller instead of deriving
them from an exact tail of unchanged length: a resize changes the tail's length (a truncate's landing)
and opens a window on it (`SegExact` fails until the fdatasync after it), where `walsOk_tail`'s
hypotheses do not hold. The crash condition of the window layout (`CrashOk`, inside `WalsOk`) is the
caller's to prove (the open item of the I3b log).

`walParked_tailW`: `walParked_tail` without its length premise (the tail is out of the parked state, so
its parked part is `emp` either way).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The parked halves with a tail replaced** by one of the same inode (any length), the changes in
flight changed on the tail only, which is out. -/
theorem walParked_tailW (Ls : GMap GoString WalLay) (cl : List Claim) (F F' : GMap Ino SegFl)
    (dir : GoString) (lay : WalLay)
    (pre : List SegG) (g0 g : SegG) (wr' : Nat) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino)
    (hF : ∀ i, i ≠ g0.ino → F' !! i = F !! i) :
    walParkedIn (L := L) (W := W) Ls cl F g0.ino ⊢
      walParked (L := L) (W := W) (<[dir := tailLay lay pre g wr']> Ls) cl F' := by
  unfold walParkedIn walParked
  iintro ⟨%b, %o, Ha, Hoa, %hp, Hs, Hc, Ht⟩
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
    simp only [if_pos hp.2]
    exact .rfl
  isplitl [Hc]
  · iapply BigSepL.bigSepL_mono (fun {k c} _ => ?_) $$ Hc
    have e : ParkedClaim (<[dir := tailLay lay pre g wr']> Ls) o.D c ↔ ParkedClaim Ls o.D c := by
      unfold ParkedClaim; rw [walDirClaimOf_tail hl c]
    simp only [propext e]
    exact .rfl
  · iapply walTmpParked_insert Ls o.T dir lay (tailLay lay pre g wr') hl rfl $$ Ht

/-- **The right to step a tail**: its key (`ok = none`), or the token of the tail lent to the
invariant with its `old` `k` long, of kind `p` (`ok = some (k, p)`; `walLentTokB`, I3b, `wal-tc14`;
`p = true`: registered, not yet zeroed, `wal-tc15`). -/
def walTailKeyL (dir : GoString) (γ : GName) : Option (Nat × Bool) → IProp GF
  | none => walTailKey (W := W) dir γ
  | some (k, p) => walLentTokB (W := W) dir γ k p

theorem walTailKeyL_none (dir : GoString) (γ : GName) :
    walTailKeyL (W := W) dir γ none = walTailKey (W := W) dir γ := rfl

theorem walTailKeyL_some (dir : GoString) (γ : GName) (k : Nat) (p : Bool) :
    walTailKeyL (W := W) dir γ (some (k, p)) = walLentTokB (W := W) dir γ k p := rfl

instance walTailKeyL_timeless (dir : GoString) (γ : GName) (ok : Option (Nat × Bool)) :
    Timeless (walTailKeyL (W := W) dir γ ok) := by
  rcases ok with _ | ⟨k, p⟩
  · rw [walTailKeyL_none]; unfold walTailKey; letI := walAllG (W := W); infer_instance
  · rw [walTailKeyL_some]; infer_instance

/-- **The tail registered at its record's name**, and, if lent, its `old` as long as lent; F-Z unless
it is registered, not yet zeroed (then `TailZ0`, `walTailsRes`'s fact; I3b, `wal-tc15`). -/
theorem walTailKeyL_lookup (T : GMap GoString GName) (Ls : GMap GoString WalLay) (dir : GoString)
    (γ : GName) (ok : Option (Nat × Bool)) :
    ⊢ walTailsAuth (W := W) T -∗ walLentRes (W := W) T Ls -∗ walTailKeyL (W := W) dir γ ok -∗
      ⌜T !! dir = some γ ∧ (∀ k p, ok = some (k, p) → LentOk T Ls dir (γ, k, p)) ∧
        ∀ lay, Ls !! dir = some lay → TailZ0 lay → TailZK ok lay⌝ ∗ walTailsAuth (W := W) T ∗
        walLentRes (W := W) T Ls ∗ walTailKeyL (W := W) dir γ ok := by
  rcases ok with _ | ⟨k, p⟩
  · rw [walTailKeyL_none]
    iintro Ha HL Hk
    icases walTailKey_lookup T dir γ $$ Ha Hk with %HT
    icases walLentRes_zeros T Ls dir γ $$ Hk HL with ⟨%HZ, Hk, HL⟩
    iframe Ha HL Hk
    ipureintro
    exact ⟨HT, (fun _ _ h => nomatch h), fun lay hl _ => HZ lay (by rw [HT]; simp) hl⟩
  · rw [walTailKeyL_some]
    iintro Ha HL Hk
    icases walLentRes_lookup T Ls dir γ k p $$ Hk HL with ⟨%hx, Hk, HL⟩
    iframe Ha HL Hk
    ipureintro
    refine ⟨hx.1.1, fun k' p' h => by cases h; exact hx.1, fun lay hl hz => ?_⟩
    cases p
    · exact hx.2 rfl lay hl
    · exact hz

/-- **The tail's access, the new invariant's pure parts given** (see the file header), by the tail's
key or, the tail lent, its token (`walTailKeyL`, which also gives `old`'s length). -/
theorem walInvBody_tailW (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) (s : AbsDiskState) (dir : GoString) (γ : GName) (ok : Option (Nat × Bool)) (tg : TailG)
    (m : OsMeta) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKeyL (W := W) dir γ ok -∗
      tailVar (W := W) γ tg -∗ tailHeld (L := L) tg m -∗
      ∃ (Ls : GMap GoString WalLay) (cl : List Claim) (n : Nat) (F : GMap Ino SegFl) (d : WalDur)
        (lay : WalLay) (pre : List SegG) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs = pre ++ [g0] ∧
          tg = tailG d lay g0.ino (F !! g0.ino) ∧ WalsOk C Mr R jr s Ls cl n ∧
          (∃ ents, WalAbsD C Mr d lay ents) ∧ g0.om.cut = none ∧ TailZK ok lay ∧
          TailBound C Mr d lay ∧ (∀ k p, ok = some (k, p) → lay.old.length = k)⌝ ∗
        segResF (L := L) F g0 ∗ walTailKeyL (W := W) dir γ ok ∗ tailVar (W := W) γ tg ∗
        tailVar (W := W) γ tg ∗ tailHeld (L := L) tg m ∗
        (∀ (g : SegG) (wr' : Nat) (F' : GMap Ino SegFl),
          ⌜g.ino = g0.ino ∧ g.name = g0.name ∧ (∀ i, i ≠ g0.ino → F' !! i = F !! i) ∧
            (wr' = lay.wr ∨ TailZeros lay) ∧
            WalsOk C Mr R jr s (<[dir := tailLay lay pre g wr']> Ls) cl n ∧
            (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
              DirKeysOk C Mr jr s (<[dir := tailLay lay pre g wr']> Ls) cl n K c)⌝ -∗
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
  icases walTailKeyL_lookup T Ls dir γ ok $$ HTa HL Hk with ⟨%HTk, HTa, HL, Hk⟩
  obtain ⟨HT, hlent, hZK⟩ := HTk
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  obtain ⟨hd, hl, hg, hZ0, hB⟩ := hp
  have hZ : TailZK ok lay := hZK lay hl hZ0
  obtain ⟨pre, hs⟩ := List.getLast?_eq_some_iff.1 hg
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  have HW0 := HW
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
  iexists Ls, cl, n, F, d, lay, pre, g0
  isplitr
  · ipureintro
    refine ⟨hd, hl, hs, Htg, HW0, ⟨_, habs⟩, hcut0, hZ, hB, fun k p hk => ?_⟩
    obtain ⟨-, la, hla, hlen⟩ := hlent k p hk
    rw [hl] at hla; cases hla; exact hlen
  iframe Hh
  rw [Htg]
  iframe Hlast Hk Hv Hv'
  iintro %g %wr' %F' %hp Hseg Hvn
  obtain ⟨hino, hname, hF', hwr', hW', hDK'⟩ := hp
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
  · ipureintro; exact hW'
  isplitr
  · ipureintro; exact HWC
  isplitl [HTa HTm Hvn HL]
  · iexists T
    ihave HL := walLentRes_insert_same (W := W) T Ls dir lay (tailLay lay pre g wr') hl rfl id $$ HL
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
      refine ⟨hd, GMap.lookup_insert _ _ _, by simp [tailLay], ?_, hB⟩
      rcases hwr' with e | hz
      · rcases hZ0 with hz | hz
        · exact Or.inl hz
        · exact Or.inr (by simp only [tailLay]; rw [e]; exact hz)
      · exact Or.inl hz
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
  · iapply walParked_tailW Ls cl F F' dir lay pre g0 g wr' hl hs hino hF' $$ Hpk
  isplitl [Hdk Hcp]
  · iexists K, cp
    iframe Hdk Hcp
    ipureintro
    exact hDK' K cp Hdko
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
