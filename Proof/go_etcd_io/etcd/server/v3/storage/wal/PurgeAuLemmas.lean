/- Lean-first (no Rocq counterpart).

# A purge's removal: the invariant's resources after its commit (unit `locks`, session 9)

The resource parts of `walInvBody` after a purge's removal (`walPurge_osAUnc`, `PurgeAu.lean`): the
purged layout `purgeLayP lay g0` lists the same segments (`g0` moved into the removed ones), keeps the
tail and its fields, and the state moves to `purSt` (histories and metadata unchanged). So:
- `segsAll_sep_same`: a resource per segment carries over; `laysResF_purge`;
- `walTailsRes_purge`: the tails (the tail record reads the cuts and the write position, the last segment,
  which a purge keeps);
- `walParked_purge`: the parked resources, the WAL directory's claim replaced (it is out: the handle's
  record `o.D`), its others (its non-`.wal` names not lent) a submap of the old ones (`walOthersL_replSub`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeCommitPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutAu

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

theorem purgeLayP_getLast? {lay : WalLay} {g0 : SegG} {gs : List SegG} (hs : lay.segs = g0 :: gs)
    (hgs : gs ≠ []) : (purgeLayP lay g0).segs.getLast? = lay.segs.getLast? := by
  simp only [purgeLayP_segs, hs, List.tail_cons]
  cases gs with
  | nil => exact absurd rfl hgs
  | cons g1 gs' => rw [List.getLast?_cons_cons]

theorem tailIdle_purgeLayP {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g0 : SegG}
    (hg : (purgeLayP lay g0).segs.getLast? = lay.segs.getLast?) (h : TailIdle C Mr d lay) :
    TailIdle C Mr d (purgeLayP lay g0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun g hg' => h1 g (hg ▸ hg'), h2, fun g hg' => h3 g (hg ▸ hg'), h4, fun g hg' => h5 g (hg ▸ hg')⟩

theorem repOld_purgeLayP {lay : WalLay} {g0 : SegG}
    (hg : (purgeLayP lay g0).segs.getLast? = lay.segs.getLast?) (h : RepOld lay) :
    RepOld (purgeLayP lay g0) :=
  ⟨h.1, fun g hg' => h.2 g (hg ▸ hg')⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A resource per segment, a layout replaced by one listing the same segments.** -/
theorem segsAll_sep_same (Φ : SegG → IProp GF) (Ls : GMap GoString WalLay) (dir : GoString)
    (lay lay' : WalLay) (hl : Ls !! dir = some lay) (he : lay'.pg ++ lay'.segs = lay.pg ++ lay.segs) :
    ([∗list] x ∈ segsAll Ls, Φ x) ⊢ [∗list] x ∈ segsAll (<[dir := lay']> Ls), Φ x := by
  refine (segsAll_sep_map Φ Ls).1.trans ?_
  refine (BigSepM.bigSepM_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] x ∈ lay.pg ++ lay.segs, Φ x)) hl).1.trans ?_
  refine Entails.trans ?_ (segsAll_sep_map Φ _).2
  refine Entails.trans ?_ (BigSepM.bigSepM_insert_delete (Φ := fun (_ : GoString) (lay : WalLay) =>
    iprop([∗list] x ∈ lay.pg ++ lay.segs, Φ x))).2
  refine sep_mono ?_ .rfl
  rw [he]

theorem laysResF_purge (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) (dir : GoString) (lay : WalLay)
    (g0 : SegG) (gs : List SegG) (hl : Ls !! dir = some lay) (hs : lay.segs = g0 :: gs) :
    laysResF (L := L) F Ls ⊢ laysResF (L := L) F (<[dir := purgeLayP lay g0]> Ls) :=
  segsAll_sep_same _ Ls dir lay _ hl (purgeLayP_all hs)

/-- **The tails after the removal** (see the file header). -/
theorem walTailsRes_purge (C : WalCodec) (Mr : WalMarshal) (s s' : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (lay : WalLay) (g0 : SegG) (gs : List SegG)
    (hl : Ls !! dir = some lay) (hs : lay.segs = g0 :: gs) (hgs : gs ≠ [])
    (h : ∀ k d, s.wal !! k = some d →
      ∃ d', s'.wal !! k = some d' ∧ d'.H = d.H ∧ d'.metadata = d.metadata)
    (h' : ∀ k d', s'.wal !! k = some d' →
      ∃ d, s.wal !! k = some d ∧ d'.H = d.H ∧ d'.metadata = d.metadata) :
    walTailsRes (W := W) C Mr s Ls F ⊢ walTailsRes (W := W) C Mr s' (<[dir := purgeLayP lay g0]> Ls) F := by
  refine (walTailsRes_mono C Mr s s' Ls F h h').trans ?_
  have hg := purgeLayP_getLast? (g0 := g0) hs hgs
  letI := walAllG (W := W)
  unfold walTailsRes
  iintro ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  iexists T
  iframe HTa
  isplitr
  · ipureintro
    intro i hi
    obtain ⟨d2, γ2, l2, g2, hT2, hl2, hg2, hi2⟩ := HTo i hi
    by_cases hd : d2 = dir
    · subst hd
      rw [hl] at hl2; cases hl2
      exact ⟨d2, γ2, purgeLayP lay g0, g2, hT2, GMap.lookup_insert_eq _ _ _, by rw [hg]; exact hg2, hi2⟩
    · exact ⟨d2, γ2, l2, g2, hT2, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hd)]; exact hl2, hg2, hi2⟩
  isplitr
  · ipureintro
    intro k d la hk hd hla
    by_cases e : k = dir
    · subst e
      rw [GMap.lookup_insert_eq] at hla; cases hla
      exact tailIdle_purgeLayP hg (HTi k d lay hk hd hl)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hla
      exact HTi k d la hk hd hla
  isplitl [HTm]
  · iapply BigSepM.bigSepM_mono (fun {k γ'} _ => ?_) $$ HTm
    iintro ⟨%d', %lay1, %g', %hp', Hv⟩
    obtain ⟨hd', hl', hg1, hZ', hB'⟩ := hp'
    by_cases e : k = dir
    · subst e
      rw [hl] at hl'; cases hl'
      iexists d', purgeLayP lay g0, g'
      rw [show tailG d' (purgeLayP lay g0) g'.ino (F !! g'.ino) = tailG d' lay g'.ino (F !! g'.ino) from rfl]
      iframe Hv
      ipureintro
      exact ⟨hd', GMap.lookup_insert_eq _ _ _, by rw [hg]; exact hg1, hZ', hB'⟩
    · iexists d', lay1, g'
      iframe Hv
      ipureintro
      exact ⟨hd', by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl', hg1, hZ', hB'⟩
  · iapply walLentRes_insert_same T _ dir lay (purgeLayP lay g0) hl rfl id
      (fun _ h => Or.inr (repOld_purgeLayP hg h)) (fun _ h => h)
      (fun _ h => h.imp id (repOld_purgeLayP hg)) $$ HL

/-- `walOthersL` with one claim replaced by one whose others are a submap of the old one's. -/
theorem walOthersL_replSub {Ls Ls' : GMap GoString WalLay} {D : List (Ino × NameSet)}
    {l1 l2 : List Claim} {c c' : Claim}
    (hL : ∀ c1 ∈ l1 ++ l2, WalDirClaimOf Ls' c1 → WalDirClaimOf Ls c1)
    (hc : WalDirClaimOf Ls' c' → WalDirClaimOf Ls c ∧ othersOf D c'.1 c'.2.2.cur ⊆ othersOf D c.1 c.2.2.cur) :
    walOthersL (L := L) Ls D (l1 ++ c :: l2) ⊢ walOthersL (L := L) Ls' D (l1 ++ c' :: l2) := by
  unfold walOthersL
  iintro H
  icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ H with ⟨H1, H2⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨Hc, H2⟩
  iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
  isplitl [H1]
  · have h := walOthersL_mono (L := L) (Ls := Ls) (Ls' := Ls') (D := D) (D' := D) (cl := l1)
      (fun c1 hc1 h1 => ⟨hL c1 (List.mem_append_left _ hc1) h1, rfl⟩)
    unfold walOthersL at h
    iapply h $$ H1
  iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
  isplitl [Hc]
  · by_cases h' : WalDirClaimOf Ls' c'
    · obtain ⟨h1, h2⟩ := hc h'
      rw [if_pos h', if_pos h1]
      unfold walOthers
      iapply BigSepM.bigSepM_subseteq h2 $$ Hc
    · rw [if_neg h']; iclear Hc; iempintro
  · have h := walOthersL_mono (L := L) (Ls := Ls) (Ls' := Ls') (D := D) (D' := D) (cl := l2)
      (fun c1 hc1 h1 => ⟨hL c1 (List.mem_append_right _ hc1) h1, rfl⟩)
    unfold walOthersL at h
    iapply h $$ H2

/-- **The parked resources after the removal** (see the file header): the segments the same list, the WAL
directory's claim `c` (out: its key in the handle's record) replaced by `c'` with the same key and, off the
`.wal` names, no more entries. -/
theorem walParked_purge (Ls : GMap GoString WalLay) (l1 l2 : List Claim) (c c' : Claim) (dir : GoString)
    (lay : WalLay) (g0 : SegG) (gs : List SegG) (F : GMap Ino SegFl) (o : WalOut)
    (hl : Ls !! dir = some lay) (hs : lay.segs = g0 :: gs) (hkey : c'.1 = c.1 ∧ c'.2.1 = c.2.1)
    (hD : (c.1, c.2.1) ∈ o.D)
    (hsub : ∀ b n, walNameP b = false → c'.2.2.cur !! b = some n → c.2.2.cur !! b = some n) :
    ⊢ walParked (L := L) (W := W) Ls (l1 ++ c :: l2) F -∗ walOutFrag (W := W) o -∗
      walParked (L := L) (W := W) (<[dir := purgeLayP lay g0]> Ls) (l1 ++ c' :: l2) F ∗ walOutFrag (W := W) o := by
  classical
  have hj : (purgeLayP lay g0).j = lay.j := rfl
  unfold walParked
  iintro ⟨%bf, %o', Ha, Hoa, %hb, Hs, Hc, Ht, Hw⟩ Hf
  icases walOut_agree (W := W) o' o $$ Hoa Hf with %ho
  subst ho
  iframe Hf
  iexists bf, o'
  iframe Ha Hoa
  isplitr
  · ipureintro; exact hb
  isplitl [Hs]
  · iapply segsAll_sep_same (fun x => iprop(if x.ino ∈ o'.O then emp else segResP (L := L) x)) Ls dir
      lay _ hl (purgeLayP_all hs) $$ Hs
  isplitl [Hc]
  · icases (BigSepL.bigSepL_append (PROP := IProp GF)).1 $$ Hc with ⟨H1, H2⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H2 with ⟨-, H2⟩
    iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
    have hP : ∀ c1, ParkedClaim (<[dir := purgeLayP lay g0]> Ls) o'.D c1 ↔ ParkedClaim Ls o'.D c1 := by
      intro c1
      unfold ParkedClaim
      rw [walDirClaimOf_insert hl hj c1]
    isplitl [H1]
    · iapply BigSepL.bigSepL_mono (fun {k c1} _ => ?_) $$ H1
      simp only [propext (hP c1)]
      exact .rfl
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      isplitr
      · have e : ¬ ParkedClaim (<[dir := purgeLayP lay g0]> Ls) o'.D c' := fun h =>
          h.2 (by rw [hkey.1, hkey.2]; exact hD)
        rw [if_neg e]
        iempintro
      · iapply BigSepL.bigSepL_mono (fun {k c1} _ => ?_) $$ H2
        simp only [propext (hP c1)]
        exact .rfl
  isplitl [Ht]
  · iapply walTmpParked_insert Ls o'.T dir lay (purgeLayP lay g0) hl hj $$ Ht
  · have hins := fun c1 => walDirClaimOf_insert (c := c1) hl (lay' := purgeLayP lay g0) hj
    iapply walOthersL_replSub (L := L) (fun c1 _ h => (hins c1).1 h) (fun h => ⟨(walDirClaimOf_key
      hkey.1 hkey.2).1 ((hins c').1 h), ?_⟩) $$ Hw
    intro b n hbn
    rw [othersOf_lookup] at hbn ⊢
    rw [hkey.1] at hbn
    split at hbn
    · next hc0 => rw [if_pos hc0]; exact hsub b n hc0.1 hbn
    · cases hbn

end iris

end WalFs
end EtcdGrove
end Perennial

end
