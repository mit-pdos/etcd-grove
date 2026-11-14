/-
**`WalCloseLaw` proved** (`CloseHandle.lean`; W10 of `notes/wal-fsext-plan.md`, the W7-W12 log's fifth
session): `Close`'s put-back at a program step.

* `tmpClaims_walTmpsRes`: the pipeline names' two claims (both of `walTmps`) are `walTmpsRes` (the same
  name twice is two whole claims on one key: impossible).
* `walTailsRes_close`: the open handle's tail record removed from the invariant's part, given the
  WAL's `TailIdle` (the WAL leaves the registered ones, so `WalTailIdle` must cover it).
* `walInvBody_untail`: the body-level unregistration; the tail's synced halves (`TailMetaS`) agree
  with the layout's last segment, whose `SegExact`, `wr` and durable bytes give `TailIdle`.
* `walCloseLaw`: the update committed unchanged, the tail unregistered, then `walInvBody_unpin`
  (`OpenUnpin.lean`) with the tail's halves, the directory claim and the pipeline names, and the lock.
Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseHandle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenUnpin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailReg
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtPin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure

theorem tailsDel_single {G : Type} (dir : GoString) (γ : G) :
    GMap.delete dir (<[dir := γ]> (∅ : GMap GoString G)) = ∅ := by
  apply (GMap.lookup_empty_iff _).1
  intro k
  by_cases h : dir = k
  · subst h; exact GMap.lookup_delete_eq _ _
  · rw [GMap.lookup_delete_ne _ h, GMap.lookup_insert_ne _ _ h]; rfl

/-- A change in flight only on the one registered tail, none on it: none at all. -/
theorem tailsOnly_single_none {G : Type} {dir : GoString} {γ : G} {Ls : GMap GoString WalLay}
    {F : GMap Ino SegFl} {lay : WalLay} {g : SegG} (hl : Ls !! dir = some lay)
    (hg : lay.segs.getLast? = some g) (hF : F !! g.ino = none)
    (h : TailsOnly (<[dir := γ]> (∅ : GMap GoString G)) Ls F) : F = ∅ := by
  apply (GMap.lookup_empty_iff F).1
  intro i
  refine Classical.byContradiction fun hi => ?_
  obtain ⟨dir', γ', lay', g', hT, hl', hg', hi'⟩ := h i hi
  have hd : dir = dir' := by
    by_cases e : dir = dir'
    · exact e
    · rw [GMap.lookup_insert_ne _ _ e] at hT; cases hT
  subst hd
  rw [hl] at hl'; cases hl'
  rw [hg] at hg'; cases hg'
  exact hi (hi' ▸ hF)

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- Two whole claims on one name: impossible. -/
theorem osNames_only_excl (j : Ino) (b : GoString) (h1 h2 : NamesH) :
    osNames (L := L) j (.only [b]) (DFrac.own 1) h1 ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h2 ⊢
      False := by
  rw [osNames_of_ne _ _ (by simp : NameSet.only [b] ≠ .only []),
    osNames_of_ne _ _ (by simp : NameSet.only [b] ≠ .only [])]
  iintro ⟨H1, H2⟩
  icases gElem_valid_2 _ _ _ _ _ _ _ $$ H1 H2 with %hv
  exact absurd (DFrac.valid_own_op hv.1) (by simp)

/-- The pipeline names' claims, both of `walTmps`, are both of them (`walTmpsRes`). -/
theorem tmpClaims_walTmpsRes (j : Ino) (b b' : GoString) (hb : b ∈ walTmps) (hb' : b' ∈ walTmps) :
    tmpClaim (hG := ⟨G, L⟩) j b ∗ tmpClaim (hG := ⟨G, L⟩) j b' ⊢ walTmpsRes (hG := ⟨G, L⟩) j := by
  by_cases e : b = b'
  · subst e
    unfold tmpClaim
    iintro ⟨⟨%h1, H1, -⟩, ⟨%h2, H2, -⟩⟩
    iexfalso
    iapply osNames_only_excl j b h1 h2
    iframe H1 H2
  · unfold walTmpsRes
    simp only [walTmps, List.mem_cons, List.mem_nil_iff, or_false] at hb hb' ⊢
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl e
    · iintro ⟨H0, H1⟩; iframe H0 H1; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    · iintro ⟨H1, H0⟩; iframe H0 H1; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    · exact absurd rfl e

/-- **The open handle's tail record removed** from the invariant's part (see the file header): the
holder's half `{dir ↦ γt}`, the key and the program's half of the record; the WAL, its layout and last
segment, the record's agreement and `TailsOnly`; given the WAL's `TailIdle`, the part without the
record and the holder's half empty. -/
theorem walTailsRes_close (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (γ γt : GName) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) (<[dir := γt]> ∅) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
      ∃ (d : WalDur) (lay : WalLay) (g : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧
          tg = tailG d lay g.ino (F !! g.ino) ∧ TailsOnly (<[dir := γt]> (∅ : GMap GoString GName)) Ls F⌝ ∗
        (⌜TailIdle C Mr d lay ∧ F !! g.ino = none⌝ ==∗ walTailsRes (W := W) C Mr s Ls F ∗ walTailsFrag (W := W) ∅) := by
  letI := walAllG (W := W)
  unfold tailVar
  iintro Htl Htf Hk Hv
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HOld⟩
  icases walTails_agree (W := W) T _ $$ HTa Htf with %hT
  subst hT
  icases walTailKey_lookup _ dir γ $$ HTa Hk with %HT
  have hγ : γt = γ := by
    rw [GMap.lookup_insert] at HT; cases HT; rfl
  subst hγ
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g, %hp, Hv'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  iexists d, lay, g
  isplitr
  · ipureintro; exact ⟨hp.1, hp.2.1, hp.2.2.1, Htg, HTo⟩
  iintro %hidle
  have hu := walTails_unregister (W := W) (<[dir := γt]> ∅) dir γt
  rw [tailsDel_single] at hu
  imod hu $$ HTa Htf Hk with ⟨HTa, Htf⟩
  imodintro
  iframe Htf
  iexists ∅
  iframe HTa HOld
  isplitr
  · ipureintro
    have hF0 := tailsOnly_single_none hp.2.1 hp.2.2.1 hidle.2 HTo
    intro i hi
    exact absurd (by rw [hF0]; exact GMap.lookup_empty i) hi
  isplitr
  · ipureintro
    intro k d' lay' _ hd' hl'
    by_cases e : dir = k
    · subst e
      rw [hp.1] at hd'; cases hd'
      rw [hp.2.1] at hl'; cases hl'
      exact hidle.1
    · exact HTi k d' lay' (GMap.lookup_insert_ne _ _ e) hd' hl'
  · iapply BigSepM.bigSepM_empty.2; iempintro

/-- **The open handle's tail unregistered** at the body (see the file header): its tail record (all
written, nothing in flight), the program's synced halves of its `OsMeta` and bytes (`TailMetaS`); the
WAL's history is the record's. -/
theorem walInvBody_untail (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState)
    (dir : GoString) (γ γt : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (wr : Nat) (ino : Ino) (m : OsMeta) (bs : List ByteG) (hTM : TailMetaS m bs)
    (hwr : wr = (tailStream Mr H md cuts).length) :
    ⊢ walInvBody (L := L) (W := W) walCodec Mr R jr r s -∗ walTailsFrag (W := W) (<[dir := γt]> ∅) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs ==∗
      ∃ d : WalDur, ⌜s.wal !! dir = some d ∧ d.H = H⌝ ∗ walInvBody (L := L) (W := W) walCodec Mr R jr r s ∗
        walTailsFrag (W := W) ∅ ∗ osMeta (L := L) ino (DFrac.own (1 : Qp).half) m ∗
        osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs := by
  iintro Hb Htf Hk Hv Hm Hbs
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    HK, %HAt, Hnms, %Hbd⟩
  icases walTailsRes_close (W := W) walCodec Mr s Ls F dir γ γt _ $$ Htl Htf Hk Hv with
    ⟨%d, %lay, %g, %hp, Hclose⟩
  obtain ⟨hd, hl, hg, htg, hTO⟩ := hp
  simp only [tailG, Prod.mk.injEq] at htg
  obtain ⟨hH, hmd, hcuts, hwr', hino, hF⟩ := htg
  have hF0 : F = ∅ := tailsOnly_single_none hl hg hF.symm hTO
  subst hF0 hH hmd hcuts hwr' hino
  icases (laysResF_empty (L := L) Ls).1 $$ Hlays with Hlays
  icases (laysRes_list (L := L) Ls).1 $$ Hlays with Hlays
  have hgm : g ∈ segsAll Ls := mem_segsAll hl (List.mem_of_getLast? hg)
  have hsz := walsOk_segs_size HW g hgm
  icases (BigSepL.bigSepL_mem_acc (Φ := fun g => segRes (L := L) g) hgm) $$ Hlays with ⟨Hg1, Hlays⟩
  iunfold segRes at Hg1
  icases Hg1 with ⟨Hm2, Hb2⟩
  icases parked_osMeta_agree (L := L) g.ino _ _ m g.om $$ Hm Hm2 with %hgom
  subst hgom
  icases osBytes_agree (L := L) g.ino _ _ 0 bs g.bs (by rw [hTM.1.1, hsz]) $$ Hbs Hb2 with %hbb
  subst hbb
  ihave Hlays := Hlays $$ [Hm2 Hb2]
  · iunfold segRes; iframe Hm2 Hb2
  have hidle : TailIdle walCodec Mr d lay := by
    refine ⟨fun g' hg' => ?_, ?_, fun g' hg' => ?_⟩
    · rw [hg] at hg'; cases hg'
      refine ⟨?_, ?_⟩
      · rw [← hsz]; exact hTM.1.2.2.2.1
      · rw [← hsz]; exact hTM.1.2.2.2.2
    · rw [hwr, tailStream_eq]
    · rw [hg] at hg'; cases hg'
      exact ⟨hTM.2, fun z hz => by rw [← hsz]; exact hTM.1.2.2.1.ge z hz⟩
  imod Hclose $$ %(⟨hidle, GMap.lookup_empty _⟩ : TailIdle walCodec Mr d lay ∧ (∅ : GMap Ino SegFl) !! g.ino = none) with ⟨Htl, Htf⟩
  ihave Hlays := (laysRes_list (L := L) Ls).2 $$ Hlays
  ihave Hlays := (laysResF_empty (L := L) Ls).2 $$ Hlays
  imodintro
  iexists d
  isplitr
  · ipureintro; exact ⟨hd, rfl⟩
  iframe Htf Hm Hbs
  iexists Ls, cl, n, ∅
  iframe Hg Hcl Hcm HCR Htl Hpk Hlays HK Hnms
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  ipureintro; exact ⟨HAt, Hbd⟩

/-- **`WalCloseLaw` proved** (see the file header). -/
theorem walCloseLaw (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    WalCloseLaw (L := L) (W := W) walCodec Mr R jr r := by
  intro w dir γ γt ino j X hj H md cuts wr m bs b b' Q hTM hwr hb hb'
  iintro #Hinv Hnc Hk Hv Hm Hbs #Hdk Hn Htb Htb' Ho Htf Hnf Hopen Hpw #Hsy Hau
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top' $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%dc, Hdc, Hucl⟩
  unfold walDiskAt walDirIs
  icases Hdc with ⟨%M, HM, %HMd⟩
  icases walInvBody_mapLe walCodec Mr R jr r s M $$ Hb HM with ⟨%HMs, Hb, HM⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
  obtain ⟨ds, hsd, hle⟩ : ∃ ds, s.wal !! dir = some ds ∧ walDurLe dc ds := by
    have h1 := HMs dir
    rw [hM0] at h1
    obtain ⟨ds, hds, hle1⟩ := (walOptLe_some_iff _ _).1 h1
    exact ⟨ds, hds, walDurLe_trans hle0 hle1⟩
  imod Hcommit $$ [HM] with HQ
  · iexists M
    iframe HM
    ipureintro; exact HMd
  imod walInvBody_untail Mr R jr r s dir γ γt H md cuts wr ino m bs hTM hwr $$ Hb Htf Hk Hv Hm Hbs with
    ⟨%d, %hd, Hb, Htf, Hm, Hbs⟩
  have hdH : dc.H = H := by
    rw [hsd] at hd; obtain ⟨hd1, hd2⟩ := hd; cases hd1; rw [hle.1, hd2]
  unfold walOpenW walLockedTok
  icases Hopen with ⟨-, Hlk⟩
  have hS : ∀ g ∈ [(⟨go!"", ino, m, bs⟩ : SegG)], g.om.size = g.bs.length := by
    intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hTM.1.1.symm
  have hu := walInvBody_unpin (L := L) (W := W) walCodec Mr R jr r s dir j X hj
    [(⟨go!"", ino, m, bs⟩ : SegG)] true hS
  simp only [List.map_cons, List.map_nil, ↓reduceIte] at hu
  imod hu $$ Hb [Hlk] Htf Hnf Ho [Hm Hbs] Hn [Htb Htb'] Hdk with ⟨Hb, Hu⟩
  · unfold walLockedTok; iexact Hlk
  · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    unfold segRes; iframe Hm Hbs
  · iapply tmpClaims_walTmpsRes (L := L) j b b' hb hb'
    iframe Htb Htb'
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc
  iexists dc
  iframe HQ Hu
  rw [hdH]; iexact Hsy

end iris

end WalFs
end EtcdGrove
end Perennial

end
