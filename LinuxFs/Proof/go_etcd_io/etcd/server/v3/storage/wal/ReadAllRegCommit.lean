/- Lean-first (no Rocq counterpart).

# `ReadAll`'s registration proved, and folded with its commit (I3b, `wal-tc18`; W1 log, twenty-eighth
session)

* `walInvBody_readReg`: `walInvBody_readState`'s look with the pending registration inside
  (`walTailsRes_registerPend`): the idle tail's record boundary (`TailIdle.bound`, finding D), its last
  segment unmapped (`TailIdle.maps`, finding C) and exact give `TailMetaR`, its `|old|` the size
  (`walAbsD_old_exact`).
* `walInvRegisterPendLaw_holds`: the law `walInvRegisterPendLaw` (`ReadAllRegPend.lean`) proved.
* **`walInv_readCommitReg`**: `walInv_readCommit` (`ReadAllCommit.lean`) with the registration in the
  same invariant opening (the coordinator's decision, 2026-11-14): the update commits at the state the
  tail record holds (`walDurLe dc d`, `d` the record's), so `ReadAll` knows the record's history and
  metadata are the committed state's. `ReadAll` (`wal-readall26`) switches to it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllRegPend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCommit
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailReg
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailLend

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

theorem getLast?_of_drop {α : Type} {l : List α} {k : Nat} {a : α}
    (h : (l.drop k).getLast? = some a) : l.getLast? = some a := by
  rw [List.getLast?_drop] at h
  split at h
  · cases h
  · exact h

section pure
variable [GooseExts]

/-- **The registered tail's `OsMeta` facts** from an idle tail's (`TailIdle`'s `TailExact` and
`TailMaps`, `WalAbsD.metas`). -/
theorem TailIdle.tailMetaR {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g : SegG} (habs : WalAbsD C Mr d lay ents) (h : TailIdle C Mr d lay)
    (hg : lay.segs.getLast? = some g) : TailMetaR g.om g.bs ∧ lay.old.length = g.om.size := by
  have hm := habs.metas g (List.mem_of_getLast? hg)
  have hex := h.1 g hg
  have hlo : g.om.lo = g.om.size := by rw [hex.1, hm.1]
  have hhi : g.om.hi = g.om.size := by rw [hex.2, hm.1]
  exact ⟨⟨hm.1.symm, h.maps g hg, hlo, hhi⟩, walAbsD_old_exact habs hg hlo hhi⟩

end pure

section body
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The WAL as `ReadAll` reads it, its tail registered, not yet zeroed** (see the file header). -/
theorem walInvBody_readReg (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH) (gs : List SegG)
    (gl : SegG)
    (hnm : ∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino))
    (hdrop : ∃ kk, (walNames hj0.cur).drop kk = gs.map (·.name))
    (hsz : ∀ g ∈ gs, g.om.size = g.bs.length) (hgl : gs.getLast? = some gl) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) ∅ -∗
      ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ==∗
      ∃ (d : WalDur) (lay : WalLay) (kk : Nat) (γ : GName),
        ⌜s.wal !! dir = some d ∧ lay.j = j ∧ WalAbsD C Mr d lay hj0.cur ∧ TailExact lay ∧
          lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ lay.segs.drop kk = gs ∧
          TailMetaR gl.om gl.bs ∧ TailZ0 lay ∧ lay.old.length = gl.om.size⌝ ∗
        walInvBody (L := L) (W := W) C Mr R jr r s ∗ walDirKey (W := W) dir j X ∗
        osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗
        walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗
        walPendTok (W := W) dir γ lay.old.length ∗
        (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay gl.ino none)) ∗
        ([∗list] g ∈ gs, osMeta (L := L) g.ino (DFrac.own (1 : Qp).half) g.om ∗
          osBytes (L := L) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) := by
  iintro Hb Hk Hn Hf Hgs
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
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
  simp only at h0
  subst h0
  icases walTailsRes_idle C Mr s Ls F $$ Htl Hf with ⟨%hidle, Htl, Hf⟩
  icases walTailsRes_none C Mr s Ls F $$ Htl Hf with ⟨%hF, Htl, Hf⟩
  have hF' : F = ∅ := (GMap.lookup_empty_iff F).1 hF
  subst hF'
  have hid : TailIdle C Mr d lay := hidle dir d lay hd hl
  have hsn : SegsNamed lay.segs hj0.cur := (HNm dir lay hl).1 hj0 hWDC
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 HW.2.2.1).1 dir lay hl
  obtain ⟨kk, hkk⟩ := hdrop
  have hn : (lay.segs.drop kk).map (·.name) = gs.map (·.name) := by
    rw [List.map_drop, ← walNames_segs hsn habs.names.1 hnd habs.names.2]; exact hkk
  have hinos := segs_drop_inos hn hsn hnm
  icases (laysResF_del (L := L) ∅ Ls dir lay hl).1 $$ Hlays with ⟨Hsegs, Hrest⟩
  icases (segResF_empty_list (L := L) lay.segs).1 $$ Hsegs with Hsegs
  icases (rs_bigSepL_take_drop (segRes (L := L)) lay.segs kk).1 $$ Hsegs with ⟨Hpre, Hsuf⟩
  icases halves_agree (L := L) gs (lay.segs.drop kk) hinos hsz
    (fun g hg => (habs.metas g (List.mem_of_mem_drop hg)).1) $$ Hgs Hsuf with ⟨%hom, Hgs, Hsuf⟩
  have hdeq := segs_drop_eq hn hsn hnm hom
  have hglL : lay.segs.getLast? = some gl := getLast?_of_drop (by rw [hdeq]; exact hgl)
  obtain ⟨htm, hold⟩ := hid.tailMetaR habs hglL
  -- the registration, not yet zeroed
  imod walTailsRes_registerPend (W := W) C Mr s Ls ∅ dir d lay gl ⟨hd, hl, hglL, hid.bound habs⟩
    $$ Htl Hf with ⟨%γ, %hz0, Htl, Hf, Hpt, Hv⟩
  isimp only [GMap.lookup_empty] at Hv
  imodintro
  iexists d, lay, kk, γ
  isplitr
  · ipureintro; exact ⟨hd, hlj, habs, hid.1, hid.2.1, hdeq, htm, hz0, hold⟩
  iframe Hk Hn Hf Hgs Hpt Hv
  iexists Ls, cl, n, ∅
  iframe Hg Hcm HCR Htl Hpk Hnms Hcl
  isplitr
  · ipureintro; exact Har
  isplitl [Hpre Hsuf Hrest]
  · iapply (laysResF_del (L := L) ∅ Ls dir lay hl).2
    iframe Hrest
    iapply (segResF_empty_list (L := L) lay.segs).2
    iapply (rs_bigSepL_take_drop (segRes (L := L)) lay.segs kk).2
    iframe
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  isplitl [Hdk Hcp]
  · iexists K, cp; iframe Hdk Hcp; ipureintro; exact Hdko
  isplitr
  · ipureintro; exact HAt
  ipureintro; exact Hbd

end body

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **`walInvRegisterPendLaw` proved** (see the file header). -/
theorem walInvRegisterPendLaw_holds (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino)
    (r : GoString) : walInvRegisterPendLaw (hG := hG) (W := W) C Mr R jr r := by
  intro dir j X hj0 gs gl hnm hdrop hsz hgl
  iintro #Hinv Hnc Hk Hn Htf Hh
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_readReg (L := hG.goose_localGS) C Mr R jr r s dir j X hj0 gs gl hnm hdrop hsz hgl
    $$ Hb Hk Hn Htf Hh with ⟨%d, %lay, %kk, %γ, %hrs, Hb, -, Hn, Htf, Hpt, Hv, Hh⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hn Hh
  iexists d, lay, kk, γ
  iframe Htf Hpt Hv
  ipureintro
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **`ReadAll`'s update committed and its tail registered at one look** (see the file header):
`walInv_readCommit`'s post with the pending registration's (`walInvRegisterPendLaw`'s), the client's
state `dc` below the registered record's `d` (`walDurLe dc d`: the same history, cut and metadata). -/
theorem walInv_readCommitReg (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (sn : w64 × w64) (j : Ino) (X : List GoString) (hj0 : NamesH)
    (gs : List SegG) (gl : SegG)
    (hnm : ∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino))
    (hdrop : ∃ kk, (walNames hj0.cur).drop kk = gs.map (·.name))
    (hsz : ∀ g ∈ gs, g.om.size = g.bs.length) (hgl : gs.getLast? = some gl)
    (Pre : WalDur → Prop) (Q : WalDur → IProp GF) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walDirKey (W := W) dir j X -∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) ∅ -∗ walNamesFrag (W := W) none -∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) -∗
      walOpening (W := W) w dir sn -∗
      (AU <{ ∃∃ d : WalDur, walDiskAt (W := W) dir d ∗ ⌜Pre d⌝ }> @ walAuMask, ∅
        <{ walDiskAt (W := W) dir d, COMM Q d }>) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗
      walNamesFrag (W := W) none ∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ∗
      walOpening (W := W) w dir sn ∗
      ∃ (dc d : WalDur) (lay : WalLay) (kk : Nat) (γ : GName) (s : AbsDiskState) (nm : GoString)
        (q : Qp) (hn : NamesH),
        Q dc ∗ walPast (W := W) s ∗ walLenLb (W := W) w dir dc.H.length ∗
        osNames (L := hG.goose_localGS) jr (.only [nm]) (DFrac.own q) hn ∗
        osLogLb (L := hG.goose_localGS) hn.next ∗
        walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗
        walPendTok (W := W) dir γ lay.old.length ∗
        (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay gl.ino none)) ∗
        ⌜Pre dc ∧ walDurLe dc d ∧ s.wal !! dir = some d ∧ lay.j = j ∧ WalAbsD C Mr d lay hj0.cur ∧
          TailExact lay ∧ lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧
          lay.segs.drop kk = gs ∧ TailMetaR gl.om gl.bs ∧ TailZ0 lay ∧ lay.old.length = gl.om.size ∧
          InArea r dir nm ∧ NameOk nm ∧ hn.cur !! nm = some (.dir j) ∧
          ClaimCoh hn jr (.only [nm])⌝ := by
  iintro #Hinv #Hsi Hnc #Hk Hn Htf Hnf Hh Ho Hau
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_readReg (L := hG.goose_localGS) C Mr R jr r s dir j X hj0 gs gl hnm hdrop hsz hgl
    $$ Hb Hk Hn Htf Hh with ⟨%d, %lay, %kk, %γ, %hrs, Hb, -, Hn, Htf, Hpt, Hv, Hh⟩
  imod walInvBody_past C Mr R jr r s $$ Hb with ⟨Hb, #Hp⟩
  imod walInvBody_nameClaim C Mr R jr r s dir j X $$ Hb Hnf Hk with ⟨Hb, Hnf, %nm, %q, %hn, Hnn, %hnc⟩
  -- the client's update, committed unchanged
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top' $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%dc, ⟨Hdc, %hpre⟩, Hucl⟩
  unfold walDiskAt walDirIs
  icases Hdc with ⟨%M, HM, %HMd⟩
  icases walInvBody_mapLe (L := hG.goose_localGS) C Mr R jr r s M $$ Hb HM with ⟨%HMs, Hb, HM⟩
  obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
  have hle : walDurLe dc d := by
    have h1 := HMs dir
    rw [hM0, hrs.1] at h1
    obtain ⟨ds, hds, hle1⟩ := (walOptLe_some_iff _ _).1 h1
    cases hds
    exact walDurLe_trans hle0 hle1
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ [HM] with HQ
  · iexists M; iframe HM; ipureintro; exact HMd
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  ihave ⟨Ho, #Hlen⟩ := walOpening_lenLb (W := W) w dir sn s d dc.H.length hrs.1
    (by rw [hle.1]; exact Nat.le_refl _) $$ Ho Hp
  imod osNames_next (L := hG.goose_localGS) R jr _ _ hn CoPset.subseteq_top $$ Hsi Hnn
    with ⟨Hnn, #Hlb⟩
  imod osNames_coh (L := hG.goose_localGS) R jr _ _ hn CoPset.subseteq_top $$ Hsi Hnn
    with ⟨Hnn, %hcoh⟩
  imodintro
  iframe Hnc Hn Hnf Hh Ho
  iexists dc, d, lay, kk, γ, s, nm, q, hn
  iframe HQ Hp Hlen Hnn Hlb Htf Hpt Hv
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hrs
  exact ⟨hpre, hle, h1, h2, h3, h4, h5, h6, h7, h8, h9, hnc.1, hnc.2.1, hnc.2.2, hcoh⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
