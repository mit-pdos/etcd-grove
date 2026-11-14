/- Lean-first (no Rocq counterpart).

# `ReadAll`'s commit (W3/W5 of `notes/wal-fsext-plan.md`, twenty-fourth session)

`ReadAll` does not change the WAL's history, so its update commits wherever the proof reads the state.
It commits at the look before the loop (`walInv_readCommit`, just before the tail's registration): the
invariant's state `d` of the WAL as `walInvBody_readState` reads it (its layout from the pinned
segments' position `kk` on), the client's state `dc` below it (`walDurLe dc d`: the same history,
cut and metadata; the synced mark and `named` may lag), `Q dc`, a past state holding `d` and the handle's
`walLenLb`. The same look lends a fraction of the WAL's registered name claim (`walInvBody_nameClaim`:
`(jr, .only [nm], hn)`, fixed for the generation, holding the WAL's directory at `nm`), with its
coherence and `osLogLb hn.next`, for the named step after the directory syncs (`ReadAllNamed.lean`).

`readAll_failWpQ`: an error exit after the commit (the ghost handle `failed`, `Q dc` kept), in place
of `readAll_failWp`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.NameClaims
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtPin
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateCoh
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllExit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- A past state of the invariant's contents. -/
theorem walInvBody_past (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ==∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗ walPast (W := W) s := by
  iintro Hb
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  imod walGhost_past (W := W) s $$ Hg with ⟨Hg, #Hp⟩
  imodintro
  iframe Hp
  iexists Ls, cl, n, F
  iframe

/-- **A fraction of a registered WAL's name claim**, lent by the invariant (see the file header; as
`walInvBody_dirPath`, the claim itself in place of a path through it). -/
theorem walInvBody_nameClaim (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s -∗ walNamesFrag (W := W) none -∗
      walDirKey (W := W) dir j X ==∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗ walNamesFrag (W := W) none ∗
        ∃ (nm : GoString) (q : Qp) (hn : NamesH),
          osNames (L := hG.goose_localGS) jr (.only [nm]) (DFrac.own q) hn ∗
          ⌜InArea r dir nm ∧ NameOk nm ∧ hn.cur !! nm = some (.dir j)⌝ := by
  iintro Hb Hf #Hk
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, HKa, Hca, %HDK⟩, %HAt, Hnms, Hbd⟩
  icases walDirKey_lookup (W := W) K dir j X $$ HKa Hk with %hK
  obtain ⟨lay, -, hl, rfl, -⟩ := HDK.1 dir j X hK
  unfold walNamesRes
  icases Hnms with ⟨%o, %Wn, Ha, Hs, %hf, Hsp, Hl⟩
  icases walNames_agree (W := W) o none $$ Ha Hf with %ho
  subst ho
  have hm : lay.nm ∈ Wn := hf.2 dir lay hl (by simp)
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hl with ⟨Hn, Hl⟩
  unfold nameShare
  icases Hn with ⟨%q, %hn, Hn, %hq⟩
  obtain ⟨hnok, hwnm, hcur⟩ := hq
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h' : s.wal !! dir with
    | none => rw [HW.2.1 dir h'] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨l2, nm2, -, hl2, hin2, -, hnm2, -⟩ := HW.1 dir d hd
  rw [hl] at hl2; cases hl2
  have hin : InArea r dir lay.nm := by rw [← Har, hnm2]; exact hin2
  have hsN : ∀ (x y z : Qp), x = y + z →
      osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own x) hn ⊢
        osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own y) hn ∗
        osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own z) hn := fun x y z h => by
    subst h; exact (osNames_frac (L := hG.goose_localGS) jr (.only [lay.nm]) y z hn).1
  icases hsN q q.half q.half (Qp.half_add_half q).symm $$ Hn with ⟨Hn, Hn2⟩
  have hset : Wn.set i lay.nm = Wn := by
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp hi
    rw [← he]; exact List.set_getElem_self hlt
  imodintro
  iframe Hf
  isplitr [Hn2]
  · iexists Ls, cl, n, F
    iframe
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
    isplitr
    · ipureintro; exact HDK
    isplitr
    · ipureintro; exact HAt
    isplitr
    · ipureintro; exact hf
    ispecialize Hl $$ %(lay.nm)
    rw [hset]
    iapply Hl
    iexists q.half, hn
    iframe Hn
    ipureintro; exact ⟨hnok, hwnm, hcur⟩
  · iexists lay.nm, q.half, hn
    iframe Hn2
    ipureintro; exact ⟨hin, hnok, hcur dir lay hl rfl⟩

/-- **`ReadAll`'s update committed at the look before the loop** (see the file header). -/
theorem walInv_readCommit (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (sn : w64 × w64) (j : Ino) (X : List GoString) (hj0 : NamesH)
    (gs : List SegG)
    (hnm : ∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino))
    (hdrop : ∃ kk, (walNames hj0.cur).drop kk = gs.map (·.name))
    (hsz : ∀ g ∈ gs, g.om.size = g.bs.length) (Pre : WalDur → Prop) (Q : WalDur → IProp GF) :
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
      walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none ∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ∗
      walOpening (W := W) w dir sn ∗
      ∃ (dc d : WalDur) (lay : WalLay) (kk : Nat) (s : AbsDiskState) (nm : GoString) (q : Qp)
        (hn : NamesH),
        Q dc ∗ walPast (W := W) s ∗ walLenLb (W := W) w dir dc.H.length ∗
        osNames (L := hG.goose_localGS) jr (.only [nm]) (DFrac.own q) hn ∗
        osLogLb (L := hG.goose_localGS) hn.next ∗
        ⌜Pre dc ∧ walDurLe dc d ∧ s.wal !! dir = some d ∧ lay.j = j ∧ WalAbsD C Mr d lay hj0.cur ∧
          TailExact lay ∧ lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧
          lay.segs.drop kk = gs ∧ InArea r dir nm ∧ NameOk nm ∧ hn.cur !! nm = some (.dir j) ∧
          ClaimCoh hn jr (.only [nm])⌝ := by
  iintro #Hinv #Hsi Hnc #Hk Hn Htf Hnf Hh Ho Hau
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_readState (L := hG.goose_localGS) C Mr R jr r s dir j X hj0 gs hnm hdrop hsz
    $$ Hb Hk Hn Htf Hh with ⟨%d, %lay, %kk, %hrs, Hb, -, Hn, Htf, Hh⟩
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
  iframe Hnc Hn Htf Hnf Hh Ho
  iexists dc, d, lay, kk, s, nm, q, hn
  iframe HQ Hp Hlen Hnn Hlb
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrs
  exact ⟨hpre, hle, h1, h2, h3, h4, h5, h6, hnc.1, hnc.2.1, hnc.2.2, hcoh⟩

end iris

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **An error exit of `ReadAll` after its commit** (see the file header). -/
theorem readAll_failWpQ (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (sn : w64 × w64) (Q : WalDur → IProp GF) (dc : WalDur)
    (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ walOpening (W := W) w dir sn -∗ Q dc -∗
      (∀ d, Q d -∗ walReadFailed (W := W) w dir -∗ WP e {{ Φ }}) -∗ WP e {{ Φ }} := by
  iintro #Hinv Ho HQ Hk
  iapply wp_notCrashed_acc _ _ h
  iintro Hnc
  imod walInv_failOpening (L := hG.goose_localGS) C Mr R jr r w dir sn $$ Hinv Hnc Ho with ⟨Hnc, Hf⟩
  imodintro
  iframe Hnc
  iapply Hk $$ HQ Hf

end wp

end WalFs
end EtcdGrove
end Perennial

end
