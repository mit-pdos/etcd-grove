/- Lean-first (no Rocq counterpart).

# Paths to a WAL directory (G-spine; `notes/wal-fsext-plan.md`, W1 log, thirteenth session)

A path to `dir = r/nm` is a spine through a fraction of a claim on `nm` alone. The invariant keeps,
for every registered WAL name, a fraction of the program's half of its own claim `(jr, .only [nm])`
and a fraction of the area's spine (`walNamesRes`, `Inv.lean`), and lends half of each: a fraction of
`osPathS R dir _ j`, kept by the borrower (never returned: the claim never changes again).

* `walInvBody_dirPath`: with the lock's record of no pending registration (`walNamesFragS ⟨none, none,
  Lo⟩`: every present WAL registered) and the WAL's key, a fraction of the path to its directory, the
  loan recorded in the record (P6b fix A: lent fractions are returned, `walInvBody_dirPathRet`, before
  the lock token is, so that `Discard`, with the free token, gets the name's claim whole).
* `walInv_dirPath`, `walInv_dirPathRet`: the same at a program step (`notCrashed`); `openAtIndex` and
  `Open` take their paths from it (until 2026-11-14 the hypothesis `WalDirPathLaw`, the area's spine
  framed).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import Proof.os.MkdirAllParts

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

/- Copies of `os.osSpine_unsnoc`/`os.osPathS_unchild` (`Proof/os/MkdirAllParts.lean`) without that
section's `go.Semantics`/`os.Assumptions` instances, which the invariant-level lemmas here lack. -/
/-- A spine ends with its last component's claim. -/
theorem nc_osSpine_unsnoc (cs : List GoString) (c : GoString) (j0 : Ino) (dq : DFrac) (J : Ino) :
    osSpine (GF := GF) j0 (cs ++ [c]) dq J ⊢ ∃ (j : Ino) (h : NamesH), osSpine j0 cs dq j ∗
      osNames j (.only [c]) dq h ∗ ⌜h.cur !! c = some (.dir J)⌝ := by
  induction cs generalizing j0 with
  | nil =>
    rw [List.nil_append, osSpine_cons]
    iintro ⟨%h, %J', Hn, %hJ, Hs⟩
    isimp only [osSpine_nil] at Hs
    icases Hs with %he
    subst he
    iexists j0, h
    rw [osSpine_nil]
    iframe
    isplitl [] <;> ipureintro
    · rfl
    · exact hJ
  | cons x cs ih =>
    rw [List.cons_append, osSpine_cons]
    iintro ⟨%h, %J', Hn, %hJ, Hs⟩
    icases ih J' $$ Hs with ⟨%j, %h', Hs, Hn', %hc⟩
    iexists j, h'
    rw [osSpine_cons]
    iframe
    isplitl [] <;> ipureintro
    · exact hJ
    · exact hc

/-- A spine to `d/b` and a spine to `d` give back a whole spine to `d` and the claim on `b`. -/
theorem nc_osPathS_unchild (R : Roots) (d b : GoString) (j J : Ino) (e a : Qp) (hb : NameOk b) :
    osPathS (GF := GF) R (child d b) (DFrac.own e) J ∗ osPathS R d (DFrac.own a) j ⊢
      ∃ h, osPathS R d (DFrac.own (e + a)) j ∗ osNames j (.only [b]) (DFrac.own e) h ∗
        ⌜h.cur !! b = some (.dir J)⌝ := by
  unfold osPathS
  iintro ⟨⟨%r, %j0, %cs, %hp, Hs⟩, ⟨%r', %j0', %cs', %hp', Hs'⟩⟩
  obtain ⟨hR, hm, hcs, he⟩ := hp
  obtain ⟨-, hm', hcs', rfl⟩ := hp'
  rw [← joinPath_snoc] at he
  have hcsb : ∀ x ∈ cs' ++ [b], NameOk x := by
    intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hcs' x hx
    · exact hb
  obtain ⟨hrj, rfl⟩ := root_split_unique hR hm' hm hcsb hcs he
  simp only [Prod.mk.injEq] at hrj
  obtain ⟨rfl, rfl⟩ := hrj
  icases nc_osSpine_unsnoc cs' b j0' (DFrac.own e) J $$ Hs with ⟨%j'', %h, Hs, Hn, %hJ⟩
  icases osSpine_join cs' j0' e a j'' j $$ [Hs Hs'] with ⟨%hj, Hs⟩
  · isplitl [Hs]; iexact Hs; iexact Hs'
  subst hj
  iexists h
  isplitl [Hs]
  · iexists _, _, cs'
    iframe
    ipureintro; exact ⟨hR, hm', hcs', rfl⟩
  iframe
  ipureintro; exact hJ

/-- **A path to a registered WAL's directory**, lent by the invariant (see the file header): with no
pending registration and loans `Lo` out, the loan `(nm, q)` added. -/
theorem walInvBody_dirPath (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString)
    (Lo : List (GoString × Qp)) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s -∗
      walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗ walDirKey (W := W) dir (incOf I dir) j X -∗
      walIncQ (W := W) I ==∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗ walIncQ (W := W) I ∗
        ∃ (nm : GoString) (q : Qp), ⌜dir = child r nm⌝ ∗
          walNamesFragS (W := W) ⟨none, none, (nm, q) :: Lo⟩ ∗
          osPathS (L := hG.goose_localGS) R dir (DFrac.own q) j := by
  iintro Hb Hf #Hk HI
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, HKa, Hca, %HDK⟩, %HAt, Hnms, Hbd⟩
  icases walDirKey_lookupI (W := W) K dir j X I $$ HKa Hk HI with %hK
  obtain ⟨lay, -, hl, rfl, -⟩ := HDK.1 dir j X hK
  unfold walNamesRes
  icases Hnms with ⟨%o, %Wn, Ha, Hs, %hf, %hun, %hst, ⟨%qs, Hsp⟩, Hl⟩
  icases walNamesS_agree (W := W) o _ $$ Ha Hf with %ho
  subst ho
  have hm : lay.nm ∈ Wn := hf.2 dir lay hl (by simp) (by simp)
  have hi := idxOf_getElem? hm
  icases BigSepL.bigSepL_lookup_acc_impl hi $$ Hl with ⟨Hn, Hl⟩
  unfold nameShare
  icases Hn with ⟨%q, %hn, Hn, %hq⟩
  obtain ⟨hqv, hnok, hwnm, hcur⟩ := hq
  -- the directory's path: `dir = r/nm`
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h' : s.wal !! dir with
    | none => rw [HW.2.1 dir h'] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨l2, nm2, -, hl2, hin2, -, hnm2, -⟩ := HW.1 dir d hd
  rw [hl] at hl2; cases hl2
  have hdir : dir = child r lay.nm := by
    rw [hin2.2, Har, ← hnm2]; simp [child, List.append_assoc]; rfl
  -- half of each, and a common fraction of the halves lent
  obtain ⟨e, a, b, hea, heb⟩ := os.qp_common q.half qs.half
  have hsN : ∀ (x y z : Qp), x = y + z →
      osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own x) hn ⊣⊢
        osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own y) hn ∗
        osNames (L := hG.goose_localGS) jr (.only [lay.nm]) (DFrac.own z) hn := fun x y z h => by
    subst h; exact osNames_frac (L := hG.goose_localGS) jr (.only [lay.nm]) y z hn
  have hsP : ∀ (x y z : Qp), x = y + z →
      osPathS (L := hG.goose_localGS) R r (DFrac.own x) jr ⊢
        osPathS (L := hG.goose_localGS) R r (DFrac.own y) jr ∗
        osPathS (L := hG.goose_localGS) R r (DFrac.own z) jr := fun x y z h => by
    subst h; exact (osPathS_frac (L := hG.goose_localGS) R r y z jr).1
  icases (hsN q q.half q.half (Qp.half_add_half q).symm).1 $$ Hn with ⟨Hn, Hn2⟩
  icases (hsN q.half e a hea.symm).1 $$ Hn2 with ⟨Hne, Hna⟩
  ihave Hn := (hsN (q.half + a) q.half a rfl).2 $$ [Hn Hna]
  · iframe
  icases hsP qs qs.half qs.half (Qp.half_add_half qs).symm $$ Hsp with ⟨Hsp, Hsp2⟩
  icases hsP qs.half e b heb.symm $$ Hsp2 with ⟨Hspe, -⟩
  ihave Hpath := osPathS_child (L := hG.goose_localGS) R r lay.nm (DFrac.own e) jr lay.j hn hnok
    (hcur dir lay hl rfl) $$ Hspe Hne
  imod walNamesS_set (W := W) _ _ ⟨none, none, (lay.nm, e) :: Lo⟩ $$ Ha Hf with ⟨Ha, Hf⟩
  have hqv' : (q.half + a).val + shareLs Wn ((lay.nm, e) :: Lo) (Wn.idxOf lay.nm) lay.nm =
      ((1 : Qp).half).val := by
    rw [shareLs_cons_eq]
    have h1 : e.val + a.val = q.half.val := congrArg Subtype.val hea
    have h2 : q.half.val + q.half.val = q.val := congrArg Subtype.val (Qp.half_add_half q)
    have h3 : (q.half + a).val = q.half.val + a.val := rfl
    rw [h3]; rw [← hqv, ← h2, ← h1]; grind
  imodintro
  isplitr [Hpath Hf HI]
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
    isplitr
    · ipureintro; exact hun
    isplitr
    · ipureintro
      refine ⟨hst.1, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hm
      · exact hst.2 x hx
    iapply Hl $$ [] [Hn]
    · imodintro
      iintro %k %y %hk %hne H
      rw [shareLs_cons_ne Wn Lo lay.nm y e k hk hne]
      iexact H
    · iexists q.half + a, hn
      iframe Hn
      ipureintro; exact ⟨hqv', hnok, hwnm, hcur⟩
  · iframe HI
    iexists lay.nm, e
    iframe Hf
    isplitr
    · ipureintro; exact hdir
    rw [hdir]; iexact Hpath

/-- **A loan returned** (see the file header): the path to `r/nm` lent as `(nm, q)` gives its fractions
back to the name's share and the area's spine. -/
theorem walInvBody_dirPathRet (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (nm : GoString) (q : Qp) (j : Ino) (Lo : List (GoString × Qp))
    (hx : (nm, q) ∈ Lo) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s -∗
      walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗
      osPathS (L := hG.goose_localGS) R (child r nm) (DFrac.own q) j ==∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗
        walNamesFragS (W := W) ⟨none, none, Lo.erase (nm, q)⟩ := by
  iintro Hb Hf Hp
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    Hdk, %HAt, Hnms, Hbd⟩
  unfold walNamesRes
  icases Hnms with ⟨%o, %Wn, Ha, Hs, %hf, %hun, %hst, ⟨%qs, Hsp⟩, Hl⟩
  icases walNamesS_agree (W := W) o _ $$ Ha Hf with %ho
  subst ho
  have hm : nm ∈ Wn := hst.2 _ hx
  have hi := idxOf_getElem? hm
  have hperm : Lo.Perm ((nm, q) :: Lo.erase (nm, q)) := List.perm_cons_erase hx
  icases BigSepL.bigSepL_lookup_acc_impl hi $$ Hl with ⟨Hn, Hl⟩
  unfold nameShare
  icases Hn with ⟨%q0, %hn, Hn, %hq⟩
  obtain ⟨hqv, hnok, hwnm, hcur⟩ := hq
  icases nc_osPathS_unchild R r nm jr j q qs hnok $$ [Hp Hsp] with ⟨%hn', Hsp, Hn', %-⟩
  · iframe
  icases osNames_agree (L := hG.goose_localGS) jr (.only [nm]) _ _ hn' hn $$ Hn' Hn with %e1
  subst e1
  ihave Hn := (osNames_frac (L := hG.goose_localGS) jr (.only [nm]) q0 q hn').2 $$ [Hn Hn']
  · iframe
  imod walNamesS_set (W := W) _ _ ⟨none, none, Lo.erase (nm, q)⟩ $$ Ha Hf with ⟨Ha, Hf⟩
  have hqv' : (q0 + q).val + shareLs Wn (Lo.erase (nm, q)) (Wn.idxOf nm) nm = ((1 : Qp).half).val := by
    rw [shareLs_perm Wn hperm, shareLs_cons_eq] at hqv
    have h3 : (q0 + q).val = q0.val + q.val := rfl
    rw [h3, ← hqv]; grind
  imodintro
  iframe Hf
  iexists Ls, cl, n, F
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
  · ipureintro; exact HAt
  isplitr
  · ipureintro; exact hf
  isplitr
  · ipureintro; exact hun
  isplitr
  · ipureintro; exact ⟨hst.1, fun x hx' => hst.2 x (List.mem_of_mem_erase hx')⟩
  iapply Hl $$ [] [Hn]
  · imodintro
    iintro %k %y %hk %hne H
    rw [shareLs_perm Wn hperm, shareLs_cons_ne Wn _ nm y q k hk hne]
    iexact H
  · iexists q0 + q, hn'
    iframe Hn
    ipureintro; exact ⟨hqv', hnok, hwnm, hcur⟩

/-- **A path to a registered WAL's directory, at a program step** (`notCrashed`), with no pending
registration (the lock's `walNamesFrag none`, which `walParked_lock`, the pin's, hands the taker), the
loan recorded. -/
theorem walInv_dirPath (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (Lo : List (GoString × Qp)) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗
      walDirKey (W := W) dir (incOf I dir) j X -∗ walIncQ (W := W) I ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walIncQ (W := W) I ∗
        ∃ (nm : GoString) (q : Qp), ⌜dir = child r nm⌝ ∗
          walNamesFragS (W := W) ⟨none, none, (nm, q) :: Lo⟩ ∗
          osPathS (L := hG.goose_localGS) R dir (DFrac.own q) j := by
  iintro #Hinv Hnc Hf #Hk HI
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_dirPath C Mr R jr r s dir I j X Lo $$ Hb Hf Hk HI with ⟨Hb, HI, Hp⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe

/-- **A loan returned, at a program step** (`notCrashed`). -/
theorem walInv_dirPathRet (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (nm : GoString) (q : Qp) (j : Ino) (Lo : List (GoString × Qp)) (hx : (nm, q) ∈ Lo) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗
      osPathS (L := hG.goose_localGS) R (child r nm) (DFrac.own q) j ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
        walNamesFragS (W := W) ⟨none, none, Lo.erase (nm, q)⟩ := by
  iintro #Hinv Hnc Hf Hp
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_dirPathRet C Mr R jr r s nm q j Lo hx $$ Hb Hf Hp with ⟨Hb, Hf⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe

/-- `walInv_dirPathRet` of the last loan taken, back to no loan out (`walNamesFrag none`). -/
theorem walInv_dirPathRet0 (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (nm : GoString) (q : Qp) (j : Ino) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walNamesFragS (W := W) ⟨none, none, [(nm, q)]⟩ -∗
      osPathS (L := hG.goose_localGS) R (child r nm) (DFrac.own q) j ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walNamesFrag (W := W) none := by
  iintro #Hinv Hnc Hf Hp
  imod walInv_dirPathRet C Mr R jr r nm q j [(nm, q)] (by simp) $$ Hinv Hnc Hf Hp with ⟨Hnc, Hf⟩
  imodintro
  iframe Hnc
  unfold walNamesFrag
  simp only [List.erase_cons_head]
  iexact Hf

end iris

end WalFs
end EtcdGrove
end Perennial

end
