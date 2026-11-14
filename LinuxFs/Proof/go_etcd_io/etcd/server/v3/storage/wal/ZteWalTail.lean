/- Lean-first (no Rocq counterpart).

# `ZeroToEnd` of the WAL's registered tail (I3b, `wal-tc19`)

`ZeroToEnd.wp_specWalTail`: `ZeroToEnd.specWalTail` (`ReadAllTailCallees.lean`) over `ZeroToEnd.specAu`
(`fileutil`'s split form). `ReadAll` registered the tail (`walTailP … true`, the pending token) with the
length word at its write position `o0` zero in the handle's bytes (`readAll_tailZeroWord`).

* *The first step* (`walInv_pendStop`, before any step of the call, `wp_notCrashed_acc`): the handle's
  tail is exact (`TailMetaR`), so its bytes are the invariant's last segment's, whose bytes at and past the
  write position are `old`'s (`TailLast`'s `ByteOk`, `ByteOk.val_unw`): `LenZ` of the layout
  (`lenZ_of_tailLast`); with the registered tail's `TailZ0` (F-Z, or `wr = z0`), F-Z or `TailPend`, which
  turns the pending token into the lent one (`walLentRes_pendStopZ`: `walLentRes_pendStop` with F-Z allowed
  too). The lent `|old|` is the size (`walAbsD_old_exact`).
* *`ZeroToEnd.specAu`* with the tie `growTie` (the lent token, the record's half, idle) and its supplies:
  the truncate to `o0` (`walTail_truncSup`, kind `false`, told `LoWr`), the growth back to the size
  (`walTail_fallocSup`, `walTail_truncSupG`, told `lo ≤ o0` and the size bound).
* *The post*: the bytes from `o0` on zeros (`osZerosA`), the `OsMeta` of the same size, unmapped, the
  page cache known zero to the end of the size's page (`TailMetaZ`), `lo ≤ o0` (`LoWr`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.GrowSup
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllTailCallees
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEndAu

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The length word at the write position of an exact tail is its bytes'** (`TailLast`'s `ByteOk`:
the bytes at and past `wr` are `old`'s, not written, not synced). -/
theorem lenZ_of_tailLast {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g : SegG}
    (hT : TailLast C Mr d lay g) (hz : ∀ j, j < 8 → (g.bs.getD (lay.wr + j) (0, [])).1 = 0) :
    LenZ lay := by
  obtain ⟨hso, -, hlen, -, hB, -⟩ := hT
  intro j hj
  by_cases hb : lay.wr + j < lay.old.length
  · obtain ⟨x, hx⟩ : ∃ x, g.bs[lay.wr + j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h := hB _ x hx
    rw [decide_eq_false (show ¬ (lay.wr + j < lay.wr) by omega),
      decide_eq_false (show ¬ (lay.wr + j < lay.so) by omega)] at h
    have hv := h.val_unw
    have h0 := hz j hj
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some] at h0
    rw [← hv]; exact h0
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **A pending tail made lent** (`walLentRes_pendStop`, its layout F-Z allowed too). -/
theorem walLentRes_pendStopZ (T : GMap GoString GName) (Ls : GMap GoString WalLay) (dir : GoString)
    (γ : GName) (k : Nat) (hp : ∀ lay, Ls !! dir = some lay → TailZeros lay ∨ TailPend lay) :
    ⊢ walPendTok (W := W) dir γ k -∗ walLentRes (W := W) T Ls ==∗
      walLentTok (W := W) dir γ k ∗ walLentRes (W := W) T Ls := by
  unfold walLentRes
  iintro Hl ⟨%M, Ha, %HZ, %HI, Hm⟩
  icases walLentTok_lookup M dir γ k true $$ Ha Hl with %hM
  ihave ⟨⟨%hx, Hk⟩, Hm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (x : GName × Nat × Bool) =>
    iprop(⌜LentOk T Ls dir x⌝ ∗ walTailKey (W := W) dir x.1)) hM).1 $$ Hm
  imod walLentTok_delete M dir γ k true $$ Ha Hl with Ha
  have hM0 : (GMap.delete dir M) !! dir = none := GMap.lookup_delete_eq _ _
  imod walLentTok_insert (GMap.delete dir M) dir γ k false hM0 $$ Ha with ⟨Ha, Hl⟩
  imodintro
  iframe Hl
  iexists _
  iframe Ha
  isplitr
  · ipureintro
    intro d la hT hla hnp
    by_cases e : d = dir
    · subst e
      rcases hp la hla with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by rw [GMap.lookup_insert]; simp, h⟩
    · have e1 : (<[dir := (γ, k, false)]> (GMap.delete dir M)) !! d = M !! d := by
        rw [GMap.lookup_insert_ne _ _ (Ne.symm e), GMap.lookup_delete_ne _ (Ne.symm e)]
      exact zerosOr_congr e1 (HZ d la hT hla (fun x hx => hnp x (by rw [e1]; exact hx)))
  isplitr
  · ipureintro; exact HI
  iapply (BigSepM.bigSepM_insert (Φ := fun (dir : GoString) (x : GName × Nat × Bool) =>
    iprop(⌜LentOk T Ls dir x⌝ ∗ walTailKey (W := W) dir x.1)) hM0).2
  iframe Hm Hk
  ipureintro; exact hx

/-- **The pending tail's first step** (see the file header): the handle's exact tail with the zero length
word at its write position; the pending token becomes the lent one, of `|old|` the size. -/
theorem walInvBody_pendStop (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (m : OsMeta) (bs : List ByteG)
    (hlo : m.lo = m.size) (hhi : m.hi = m.size) (hbs : bs.length = m.size)
    (hz : ∀ j, j < 8 → (bs.getD (wr + j) (0, [])).1 = 0) :
    ⊢ walInvBody (W := W) C Mr R jr r s -∗ walPendTok (W := W) dir γ k -∗
      tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) -∗
      osMeta i (DFrac.own (1 : Qp).half) m -∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ==∗
      ⌜k = m.size⌝ ∗ walInvBody (W := W) C Mr R jr r s ∗ walLentTok (W := W) dir γ k ∗
        tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) ∗ osMeta i (DFrac.own (1 : Qp).half) m ∗
        osBytes i 0 (DFrac.own (1 : Qp).half) bs := by
  letI := walAllG (W := W)
  unfold tailVar
  iintro Hb Hk Hv Hm Hbs
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    HDK, %HAt, Hnms, %Hbd⟩
  unfold walTailsRes
  icases Htl with ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩
  ihave Hk : walTailKeyL (W := W) dir γ (some (k, true)) $$ [Hk]
  · rw [walTailKeyL_some]; iexact Hk
  icases walTailKeyL_lookup T Ls dir γ (some (k, true)) $$ HTa HL Hk with ⟨%HTk, HTa, HL, Hk⟩
  ihave Hk : walPendTok (W := W) dir γ k $$ [Hk]
  · rw [show walPendTok (W := W) dir γ k = walTailKeyL (W := W) dir γ (some (k, true)) from
      (walTailKeyL_some dir γ k true).symm]
    iexact Hk
  obtain ⟨HT, hlent, -⟩ := HTk
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZ0 lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm with ⟨Hent, HTm⟩
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  have Htg' := Htg
  simp only [tailG, Prod.mk.injEq] at Htg'
  obtain ⟨-, -, -, hwr, hino, hF⟩ := Htg'
  obtain ⟨hd, hl, hg, hZ, hB⟩ := hp
  subst hino
  have hg0m : g0 ∈ segsAll Ls := mem_segsAll hl (List.mem_of_getLast? hg)
  iunfold laysResF at Hlays
  ihave ⟨Hs0, Hlays⟩ := BigSepL.bigSepL_mem_acc hg0m $$ Hlays
  have eseg : segResF (GF := GF) F g0 = segRes (GF := GF) g0 := by
    unfold segResF; rw [← hF]
  rw [eseg]
  unfold segRes
  icases Hs0 with ⟨Hm0, Hb0⟩
  icases osMeta_agree2 _ _ _ _ _ $$ Hm Hm0 with %hm
  subst hm
  have HW0 := HW
  obtain ⟨hW1, -⟩ := HW0
  obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := hW1 dir d hd
  rw [hl] at hl1; cases hl1
  have hmet := habs.metas g0 (List.mem_of_getLast? hg)
  icases osBytes_agree g0.ino _ _ 0 bs g0.bs (by rw [hbs, hmet.1]) $$ Hbs Hb0 with %hbb
  subst hbb
  have hex : SegExact g0 := ⟨by rw [hlo, hmet.1], by rw [hhi, hmet.1]⟩
  have hTL := (habs.last g0 hg).1 hex
  have hLZ : LenZ lay := lenZ_of_tailLast hTL (by rw [← hwr]; exact hz)
  have hZP : TailZeros lay ∨ TailPend lay := by
    rcases hZ with h | h
    · exact .inl h
    · exact .inr ⟨h, hLZ⟩
  have hold : lay.old.length = g0.om.size := walAbsD_old_exact habs hg hlo hhi
  obtain ⟨-, la, hla, hlk⟩ := hlent k true rfl
  rw [hl] at hla; cases hla
  simp only at hlk
  imod walLentRes_pendStopZ T Ls dir γ k (fun la' hla' => by rw [hl] at hla'; cases hla'; exact hZP)
    $$ Hk HL with ⟨Hlt, HL⟩
  imodintro
  isplitr
  · ipureintro; omega
  iframe Hlt Hv Hm Hbs
  iexists Ls, cl, n, F
  iframe Hg Hcl Hn HCR Hpk HDK Hnms
  isplitr
  · ipureintro; exact Har
  isplitl [Hlays Hm0 Hb0]
  · iunfold laysResF
    iapply Hlays
    iframe Hm0 Hb0
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitl [HTa HTm Hv' HL]
  · iexists T
    iframe HTa HL
    isplitr
    · ipureintro; exact HTo
    isplitr
    · ipureintro; exact HTi
    iapply HTm
    iexists d, lay, g0
    iframe Hv'
    ipureintro; exact ⟨hd, hl, hg, hZ, hB⟩
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  isplitr
  · ipureintro; exact HAt
  ipureintro; exact Hbd

/-- **The pending tail's first step, at a program step** (`walInvBody_pendStop` under `walInv`). -/
theorem walInv_pendStop (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (γ : GName) (k : Nat) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (wr : Nat) (i : Ino) (m : OsMeta) (bs : List ByteG)
    (hlo : m.lo = m.size) (hhi : m.hi = m.size) (hbs : bs.length = m.size)
    (hz : ∀ j, j < 8 → (bs.getD (wr + j) (0, [])).1 = 0) :
    ⊢ walInv (W := W) C Mr R jr r -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walPendTok (W := W) dir γ k -∗ tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) -∗
      osMeta i (DFrac.own (1 : Qp).half) m -∗ osBytes i 0 (DFrac.own (1 : Qp).half) bs ={⊤}=∗
      ⌜k = m.size⌝ ∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walLentTok (W := W) dir γ k ∗
        tailVar (W := W) γ ((H, md, cuts, wr, i, none) : TailG) ∗ osMeta i (DFrac.own (1 : Qp).half) m ∗
        osBytes i 0 (DFrac.own (1 : Qp).half) bs := by
  iintro #Hinv Hnc Hk Hv Hm Hbs
  imod walInv_open C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_pendStop C Mr R jr r s dir γ k H md cuts wr i m bs hlo hhi hbs hz
    $$ Hb Hk Hv Hm Hbs with ⟨%hk, Hb, Hlt, Hv, Hm, Hbs⟩
  imod Hcl $$ [Hb]
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hlt Hv Hm Hbs
  ipureintro; exact hk

/-- Bytes at an offset, the offset rewritten. -/
theorem osBytes_off_eq {i : Ino} {off1 off2 : Nat} {dq : DFrac} {xs : List ByteG} (h : off1 = off2) :
    osBytes (GF := GF) i off1 dq xs ⊢ osBytes i off2 dq xs := by
  subst h; exact .rfl

theorem osZerosA_eq {i : Ino} {off1 off2 n1 n2 : Nat} {dq : DFrac} (h1 : off1 = off2) (h2 : n1 = n2) :
    osZerosA (GF := GF) i off1 n1 dq ⊢ osZerosA i off2 n2 dq := by
  subst h1 h2; exact .rfl

end iris

end WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]


/-- **`ZeroToEnd` of the WAL's registered tail** (see the file header). -/
theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.wp_specWalTail (Mr : WalMarshal)
    (wp_zte : go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.specAu (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.specWalTail (W := W) Mr := by
  intro R jr r f fd name dir γ i H md cuts o0 sz k ho0 hS
  iintro %Φ ⟨#Harea, #Herr, Hw⟩ HΦ
  unfold walTailP
  rw [show ((o0 : Int) + (([] : List w8).length : Int)) = (o0 : Int) by simp]
  icases Hw with ⟨Hof, ⟨%rd, Hfd⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, ⟨⟨hlen, hmaps, hlo, hhi⟩, hz⟩, hsz62, hfd, hlw⟩ := hp
  simp only [List.length_nil, Nat.add_zero] at hlw
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  unfold WalFs.walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_pendStop walCodec Mr R jr r dir γ k H md cuts o0 i m bs hlo hhi hlen hz
    $$ Hinv Hnc Hk Hv Hm Hb with ⟨%hk, Hnc, Hk, Hv, Hm, Hb⟩
  iframe Hnc
  imodintro
  iapply Fs.wp_osMeta_size _ _ rfl i _ m $$ Hm
  iintro %hmx Hm
  have hmx' : m.size ≤ 0xffffffff000 := hmx
  have hT : (W64 (o0 : Int)).toNat = o0 := by word
  have hI : 0 ≤ (W64 (o0 : Int)).toInt := by word
  icases (osBytes_takeDrop i _ bs o0 (by omega)).1 $$ Hb with ⟨Hbt, Hbd⟩
  ihave #Hts : os.truncSup (growTie (W := W) dir γ k H md cuts o0 i) i (W64 (o0 : Int)).toNat
      (fun m => LoWr m o0) $$ []
  · rw [hT]; unfold growTie
    iapply walTail_truncSup Mr R jr r dir γ (some (k, false)) H md cuts o0 i
      (fun _ h => by simp at h) (fun _ _ => hS) $$ Hinv
  ihave #Hgs : os.truncSup (growTie (W := W) dir γ k H md cuts o0 i) i m.size
      (fun m' => m'.lo ≤ o0 ∧ m'.size ≤ m.size) $$ []
  · iapply walTail_truncSupG Mr R jr r dir γ k H md cuts o0 i m.size (by omega) $$ Hinv
  ihave #Hfs : fallocSup (growTie (W := W) dir γ k H md cuts o0 i) i m.size
      (fun m' => m'.lo ≤ o0 ∧ m'.size ≤ m.size) $$ []
  · iapply walTail_fallocSup Mr R jr r dir γ k H md cuts o0 i m.size (by omega) $$ Hinv
  ihave HK : growTie (W := W) dir γ k H md cuts o0 i $$ [Hk Hv]
  · unfold growTie; rw [walTailKeyL_some]; iframe
  ihave Hbd : osBytes i (W64 (o0 : Int)).toNat (DFrac.own (1 : Qp).half) (bs.drop o0) $$ [Hbd]
  · iapply (osBytes_off_eq hT.symm) $$ Hbd
  wp_apply wp_zte f fd name (DFrac.own 1) (DFrac.own 1) ⟨i, rd, true⟩ m (W64 (o0 : Int)) (bs.drop o0)
      (growTie (W := W) dir γ k H md cuts o0 i) (fun m => LoWr m o0)
      (fun m' => m'.lo ≤ o0 ∧ m'.size ≤ m.size)
      hfd rfl hmaps hI (by rw [hT]; omega) hmx' (by rw [List.length_drop, hT]; omega) hlw
      (fun m' h h' => ⟨.inr (by rw [hT] at h; omega), by rw [hT] at h; omega, h'⟩)
    $$ [Hof Hoff Hfd Hm Hbd HK] as %err ⟨Hof, Hfd, HK, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%he, Hoff, %m', %hm', Hm', Hz⟩ | ⟨%he, -⟩)
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; exact he
    iexists m.size
    isplitr
    · ipureintro; exact ⟨by omega, hmsz⟩
    icases (osZerosA_unfold _ _ _ _).1 $$ Hz with ⟨%zs, %hzs, Hz⟩
    have htl : (bs.take o0).length = o0 := by rw [List.length_take]; omega
    ihave Hz : osBytes i (bs.take o0).length (DFrac.own (1 : Qp).half) (zs.map (fun c => ((0 : w8), c)))
      $$ [Hz]
    · iapply (osBytes_off_eq (by rw [htl, hT])) $$ Hz
    unfold growTie
    icases HK with ⟨Hk, Hv⟩
    iframe Hof Hoff
    isplitl [Hfd]
    · iexists rd; iexact Hfd
    isplitl [Hk]
    · rw [← walTailKeyL_some]; iexact Hk
    iexists m', bs.take o0 ++ zs.map (fun c => ((0 : w8), c))
    iframe Hm'
    isplitl [Hbt Hz]
    · iapply osBytes_app0; iframe
    isplitr
    · ipureintro
      rw [hT] at hzs
      obtain ⟨hs', hmp', hcz', -, hlo'⟩ := hm'
      refine ⟨by rw [hs', hmsz], ⟨⟨?_, hmp'.trans hmaps, ?_⟩, ?_⟩, by omega, hfd, ?_⟩
      · simp only [List.length_append, List.length_map]; rw [hs']; omega
      · rw [hs']; exact Nat.le_trans hcz' (Nat.le_max_right _ _)
      · intro b x hb hx
        rw [List.getElem?_append_right (by omega)] at hx
        simp only [List.getElem?_map] at hx
        obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hx
        rfl
      · exact .inr (by rw [hT] at hlo'; simp only [List.length_nil, Nat.add_zero]; omega)
    unfold tailVar; iexact Hv
  · iapply HΦ
    iright
    ipureintro; exact he

end spec

end EtcdGrove
end Perennial

end
