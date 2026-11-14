/- Lean-first (no Rocq counterpart).

# The append's commit (W6 of `notes/wal-fsext-plan.md`, "W6 implementation log"): `Save`'s and `SaveSnapshot`'s shared step

Both commit the client's update right after `w.mu.Lock()`, before any record is encoded (the error
arms need `Q d`): the WAL's history gains the operation `o`, in the WAL state (`walAppS`, the program's
map `walOwn` with it) and in the open handle's tail record (both halves), the layouts unchanged.

* `walTailsRes_append`: the tail record of `dir` moved to `H ++ [o]` (both halves), the other tails
  kept, the record boundary kept (`tailBound_snoc`).
* `walInvBody_append`: the invariant's contents at `walAppS s dir d o`, with the program's map, given the
  handle's key, its half of the tail record and the lock token's pending-cut flag (`walCutFrag none`:
  the crash condition has no alternative layout, so `crashOk_snoc` gives it); `o`'s records must fit
  a frame (`hfit`: the WAL's records fitting, as the static relation's `fit` says, so do they with
  `o`'s).
* `walTail_append`: the step, at an update of mask `⊤` (`wp_notCrashed_acc` right after `w.mu.Lock()`, whose
  deferred `Unlock`'s resolution, a counted step, raised the WALs' step bound to `⧖ (|H| + 1)`, which the
  commit deposits: `walGhost_updR`;
  `Steps.lean`): `walInv` opened with `notCrashed`, the client's update (at `walAuMask`) committed; the client's
  `Q d` (`d.H` the handle's history), the handle's `walLenLb` at the new length, and the cuts' facts of
  the static relation (`walCutPos`, increasing: `cut.spec`'s premises).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.AppendPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Steps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

theorem walAuMask_sub_top : walAuMask ⊆ (⊤ : CoPset) \ ↑walN := by
  intro p hp
  obtain ⟨-, hn⟩ := LawfulSet.mem_diff.1 hp
  exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, hn⟩

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The tail record of `dir` after its append of `o`** (see the file header). -/
theorem walTailsRes_append (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (F : GMap Ino SegFl) (dir : GoString) (γ : GName) (tg : TailG)
    (o : WalOpG WalEnt) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg ==∗
      ∃ (d : WalDur) (lay : WalLay) (g0 : SegG),
        ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g0 ∧
          tg = tailG d lay g0.ino (F !! g0.ino) ∧ TailZeros lay⌝ ∗
        walTailKey (W := W) dir γ ∗ tailVar (W := W) γ (tg.1 ++ [o], tg.2) ∗
        (⌜∀ b ∈ lay.cuts, b ≤ d.H.length⌝ -∗ walTailsRes (W := W) C Mr (walAppS s dir d o) Ls F) := by
  letI := walAllG (W := W)
  unfold walTailsRes tailVar
  iintro ⟨%T, HTa, %HTo, %HTi, HTm, HL⟩ Hk Hv
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
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  imod ghostVar_update_halves ((tg.1 ++ [o], tg.2) : TailG) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imodintro
  iexists d, lay, g0
  isplitr
  · ipureintro; exact ⟨hd, hl, hg, Htg, hZ⟩
  iframe Hk Hv
  iintro %hc
  iexists T
  iframe HTa HL
  isplitr
  · ipureintro; exact HTo
  isplitr
  · ipureintro
    exact HTi.of_reg dir (fun h => by rw [HT] at h; cases h) (fun k hk => walAppS_lookup_ne s dir d o hk)
      (fun _ _ => rfl)
  iapply (BigSepM.bigSepM_delete (Φ := fun (k : GoString) (v : GName) =>
    iprop(∃ (d1 : WalDur) (lay1 : WalLay) (g : SegG),
      ⌜(walAppS s dir d o).wal !! k = some d1 ∧ Ls !! k = some lay1 ∧ lay1.segs.getLast? = some g ∧
        TailZ0 lay1 ∧ TailBound C Mr d1 lay1⌝ ∗
      ghostVar v (1 : Qp).half (tailG d1 lay1 g.ino (F !! g.ino)))) HT).2
  isplitl [Hv']
  · iexists { d with H := d.H ++ [o] }, lay, g0
    have e : tailG { d with H := d.H ++ [o] } lay g0.ino (F !! g0.ino) = ((tg.1 ++ [o], tg.2) : TailG) := by
      rw [Htg]; rfl
    rw [e]
    iframe Hv'
    ipureintro
    exact ⟨walAppS_lookup s dir d o, hl, hg, Or.inl hZ, tailBound_snoc o hc hB⟩
  iapply BigSepM.bigSepM_mono (fun {k x} hk => ?_) $$ HTm
  have hkd : k ≠ dir := by
    rintro rfl
    rw [show get? (delete T k) k = none from GMap.lookup_delete_eq T k] at hk; cases hk
  iintro ⟨%d1, %lay1, %g1, %hp1, Hv1⟩
  iexists d1, lay1, g1
  iframe Hv1
  ipureintro
  exact ⟨by rw [walAppS_lookup_ne s dir d o hkd]; exact hp1.1, hp1.2⟩

/-- **The invariant's contents after `dir`'s append of `o`** (see the file header). -/
theorem walInvBody_append (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (γ : GName) (tg : TailG) (o : WalOpG WalEnt)
    (M : GMap GoString WalDur)
    (hfit : (∀ b ∈ tg.2.2.1, b ≤ tg.1.length) →
      RecsFit C (recsOfSegs C Mr tg.2.1 (segsOf (tg.1.map WalOpG.toM) tg.2.2.1)) →
      RecsFit C (recsOfSegs C Mr tg.2.1 (segsOf ((tg.1 ++ [o]).map WalOpG.toM) tg.2.2.1)))
    (hox : ¬ walHasMaxIdx [o.toM]) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗ walCutFrag (W := W) none -∗ walOwn (W := W) M -∗ ⧖ (tg.1.length + 1) ==∗
      ∃ d : WalDur, ⌜s.wal !! dir = some d ∧ walMapLe M s.wal ∧ d.H = tg.1 ∧
          (∀ b ∈ tg.2.2.1, walCutPos (tg.1.map WalOpG.toM) b) ∧ tg.2.2.1.Pairwise (· < ·)⌝ ∗
        walInvBody (L := L) (W := W) C Mr R jr r (walAppS s dir d o) ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ (tg.1 ++ [o], tg.2) ∗ walCutFrag (W := W) none ∗
        walOwn (W := W) (walAppS s dir d o).wal ∗ walPast (W := W) (walAppS s dir d o) := by
  letI := walAllG (W := W)
  iintro Hb Hk Hv Hcf HM #Hst
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hn, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walCut_agree cp none $$ Hcp Hcf with %Hcpe
  subst Hcpe
  imod walTailsRes_append C Mr s Ls F dir γ tg o $$ Htl Hk Hv with ⟨%d, %lay, %g0, %hp, Hk, Hv, Htlc⟩
  obtain ⟨hd, hl, hg, htg, hZ⟩ := hp
  obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := HW.1 dir d hd
  rw [hl] at hl1; cases hl1
  have hcuts : ∀ b ∈ lay.cuts, b ≤ d.H.length := fun b hb => by
    have := walCutPos_le (habs.cuts.1 b hb)
    simpa [histM] using this
  have hok : CrashOk C Mr d lay cl n :=
    (crashOkA_none_iff _ _ _ _ _ _).1 (Hdko.2.1 dir d lay hd hl (by simp))
  subst htg
  have hfit' : RecsFit C (recsOfSegs C Mr d.metadata
      (segsOf (histM { d with H := d.H ++ [o] }) lay.cuts)) := hfit hcuts habs.fit
  imod walGhost_updR s (walAppS s dir d o) M (absLe_append o hd) (walKeysInArea_append o hd) _
    (fun n hn => (hn.mono (Nat.le_max_left _ _)).insert rfl
      (by simp only [List.length_append, List.length_singleton]; exact Nat.le_max_right _ _))
    $$ Hst Hg HM
    with ⟨%HMs, Hg, HM, #Hp⟩
  imodintro
  iexists d
  isplitr
  · ipureintro
    exact ⟨hd, HMs, rfl, habs.cuts.1, habs.cuts.2.1⟩
  iframe Hk Hv Hcf HM Hp
  iexists Ls, cl, n, F
  iframe Hg Hcl Hn Hlays HCR Hpk
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact walsOk_append o HW hd hl hZ hfit' hok
  isplitr
  · ipureintro; exact HWC
  isplitl [Htlc]
  · iapply Htlc; ipureintro; exact hcuts
  isplitr
  · ipureintro; exact ⟨absentNone_append o Hab.1, dirsAvoid_append o Hab.2⟩
  isplitr
  · ipureintro; exact HNm
  isplitl [Hdk Hcp]
  · iexists K, none
    iframe Hdk Hcp
    ipureintro; exact dirKeysOk_append o hd Hdko
  iframe Hnms; ipureintro; exact ⟨HAt, walsBounded_app Hbd rfl hd rfl rfl hox⟩

/-- **The append's commit** (see the file header). -/
theorem walTail_append (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (γ : GName) (tg : TailG) (o : WalOpG WalEnt) (sized : Bool)
    (Q : WalDur → IProp GF)
    (hfit : (∀ b ∈ tg.2.2.1, b ≤ tg.1.length) →
      RecsFit C (recsOfSegs C Mr tg.2.1 (segsOf (tg.1.map WalOpG.toM) tg.2.2.1)) →
      RecsFit C (recsOfSegs C Mr tg.2.1 (segsOf ((tg.1 ++ [o]).map WalOpG.toM) tg.2.2.1)))
    (hox : ¬ walHasMaxIdx [o.toM]) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗ walOpenW (W := W) w dir -∗
      (AU <{ ∃∃ d : WalDur, walDiskAt (W := W) dir d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ walDiskAt (W := W) dir { d with H := d.H ++ [o] }, COMM Q d }>) -∗ ⧖ (tg.1.length + 1) -∗
      |={⊤}=> notCrashed (hC := L.goose_crashGS) ∗ walTailKey (W := W) dir γ ∗
        tailVar (W := W) γ (tg.1 ++ [o], tg.2) ∗ walOpenW (W := W) w dir ∗
        walLenLb (W := W) w dir (tg.1.length + 1) ∗ (∃ d : WalDur, Q d ∗ ⌜d.H = tg.1⌝) ∗
        ⌜(∀ b ∈ tg.2.2.1, walCutPos (tg.1.map WalOpG.toM) b) ∧ tg.2.2.1.Pairwise (· < ·)⌝ := by
  iintro #Hinv Hnc Hk Hv Hw Hau #Hst
  imod walInv_open C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases (walOpenW_cut (W := W) w dir).1 $$ Hw with ⟨Hwc, Hpf, Hcf⟩
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%dc, ⟨Hdc, %hsz⟩, Hucl⟩
  unfold walDiskAt walDirIs
  icases Hdc with ⟨%M, HM, %HMd⟩
  imod walInvBody_append C Mr R jr r s dir γ tg o M hfit hox $$ Hb Hk Hv Hcf HM Hst
    with ⟨%d, %hp, Hb, Hk, Hv, Hcf, HM, #Hp⟩
  obtain ⟨hd, HMs, hH, hcp, hpw⟩ := hp
  -- the client's copy is below the real WAL
  obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
  have hle : walDurLe dc d := by
    have h1 := HMs dir
    rw [hM0, hd] at h1
    exact walDurLe_trans hle0 h1
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ [HM] with HQ
  · iexists (walAppS s dir d o).wal
    iframe HM
    ipureintro
    rw [walAppS_lookup]
    exact walDurLe_append o hle
  imod Hcl $$ [Hb]
  · iexists (walAppS s dir d o); iexact Hb
  ihave Hw := (walOpenW_cut (W := W) w dir).2 $$ [Hwc Hpf Hcf]
  · iframe Hwc Hpf Hcf
  icases walOpenW_lenLb (W := W) w dir (walAppS s dir d o) { d with H := d.H ++ [o] }
    (tg.1.length + 1) (walAppS_lookup s dir d o) (by simp [hH]) $$ Hw Hp with ⟨Hw, Hlb⟩
  imodintro
  iframe Hnc Hk Hv Hw Hlb
  isplitl [HQ]
  · iexists dc; iframe HQ; ipureintro; rw [hle.1, hH]
  ipureintro; exact ⟨hcp, hpw⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
