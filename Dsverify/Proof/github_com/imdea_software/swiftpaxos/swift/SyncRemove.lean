/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncRemove.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleSync`'s emptying of `delivered` in removal mode (internal, the swift group's; round 11,
sv-swa). The run loop holds its half of the mirror (`swift.rmTok γrm (some (M, v, d))`,
Deliver.lean / SyncEpoch.lean), so the view is `M` throughout, though it lives in `delivInv`:

* `swift.deliv_iter`: `delivered.IterCb(fn)` visits exactly `M`'s entries (`IterCbV` with the
  observations through `swift.deliv_rm_acc`, each one `M`);
* `swift.deliv_remove`: `delivered.Remove(k)` deletes `k` from the view and the mirror;
* `swift.keys_delete_empty`: removing the visited keys empties the view;
* `swift.execL_reset` (Go: under `execL`, `execLog = nil`): with the view empty and the new
  `State` (`stp'`, empty), `execLInv` holds again at the new epoch `b'` (`deliv_rm_exec`);
* `swift.acceptL_reset` (Go: under `acceptL`, `accepted`/`waiting` new maps): with every key
  of `accepted` accepted here in `b'` (the `MSync`'s commands: `takeSync_stepD`), `acceptInv`
  holds at `b'` and removal mode ends (`deliv_rm_end`): the run loop gets the new epoch's
  pins' half and `γxe`'s half;
* `swift.epochStopped_rm`: the stopped epoch (the run loop's `epochStopped n v ½`, after
  `stopDescs`) starts removal mode (`deliv_rm_start`), leaving the epoch's field shares;
  `swift.epochShare_new`: after the resets, the new epoch's share `epochShare n v' ½` (for
  `epochPool_init`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncEpoch
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.EpochPool
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DeliverE

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- Removing the keys of a permutation of `M`'s entries empties `M`. -/
theorem swift.keys_delete_empty (vis : List (GoString × GoInterface))
    (M : GMap GoString GoInterface) (h : vis.Perm M.toList) :
    (vis.map Prod.fst).foldl (fun M k => GMap.delete k M) M = ∅ := by
  apply github_com.orcaman.concurrent_map.foldl_delete_empty
  intro k hk
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hk
  have : (k, w) ∈ vis := h.mem_iff.mpr ((GMap.mem_toList M k w).mpr hw)
  exact List.mem_map.mpr ⟨(k, w), this, rfl⟩

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [github_com.orcaman.concurrent_map.Assumptions] [sync.Assumptions]

/-- `delivered.Remove(k)` in removal mode (see the file header). -/
theorem swift.deliv_remove
    (wp_RemoveV : github_com.orcaman.concurrent_map.ConcurrentMap.RemoveV.spec (GF := netDistGF))
    (γ : sp.Names) (N r : Nat) (γdl γx γxp γxm γa γxe γrm : GName)
    (str : swift.CommandId → GoString) (dm : GoSlice) (key : GoString)
    (M : GMap GoString GoInterface) (v : Nat × Loc) (d : Bool) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.orcaman.concurrent_map ∗
        github_com.orcaman.concurrent_map.isCMapV dm γdl swift.deliveredR ∗
        inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
        swift.rmTok γrm (some (M, v, d)) }}
      (App (Val #(methods github_com.orcaman.concurrent_map.ConcurrentMap.ty go!"Remove" #dm))
        (Val #key))
    {{ RET #(); swift.rmTok γrm (some (GMap.delete key M, v, d)) }} := by
  iintro %Φ ⟨#Hpkg, #Hm, #Hinv, Htok⟩ HΦ
  iapply (wp_RemoveV dm γdl swift.deliveredR key) $$ %Φ [$Hpkg $Hm]
  inext
  imod (swift.deliv_rm_acc (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) swift.delivN_sub γ N r
    γdl γx γxp γxm γa γxe γrm str M v d) $$ [Hinv Htok] with ⟨HV, Hcl⟩
  · iframe Hinv Htok
  imod (fupd_mask_subseteq (E1 := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \
    (↑swift.delivN : CoPset)) (E2 := ∅) (by simp)) with Hback
  imodintro
  iexists M
  iframe HV
  iintro HV
  imod Hback with -
  imod Hcl $$ %(GMap.delete key M) [] HV with Htok
  · ipureintro
    intro k w hk
    by_cases hkk : key = k
    · subst hkk; simp [GMap.lookup_delete] at hk
    · rw [GMap.lookup_delete_ne] at hk
      · rw [hk]; rfl
      · exact hkk
  imodintro
  iintro _
  iapply HΦ
  iexact Htok

/-- `delivered.IterCb(fn)` in removal mode (see the file header): `fn` is called on each entry
of the view `M` once, `J vis` collecting them. -/
theorem swift.deliv_iter
    (wp_IterCbV : github_com.orcaman.concurrent_map.ConcurrentMap.IterCbV.spec (GF := netDistGF))
    (γ : sp.Names) (N r : Nat) (γdl γx γxp γxm γa γxe γrm : GName)
    (str : swift.CommandId → GoString) (dm : GoSlice) (fn : GoFunc)
    (M : GMap GoString GoInterface) (v : Nat × Loc) (d : Bool)
    (J : List (GoString × GoInterface) → IProp netDistGF) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.orcaman.concurrent_map ∗
        github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ∗
        inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
        swift.rmTok γrm (some (M, v, d)) ∗ J [] ∗
        □ (∀ (vis : List (GoString × GoInterface)) (k : GoString) (w : GoInterface)
            (Φ : val → IProp netDistGF), ⌜M !! k = some w⌝ -∗ swift.deliveredR k w -∗ J vis -∗
            ▷ (J (vis ++ [(k, w)]) -∗ Φ #()) -∗
            WP (App (App (Val #fn) (Val #k)) (Val #w)) {{ Φ }}) }}
      (App (Val #(methods github_com.orcaman.concurrent_map.ConcurrentMap.ty go!"IterCb" #dm))
        (Val #fn))
    {{ RET #(); github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ∗
        swift.rmTok γrm (some (M, v, d)) ∗
        ∃ vis : List (GoString × GoInterface), J vis ∗ ⌜vis.Perm M.toList⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hr, #Hinv, Htok, HJ, #Hfn⟩ HΦ
  iapply (wp_IterCbV dm γdl swift.deliveredR fn
      (fun obs vis => iprop(swift.rmTok γrm (some (M, v, d)) ∗ J vis ∗ ⌜∀ M' ∈ obs, M' = M⌝)))
    $$ %Φ [Hr Htok HJ]
  · iframe Hpkg Hr
    isplitl [Htok HJ]
    · iframe Htok HJ; ipureintro; intro _ h; simp at h
    isplitl []
    · imodintro
      iintro %obs %vis ⟨Htok, HJ, %Hobs⟩
      imod (swift.deliv_rm_acc (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) swift.delivN_sub γ N
        r γdl γx γxp γxm γa γxe γrm str M v d) $$ [Hinv Htok] with ⟨HV, Hcl⟩
      · iframe Hinv Htok
      imod (fupd_mask_subseteq (E1 := (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \
        (↑swift.delivN : CoPset)) (E2 := ∅) (by simp)) with Hback
      imodintro
      iexists M
      iframe HV
      iintro HV
      imod Hback with -
      imod Hcl $$ %M [] HV with Htok
      · ipureintro; intro k w hk; rw [hk]; rfl
      imodintro
      iframe Htok HJ
      ipureintro
      intro M'' h
      rcases List.mem_append.mp h with h | h
      · exact Hobs M'' h
      · simp at h; exact h
    · imodintro
      iintro %obs %vis %k %w %Φ' %Hlast HR ⟨Htok, HJ, %Hobs⟩ HΦ'
      iapply Hfn $$ %vis %k %w %Φ' [] HR HJ [Htok HΦ']
      · ipureintro
        obtain ⟨M', hM', hk⟩ := Hlast
        rw [← Hobs M' (List.mem_of_getLast? hM')]; exact hk
      · inext
        iintro HJ
        iapply HΦ'
        iframe Htok HJ
        ipureintro; exact Hobs
  inext
  iintro ⟨Hr, %n, %obs, %vis, -, ⟨Htok, HJ, %Hobs⟩, %Htr⟩
  iapply HΦ
  iframe Hr Htok
  iexists vis
  iframe HJ
  ipureintro
  exact github_com.orcaman.concurrent_map.iterTrace_perm n obs vis M Htr Hobs

/-- **The reset under `execL`** (see the file header). -/
theorem swift.execL_reset (γ : sp.Names) (N r : Nat) (γdl γx γxp γxm γa γxe γrm γxu : GName)
    (str : swift.CommandId → GoString) (rp : Loc) (b : Nat) (stp : Loc) (b' : Nat) (stp' : Loc)
    (hb : b < b') (bX : Nat) (X : List swift.ExE) (stpX : Loc) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
      swift.rmTok γrm (some (∅, (b, stp), false)) ∗
      ghostVar γx (1 : Qp).half (bX, X) ∗ ghostVar γxe (1 : Qp).half (bX, stpX) ∗
      swift.fld rp go!"execLog" ↦ slice.nil ∗ state.ownState stp' (swift.applyX []) ⊢
    |={⊤}=> swift.execLInvE γ γx γxe γxm γxu N r rp ∗ swift.rmTok γrm (some (∅, (b', stp'), true)) ∗
      ⌜bX = b ∧ stpX = stp⌝ := by
  iintro ⟨#Hinv, Htok, Hx, Hxe, Hlog, Hown⟩
  imod (swift.deliv_rm_exec ⊤ (by simp) γ N r γdl γx γxp γxm γa γxe γrm str b bX stp stpX X b'
    stp' hb) $$ [Hinv Htok Hx Hxe] with ⟨Htok, Hx, Hxe, %Heq⟩
  · iframe Hinv Htok Hx Hxe
  imodintro
  iframe Htok
  isplitl
  · iapply swift.execLInvE_empty γ γx γxe γxm γxu N r rp slice.nil b' stp'
    iframe Hlog Hx Hxe Hown
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  ipureintro; exact Heq

/-- **The reset under `acceptL`; removal mode ends** (see the file header). -/
theorem swift.acceptL_reset (γ : sp.Names) (N r : Nat) (γdl γx γxp γxm γa γxe γrm : GName)
    (str : swift.CommandId → GoString) (rp : Loc) (b' : Nat) (stp' : Loc) (bA : Nat)
    (am wm : Loc) (A : GMap swift.CommandId Unit) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
      swift.rmTok γrm (some (∅, (b', stp'), true)) ∗ ghostVar γa (1 : Qp).half bA ∗
      swift.fld rp go!"accepted" ↦ am ∗ am ↦$ A ∗
      swift.fld rp go!"waiting" ↦ wm ∗ wm ↦$ (∅ : GMap swift.CommandId GoSlice) ∗
      swift.fld rp go!"rechecks" ↦ (slice.nil : GoSlice) ∗
      □ (∀ d : swift.CommandId, ⌜(A !! d).isSome⌝ -∗ sp.accepted γ r b' (toCmdId d)) ⊢
    |={⊤}=> swift.acceptInv γ r rp γa ∗ swift.rmTok γrm none ∗
      ghostVar γxp (1 : Qp).half b' ∗ ghostVar γxe (1 : Qp).half (b', stp') := by
  iintro ⟨#Hinv, Htok, Ha, Hacc, HA, Hw, HW, Hrk, #HAok⟩
  imod (swift.deliv_rm_end ⊤ (by simp) γ N r γdl γx γxp γxm γa γxe γrm str b' stp' bA)
    $$ [Hinv Htok Ha] with ⟨Htok, Ha, Hp, Hxe⟩
  · iframe Hinv Htok Ha
  imodintro
  iframe Htok Hp Hxe
  iunfold swift.acceptInv
  iexists am, wm, A, ∅, b'
  iframe Hacc HA Hw HW Ha HAok
  isplitr
  · iapply BigSepM.bigSepM_empty.2; iempintro
  -- N2-loop: `rechecks` reset to nil with `waiting`
  iunfold swift.recheckOwn
  iexists slice.nil, []
  iframe Hrk
  isplitr
  · iapply (ownSlice_nil (V := swift.CommandId) (DFrac.own 1))
  · iapply ownSliceCap_nil

/-- The stopped epoch starts removal mode (see the file header). -/
theorem swift.epochStopped_rm (γ : sp.Names) (N r : Nat) (γdl γx γxm γa γrm : GName)
    (str : swift.CommandId → GoString) (n : swift.EpN) (v : swift.EpV) :
    inv swift.delivN (swift.delivInv γ N r γdl γx n.γxp γxm γa n.γxe γrm str) ∗
      swift.epochStopped n v (1 : Qp).half ∗ swift.rmTok γrm none ⊢
    |={⊤}=> (∃ M : GMap GoString GoInterface, swift.rmTok γrm (some (M, (v.b, v.stp), false))) ∗
      typedPointsto (swift.fld n.rp go!"ballot") v.bw (DFrac.own (1 : Qp).half) ∗
      typedPointsto (replica.fld n.rr go!"State") v.stp (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.fld n.rp go!"repchan") v.rcp (DFrac.own (1 : Qp).half) ∗
      swift.epochTok n.γe (1 : Qp).half (v.b, v.b) ∗
      typedPointsto (swift.fld n.rp go!"status") v.st (DFrac.own (1 : Qp).half) ∗
      swift.fqShare n v (1 : Qp).half ∗ ⌜sp.bal v.bw = v.b ∧ 0 ≤ sint.Z v.bw⌝ := by
  iintro ⟨#Hinv, Hst, Htok⟩
  iunfold swift.epochStopped at Hst
  iunfold swift.epochShare at Hst
  icases Hst with ⟨Hrd, Hp, Hstatus, Hfq⟩
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HSt, Hrc, Het, Hxe, %Hbw⟩
  imod (swift.deliv_rm_start ⊤ (by simp) γ N r γdl γx n.γxp γxm γa n.γxe γrm str v.b v.stp)
    $$ [Hinv Hp Hxe Htok] with Htok
  · iframe Hinv Hp Hxe Htok
  imodintro
  iframe Htok Hbal HSt Hrc Het Hstatus Hfq
  ipureintro; exact Hbw

/-- The new epoch's share (see the file header). -/
theorem swift.epochShare_new (n : swift.EpN) (v : swift.EpV) :
    typedPointsto (swift.fld n.rp go!"ballot") v.bw (DFrac.own (1 : Qp).half) ∗
      typedPointsto (replica.fld n.rr go!"State") v.stp (DFrac.own (1 : Qp).half) ∗
      typedPointsto (swift.fld n.rp go!"repchan") v.rcp (DFrac.own (1 : Qp).half) ∗
      swift.epochTok n.γe (1 : Qp).half (v.b, v.b) ∗
      ghostVar n.γxe (1 : Qp).half (v.b, v.stp) ∗ ghostVar n.γxp (1 : Qp).half v.b ∗
      typedPointsto (swift.fld n.rp go!"status") v.st (DFrac.own (1 : Qp).half) ∗
      swift.fqShare n v (1 : Qp).half ∗ ⌜sp.bal v.bw = v.b ∧ 0 ≤ sint.Z v.bw⌝ ⊢
    swift.epochShare n v (1 : Qp).half := by
  iintro ⟨Hbal, HSt, Hrc, Het, Hxe, Hp, Hstatus, Hfq, %Hbw⟩
  iunfold swift.epochShare
  iframe Hp Hstatus Hfq
  iunfold swift.epochRd
  iframe Hbal HSt Hrc Het Hxe
  ipureintro; exact Hbw

end proof

end Perennial.github_com.imdea_software.swiftpaxos
