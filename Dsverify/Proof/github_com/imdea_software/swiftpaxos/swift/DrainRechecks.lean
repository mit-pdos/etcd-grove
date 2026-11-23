/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DrainRechecks.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
N2-loop: `r.drainRechecks()` (swift.go), the end of each run-loop step: under `acceptL`, take the
first id of `rechecks` (or return when it is empty), and recheck it with the run loop's recheck
call `getCmdDesc(w, "recheck", nil)`; repeat (the rechecks it adds in turn are taken too).

`acceptL`'s list is ids only (`swift.recheckOwn`, Deliver.lean): no fact of an id is needed, since
the recheck call's spec (the run loop's `getDesc` arm, `RunArms.getDesc`) holds of any id. The
generic spec below is over any loop invariant `I` with that arm; `swift.runArm_drain` is the
run loop's `drain` arm over `runInv`, whose context has `acceptL`'s mutex. Partial correctness
only, as every spec here: that the loop ends (each id taken off, none added unboundedly) is not
proved, and safety does not need it.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInvD

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

set_option goose.wp.extras true

/-- **`drainRechecks`** over a loop invariant `I` with the recheck call's spec (see the file
header). -/
theorem swift.Replica.drainRechecks.wp_gen (rp : Loc) (γ : sp.Names) (r : Nat) (γa : GName)
    (I : IProp netDistGF)
    (hrc : ∀ xid : swift.CommandId,
      {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I }}
        (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
          (Val #xid)) (Val #(interface.mkOk go.string #(go!"recheck")))) (Val #slice.nil))
      {{ (d : Loc), RET #d; I }}) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗ I ∗
        sync.isMutex (swift.fld rp go!"acceptL") (swift.acceptInv γ r rp γa) }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"drainRechecks")) (Val #()))
    {{ RET #(); I }} := by
  wp_start as ⟨HI, #HacL⟩
  wp_auto
  ipersist r
  ihave HL : ("HI" ∷ I : IProp netDistGF) $$ [HI]
  · iframe
  wp_for HL
  wp_apply sync.Mutex.wp_Lock $$ [$HacL] as ⟨Hlk, HA⟩
  iunfold swift.acceptInv at HA
  icases HA with ⟨%am, %wm, %A, %W, %bA, Haf, HAm, Hwf, HWm, HWents, Ha, #HAents, Hrk⟩
  iunfold swift.recheckOwn at Hrk
  icases Hrk with ⟨%rk, %ids, Frk, Hrks, Hrkcap⟩
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hrks
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hrks
  wp_if_destruct
  · -- empty: unlock and return
    wp_apply sync.Mutex.wp_Unlock $$ [$HacL $Hlk Haf HAm Hwf HWm HWents Ha Frk Hrks Hrkcap]
    · iunfold swift.acceptInv
      inext
      iexists am, wm, A, W, bA
      iframe
      isplitr
      · first | iexact HAents | (imodintro; iexact HAents)
      iunfold swift.recheckOwn
      iexists rk, ids
      iframe
    try wp_auto
    try wp_for_post
    iapply HΦ
    iexact HI
  · -- the first id: taken off the list, then rechecked
    have hlen0 : sint.Z (W64 0) < sint.Z rk.len := by
      have h0 : sint.Z (W64 0) = 0 := rfl
      have hne : rk.len ≠ W64 0 := by
        first
        | exact Hif
        | (intro h; apply Hif; rw [h])
        | (intro h; apply Hif; simp [h])
      rw [h0]
      have : sint.Z rk.len ≠ 0 := fun h => hne (by word)
      omega
    obtain ⟨w, ws, rfl⟩ : ∃ w ws, ids = w :: ws := by
      cases ids with
      | nil =>
        exfalso
        have h2 := Hlen.1
        simp at h2
        have h0 : sint.Z (W64 0) = 0 := rfl
        rw [h0] at hlen0
        first | word | omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rk.len := ⟨by decide, hlen0⟩
    try rw [ite_eq_left hb0]
    wp_apply (wp_load_slice_index (V := swift.CommandId) rk (sint.Z (W64 0)) _ _ w
      (by decide)) $$ [Hrks] as Hrks
    · iframe; ipureintro; rfl
    try wp_auto
    have hsb : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z rk.len ∧
        sint.Z rk.len ≤ sint.Z rk.cap := by
      refine ⟨by decide, ?_, Hwf.2⟩
      have h0 : sint.Z (W64 0) = 0 := rfl
      have h1 : sint.Z (W64 1) = 1 := rfl
      rw [h1]; rw [h0] at hlen0; omega
    try rw [ite_eq_left hsb]
    icases ownSlice_slice_with_cap (V := swift.CommandId) (W64 1) rk.len rk _
      ⟨hsb.1, hsb.2.1, Int.le_refl _⟩ $$ [Hrks Hrkcap] with ⟨-, Hrks, Hrkcap⟩
    · iframe
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$HacL $Hlk Haf HAm Hwf HWm HWents Ha Frk Hrks Hrkcap]
    · iunfold swift.acceptInv
      inext
      iexists am, wm, A, W, bA
      iframe
      isplitr
      · first | iexact HAents | (imodintro; iexact HAents)
      iunfold swift.recheckOwn
      iexists _, _
      iframe
    try wp_auto
    wp_apply (hrc w) $$ [$HI] as %d HI
    try wp_auto
    wp_for_post
    iframe

/-- `runInv`'s `acceptL` mutex (its descriptor context `descCtxE`). -/
theorem swift.runInv_acceptL (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.runInv rp γ γc γm x ⊢
      ∃ (r : Nat) (γa : GName), sync.isMutex (swift.fld rp go!"acceptL") (swift.acceptInv γ r rp γa) := by
  iintro H
  iunfold swift.runInv at H
  icases H with ⟨#Hd, -⟩
  iunfold swift.descCtxE at Hd
  icases Hd with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, #HacL, -⟩
  iexists x.r, γa
  iexact HacL

/-- **The run loop's `drain` arm** (`RunArms.drain`) over `runInv`, from its recheck arm. -/
theorem swift.runArm_drain (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (hrc : ∀ xid : swift.CommandId,
      {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
          swift.runInv rp γ γc γm x }}
        (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
          (Val #xid)) (Val #(interface.mkOk go.string #(go!"recheck")))) (Val #slice.nil))
      {{ (d : Loc), RET #d; swift.runInv rp γ γc γm x }}) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"drainRechecks")) (Val #()))
    {{ RET #(); swift.runInv rp γ γc γm x }} := by
  iintro %Φ ⟨#Hpkg, Hinv⟩ HΦ
  ihave ⟨⟨%r, %γa, #HacL⟩, Hinv⟩ :=
    BI.persistent_entails_right (swift.runInv_acceptL rp γ γc γm x) $$ Hinv
  iapply (swift.Replica.drainRechecks.wp_gen rp γ r γa _ hrc) $$ [Hinv] HΦ
  iframe Hpkg Hinv HacL

end proof

end Perennial.github_com.imdea_software.swiftpaxos
