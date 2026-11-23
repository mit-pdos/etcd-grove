/-
`cdr.Write(key, value)`: the coordinator assigns the next version under its lock (`assign`
deposits the put's atomic update), forwards the write to the head, and on success collects the
put's receipt (`collect`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Reps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

/-- An error made by `errors.New(pfx + msg)` with a non-empty prefix. -/
theorem wp_errors_New_ne (pfx msg : GoString) (h : pfx ≠ []) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #(pfx ++ msg)))
    {{ (err : GoInterface), RET #err; errNE err }} := by
  wp_start_folded
  wp_apply errors.wp_New_errorString as %x ⟨-, #He⟩
  iapply HΦ
  unfold errNE net.rpc.errMsg
  iexists pfx ++ msg
  isplitr
  · ipureintro; simp [h]
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact errorString_isError
  iexact He

theorem wp_Write (Hassign : assign.spec (GF := GF)) (Hcollect : collect.spec (GF := GF))
    (cfg : Cfg GF) (c : Loc) (k : GoString) (vsl : GoSlice) (x : GoString)
    (Q : KvM.Output → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        isCoord cfg c ∗ vsl ↦*□ x ∗ opAU cfg.γ (.put k x) Q }}
      (App (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"Write"))
        (Val #k)) (Val #vsl))
    {{ (err : GoInterface), RET #err; (⌜err = interface.nil⌝ ∗ putReceipt k x Q) ∨ errNE err }} := by
  wp_start as ⟨#Hc, #Hval, HAU⟩
  unfold isCoord coordDef
  icases Hc with ⟨#Hctx, -, %Hbound, %f, #Htport, #Hfac, #Hmu⟩
  ihave ⟨#HerrE, #HerrL, #HerrD, #HerrV⟩ := coord_pkg_errs $$ Hpkg
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
  iNamed Hlk
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  simp only [List.length_map] at Hlen
  unfold craqCtx
  icases Hctx with ⟨#Hcraq, %Hctxp, -⟩
  wp_if_destruct
  · -- no replica
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
      Hreps Hjoin Htok]
    · inext; iapply coordLock_pack cfg c sl rs ver hd tl Hwf; iframe; iexact Hnfs
    ihave ⟨%errE, #HerrEa, #HerrEm⟩ := newVar_errMsg _ _ $$ HerrE
    wp_auto
    iapply HΦ
    iright
    iapply errMsg_errNE _ _ (by simp) $$ HerrEm
  have hr0 : 0 < rs.length := by word
  wp_if_destruct
  · -- every version used
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
      Hreps Hjoin Htok]
    · inext; iapply coordLock_pack cfg c sl rs _ hd tl Hwf; iframe; iexact Hnfs
    ihave ⟨%errV, #HerrVa, #HerrVm⟩ := newVar_errMsg _ _ $$ HerrV
    wp_auto
    iapply HΦ
    iright
    iapply errMsg_errNE _ _ (by simp) $$ HerrVm
  -- the next version, assigned to the put
  have hv : uint.Z ver < 2 ^ 64 - 1 := by
    have : ver ≠ W64 (2 ^ 64 - 1) := by intro h; apply Hif; rw [h]; rfl
    word
  iapply fupd_wp
  imod (Hassign cfg.γ ⊤ (fun _ _ => CoPset.mem_full) ver hv k x Q) $$ [Hcraq Hnext HAU]
    with ⟨Hnext, #Hve, Hticket⟩
  · iframe; iexact Hcraq
  imodintro
  list_elem rs 0 as r0
  ihave #Hnf0 := nodeFacts_at cfg rs 0 r0 Hr0_lookup $$ Hnfs
  simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len from ⟨by word, by word⟩,
    _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) _ (DFrac.own 1) r0.loc (by word) $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; exact locs_at rs 0 r0 Hr0_lookup
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
    Hreps Hjoin Htok]
  · inext; iapply coordLock_pack cfg c sl rs _ hd tl Hwf; iframe; iexact Hnfs
  unfold nodeFacts
  icases Hnf0 with ⟨-, %cl, #Hrpc, #Hcl⟩
  unfold isNodeClient
  icases Hcl with ⟨%e, ⟨%He, -⟩, #Hcl⟩
  subst He
  icases Hcl with ⟨-, #HW, -⟩
  wp_auto
  wp_apply +noauto HW $$ %k %vsl %x %(ver + W64 1) %_ Hval Hve as %err Hres
  wp_auto_lc 2
  icases Hres with (⟨%Hnil, #Hcv⟩ | #Hany)
  · subst Hnil
    iapply fupd_wp
    imod (Hcollect cfg.γ ⊤ (fun _ _ => CoPset.mem_full) (ver + W64 1) k x Q) $$ [Hcraq Hticket Hcv Hlc1 Hlc2]
      with HR
    · iframe Hcraq Hcv Hticket
      iapply (lc_split (n := 1) (m := 1)).2
      iframe
    imodintro
    wp_auto
    iapply HΦ
    ileft; iframe HR; ipureintro; rfl
  · ihave %Hne := models_lab.errAny_ne_nil $$ Hany
    obtain ⟨ie, rfl⟩ : ∃ ie, err = GoInterface.ok ie := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok i => exact ⟨i, rfl⟩
    wp_auto
    ihave #Hany' := Hany
    unfold models_lab.errAny
    icases Hany' with ⟨%e', %He', -, #HE⟩
    cases He'
    wp_apply HE
    iintro %msg
    wp_auto
    wp_apply wp_errors_New_ne _ msg (by simp) as %err' Herr'
    iapply HΦ
    iright; iexact Herr'

end proof

end github_com.despreston.go_craq

end Perennial
