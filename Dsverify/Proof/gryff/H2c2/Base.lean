/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c2/Base.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c2: helpers for the commit points (`NeedsWaitForExecute`, `h2Fixed`'s fields)
-/
module

public import Dsverify.Proof.gryff.H2c.Base
public import Dsverify.Proof.gryff.H2b.Phase1
public import Dsverify.Proof.gryff.H2c.SlotOpen
public import Dsverify.Proof.gryff.H2c.LeaderModel
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The copy after the commit block (G11: the bookkeeping dropped). -/
def lcC3 (c : Copy) (lb : LB) : Copy := if lcRe c lb then { lcC1 c lb with lb := none } else lcC1 c lb

/-- The proposals queue after the commit block. -/
def lcPQ (s : RState) (c : Copy) (lb : LB) : List Proposal :=
  if lcRe c lb then s.proposeQ ++ lb.clientProposals else s.proposeQ

/-- A copy replaced by one of the same status keeps its committedness. -/
theorem committedOrExecuted_setInst_status' (s : RState) (q i : w32) (c c' : Copy)
    (hb : model.inBox q i = true) (h : s.inst q i = some c) (hst : c'.status = c.status) :
    committedOrExecuted (s.setInst q i c') (sint.Z q, sint.Z i) =
      committedOrExecuted s (sint.Z q, sint.Z i) := by
  have hb' := of_decide_eq_true hb
  unfold committedOrExecuted model.committedCopy
  simp only [BitVec.ofInt_toInt, model.RState.setInst, and_self, ↓reduceIte, h, hst]
  by_cases hc : c.status = model.St.COMMITTED ∨ c.status = model.St.EXECUTED <;> simp [hc, hb']

section lcC3
variable (c : Copy) (lb : LB)
@[simp] theorem lcC3_cmds : (lcC3 c lb).cmds = c.cmds := by unfold lcC3; split <;> rfl
@[simp] theorem lcC3_ballot : (lcC3 c lb).ballot = c.ballot := by unfold lcC3; split <;> rfl
@[simp] theorem lcC3_status : (lcC3 c lb).status = model.St.COMMITTED := by
  unfold lcC3; split <;> rfl
@[simp] theorem lcC3_seq : (lcC3 c lb).seq = c.seq := by unfold lcC3; split <;> rfl
@[simp] theorem lcC3_deps : (lcC3 c lb).deps = c.deps := by unfold lcC3; split <;> rfl
@[simp] theorem lcC3_base : (lcC3 c lb).base = c.base := by unfold lcC3; split <;> rfl
@[simp] theorem lcC3_slot : (lcC3 c lb).slot = c.slot := by unfold lcC3; split <;> rfl
@[simp] theorem lcC3_leader : (lcC3 c lb).leader = c.leader := by unfold lcC3; split <;> rfl
@[simp] theorem lcC3_vbal : (lcC3 c lb).vbal = c.vbal := by unfold lcC3; split <;> rfl
end lcC3

theorem lcS3_eq (s s2 : RState) (q i : w32) (c : Copy) (lb : LB)
    (hs2 : model.updateCommitted (s.setInst q i (lcC1 c lb)) q = some s2) :
    lcS3 s2 q i c lb = { s2.setInst q i (lcC3 c lb) with proposeQ := lcPQ s c lb } := by
  have hpq : s2.proposeQ = s.proposeQ := (sameOut_updateCommitted hs2).2.2.2.2.2.2.2.2.1
  have hi : s2.inst q i = some (lcC1 c lb) := by
    rw [updateCommitted_inst hs2]; simp [model.RState.setInst]
  unfold lcS3 lcC3 lcPQ
  by_cases hre : lcRe c lb
  · simp only [hre, ↓reduceIte, hpq]; rfl
  · simp only [hre, ↓reduceIte, hpq]
    rw [setInst_self s2 q i _ hi, ← hpq]

theorem lcS3_sameOut (s s2 : RState) (q i : w32) (c : Copy) (lb : LB)
    (hs2 : model.updateCommitted (s.setInst q i (lcC1 c lb)) q = some s2) :
    let s3 := lcS3 s2 q i c lb
    s3.id = s.id ∧ s3.val = s.val ∧ s3.tag = s.tag ∧ s3.ongoing = s.ongoing ∧ s3.maxN = s.maxN ∧
      s3.rops = s.rops ∧ s3.wops = s.wops ∧ s3.ongoingReqs = s.ongoingReqs ∧
      s3.proposeQ = lcPQ s c lb := by
  intro s3
  have h := sameOut_updateCommitted hs2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -, -⟩ := h
  simp only [s3, lcS3_eq s s2 q i c lb hs2, model.RState.setInst]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, trivial⟩

theorem lcC3_committed (s : RState) (q i : w32) (c : Copy) (lb : LB) (hb : model.inBox q i = true) :
    committedOrExecuted (s.setInst q i (lcC3 c lb)) (sint.Z q, sint.Z i) = true := by
  rw [committedOrExecuted_setInst_self s _ _ _ hb]
  unfold lcC3; split <;> simp [lcC1]

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- **A slot's pointer, read access**, with the pointer `nil` at an empty slot. -/
theorem epaxosOwn_peek' (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (q i : w32)
    (hb : model.inBox q i = true) :
    epaxosOwn (GF := GF) ρ h r xs s ⊢ ∃ (ispS sq : GoSlice) (isp : List GoSlice) (ptrs : List Loc) (p : Loc),
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ ispS ∗ ispS ↦*□ isp ∗
      ⌜isp[(sint.Z q).toNat]? = some sq ∧ ptrs[(sint.Z i).toNat]? = some p ∧
        (s.inst q i = none → p = Loc.null)⌝ ∗ sq ↦* ptrs ∗
      (sq ↦* ptrs -∗ epaxosOwn ρ h r xs s) := by
  have hb' := of_decide_eq_true hb
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hb'
  unfold model.SLOTS at hiS
  iintro H
  icases (epaxosOwn_open ..).1 $$ H with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu,
    %pm, #HR, #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  obtain ⟨sq, hsq⟩ : ∃ sq, isp[(sint.Z q).toNat]? = some sq :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hf.1]; omega)⟩
  icases rows_acc' M isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
  icases (replica.rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
  obtain ⟨p, hp⟩ : ∃ p, ptrs[(sint.Z i).toNat]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hrowf.1]; unfold nSlots; omega)⟩
  have hnull : s.inst q i = none → p = Loc.null := by
    intro hn
    have h1 := Hf.2.2.2.2.2.2.1 q i hb
    have h2 := Hrowf.2 _ p hp
    rw [hn] at h1
    have e1 : (((sint.Z q).toNat : Nat) : Int) = sint.Z q := by omega
    have e2 : (((sint.Z i).toNat : Nat) : Int) = sint.Z i := by omega
    rw [e1, e2] at h2
    rw [h2] at h1
    by_cases hpn : p = Loc.null
    · exact hpn
    · simp [hpn] at h1
  iexists ispS, sq, isp, ptrs, p
  iframe HispS Hisp Hrow
  isplitr; · ipureintro; exact ⟨hsq, hp, hnull⟩
  iintro Hrow
  ihave Hrow := (replica.rowOwn_open M _ sq).2 $$ [Hrow]
  · iexists ptrs; iframe; ipureintro; exact Hrowf
  ihave Hrows := Hrows $$ %M %(fun _ _ _ => rfl) Hrow
  iapply (epaxosOwn_open ..).2
  iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
  iframe # ∗
  ipureintro; exact Hf

/-- `epaxosRest`'s counters `conflicted`, `happy`, `slow`, `weird`, taken out. -/
theorem epaxosRest_ctrs (h : Loc) :
    epaxosRest (GF := GF) h ⊢ ∃ (v1 v2 v3 v4 : w64),
      globalAddr src.gryff.conflicted ↦ v1 ∗ globalAddr src.gryff.happy ↦ v2 ∗
      globalAddr src.gryff.slow ↦ v3 ∗ globalAddr src.gryff.weird ↦ v4 ∗
      (∀ (w1 w2 w3 w4 : w64), globalAddr src.gryff.conflicted ↦ w1 -∗
        globalAddr src.gryff.happy ↦ w2 -∗ globalAddr src.gryff.slow ↦ w3 -∗
        globalAddr src.gryff.weird ↦ w4 -∗ epaxosRest h) := by
  unfold epaxosRest
  iintro ⟨%ms, %lcp, %lci, %cS, %cs, %mskR, %msk, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10,
    H11, H12, ⟨%v1, Hc⟩, ⟨%v2, Hh⟩, ⟨%v3, Hs⟩, ⟨%v4, Hw⟩, Hr⟩
  iexists v1, v2, v3, v4
  iframe Hc Hh Hs Hw
  iintro %w1 %w2 %w3 %w4 Hc Hh Hs Hw
  iexists ms, lcp, lci, cS, cs, mskR, msk
  iframe

/-- `Stats` (`h2Fixed`). -/
theorem h2Fixed_stats (k : Fin 3) (gR h : Loc) :
    h2Fixed (GF := GF) k gR h ⊢ ∃ st, gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ statsOk st := by
  unfold h2Fixed
  iintro ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, #H1, #H2, -⟩
  iexists st; iframe #

/-- `Dreply` (`h2Fixed`, H2c-R3). -/
theorem h2Fixed_dreply (k : Fin 3) (gR h : Loc) :
    h2Fixed (GF := GF) k gR h ⊢ gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true := by
  unfold h2Fixed
  iintro ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H⟩
  iexact H

/-- The command of a `cmdsOk` batch at index `j`: a CAS on key 0. -/
theorem cmdsOk_get (gs : List src.state.Command) (j : Nat) (c : src.state.Command)
    (hok : model.cmdsOk (gs.map cmdOf) = true) (hc : gs[j]? = some c) :
    c.K' = W64 0 ∧ c.Op' = W8 6 := by
  simp only [model.cmdsOk, List.all_eq_true, List.mem_map] at hok
  have h1 := hok (cmdOf c) ⟨c, List.mem_of_getElem? hc, rfl⟩
  simp [model.Cmd.ok, cmdOf, model.opCAS] at h1
  exact ⟨h1.2, h1.1⟩

end

end Perennial.gryff.replica2

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]


set_option goose.wp.extras true

/-- `r.NeedsWaitForExecute(&cmd)` on a CAS (`Dreply` set): true. -/
theorem wp_NeedsWait (r gR cp : Loc) (cmd : src.state.Command) (hop : cmd.Op' = W8 6) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true ∗ cp ↦□ cmd }}
      (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"NeedsWaitForExecute"))
        (Val #cp))
    {{ RET #true; True }} := by
  wp_start as ⟨#HgR, #HD, #Hc⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iStructNamed Hc
  simp only [src.state.PUT]
  wp_apply (IntoValTyped.wp_load (t := src.state.Operation.ty) _ _ _) $$ [$Op] as -
  rw [hop]
  rw [show (!decide (W8 6 = W8 1)) = true by decide]
  iapply HΦ
  ipureintro; trivial

end

end Perennial.gryff.replica2

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]


/-- `atomic.AddInt32(addr, v)` on an owned `int32`. -/
theorem wp_AddInt32_own (addr : Loc) (v0 v : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ addr ↦ v0 }}
      (App (App (Val #(functions sync.atomic.AddInt32 [])) (Val #addr)) (Val #v))
    {{ RET #(v0 + v); addr ↦ (v0 + v) }} := by
  iintro %Φ ⟨#Hpkg, Ha⟩ HΦ
  iapply (sync.atomic.wp_AddInt32 addr v) $$ Hpkg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  iexists v0
  iframe Ha
  iintro Ha
  imod Hclose
  imodintro
  iapply HΦ $$ Ha

end

end Perennial.gryff.replica2

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- `a && *l` (Go's short-circuit `&&` with a loaded right operand). -/
theorem wp_if_and (ae e1 : Bool) (l : Loc) :
    {{ (l ↦ e1 : IProp GF) }}
      (If (Val #ae) (App (Val (GoInstruction (GoLoad go.bool))) (Val #l)) (Val #false))
    {{ RET #(ae && e1); l ↦ e1 }} := by
  wp_start as Hl
  cases ae
  · wp_auto; iapply HΦ; iexact Hl
  · wp_auto; iapply HΦ; iexact Hl

end

end Perennial.gryff.replica2
