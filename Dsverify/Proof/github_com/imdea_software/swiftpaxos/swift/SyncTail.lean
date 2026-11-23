/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncTail.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Lemmas for `handleSync`'s tail (round 14, sv-swa; internal): a proposal's record (`propIs`,
D16) with another command witness (`swift.propIs_cmd`: `cmdIs` agrees), a fresh one,
and `log.Println` for the arguments `handleSync` prints: strings, an `int32`, quorum values
(`Majority`, `ThreeQuarters`, `Quorum`: no `Error`/`String` method, so the lab's `log` model
calls none) and the recovery's duration as an `int64` (fork c1ecf8e: no `Duration` method).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ProposeHalves
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSetQ
public import Perennial.Proof.fmt
public import Perennial.Proof.log

-- PORT: lab imports dropped: Harness.Proof.log

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- (AcksCommon.lean's `swift.rid_leader`, restated here to keep `handleSync`'s imports light.) -/
theorem swift.rid_leaderS (bw : w32) (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (hb : sp.bal bw = b)
    (hpos : 0 ≤ sint.Z bw) :
    sp.rid (BitVec.srem bw (W32 (sint.Z (W64 (N : Int))))) = sp.leaderOf N b := by
  have hv := replica.quorum.leader_val bw N (by omega) hpos
  have hN' : sint.Z (W64 (N : Int)) = N := by word
  rw [← hb]
  unfold sp.rid sp.bal sp.leaderOf
  rw [hN']
  have hv' : (BitVec.srem bw (W32 (N : Int))).toInt = bw.toInt % (N : Int) := hv
  rw [hv', Int.toNat_emod hpos (by omega)]
  simp

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- A proposal's `cmdIs`. -/
theorem swift.propIs_cmdIs (γ : sp.Names) (gp : Loc) (x : sp.CmdId) (c : sp.Cmd) :
    swift.propIs γ gp x c ⊢ sp.cmdIs γ x c := by
  unfold swift.propIs
  iintro ⟨%p, %w, %mu, %addr, %ts, %vs, -, -, -, #Hc, -⟩
  iexact Hc

/-- The proposal's command is any `c'` with `cmdIs γ x c'` (`sp.cmdIs_agree`). -/
theorem swift.propIs_cmd (γ : sp.Names) (gp : Loc) (x : sp.CmdId) (c c' : sp.Cmd) :
    swift.propIs γ gp x c ∗ sp.cmdIs γ x c' ⊢ swift.propIs γ gp x c' := by
  iintro ⟨#H, #Hc'⟩
  ihave #Hc := swift.propIs_cmdIs γ gp x c $$ H
  ihave %Heq := sp.cmdIs_agree x c c' $$ [Hc Hc']
  · iframe Hc Hc'
  subst Heq
  iexact H

/-- **A fresh proposal** (`handleSync`'s `GPropose` for a command of the `MSync` not in
`proposes`): its `Propose` made read-only (D16). -/
theorem swift.propIs_new (γ : sp.Names) (gp p : Loc) (x : sp.CmdId) (c : sp.Cmd) (vs : GoSlice)
    (w mu : Loc) (addr : GoString) (ts : w64) (hwf : c.wf) :
    gp ↦□ replica.defs.GPropose.mk p w mu false addr ∗
      p ↦ replica.defs.Propose.mk x.seq x.cl (state.Command.mk c.op c.key vs) ts ∗
      vs ↦*□ c.val ∗ sp.cmdIs γ x c ⊢ |==> swift.propIs γ gp x c := by
  iintro ⟨#Hg, Hp, #Hv, #Hc⟩
  ihave ⟨Hp, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hp
  ipersist Hp
  imodintro
  unfold swift.propIs
  iexists p, w, mu, addr, ts, vs
  iframe Hg Hv Hc Hp
  ipureintro; exact ⟨hwf, Hnn⟩

/-- (AcksCommon.lean's `swift.lightSlowAckOk_intro`, restated here.) -/
theorem swift.lsaOk_introS (γ : sp.Names) (γc γm : GName) (N : Nat) (fr : Bool)
    (l : List GoString) (me bw : w32) (x : sp.CmdId) (hw : sp.wireOk me bw)
    (hnl : sp.rid me ≠ sp.leaderOf N (sp.bal bw)) :
    sp.cfg γc γm N fr l ∗ sp.accepted γ (sp.rid me) (sp.bal bw) x ⊢
      sp.msgOk γ γc γm (.lightSlowAck ⟨me, bw, x⟩) := by
  iintro ⟨#Hcfg, #Hacc⟩
  simp only [sp.msgOk]
  iframe Hacc
  isplitr
  · ipureintro; exact hw
  iexists N, fr, l
  iframe Hcfg
  ipureintro; exact hnl

end lemmas

section log
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [log.Assumptions] [π : NetProtoGS]

/-- An argument `log.Println` formats without calling a method of it (the condition under which
Perennial's trusted model of `log.Println`, which does nothing, is faithful,
`Net/Spec/log/Println.lean`): `nil`, `fmt.ArgWf` (a basic value), or a value whose type has no
`Error`, `String` or `Format` method (fmt's `%v` calls only those; the quorum values `handleSync`
prints). **Port change**: the lab's `log` model called `touch` on each argument; Perennial's
does nothing (notes/dsv-swiftpaxos.md). -/
def swift.printable (v : GoInterface) : Prop :=
  ∀ ii, v = interface.ok ii → fmt.ArgWf ii ∨
    (methodSet ii.ty !! go!"Error" = none ∧ methodSet ii.ty !! go!"String" = none ∧
      methodSet ii.ty !! go!"Format" = none)

/-- A value whose type has no `Error`, `String` or `Format` method is printable. -/
theorem swift.wp_touch_noFmt (v : GoInterface)
    (hv : ∀ ii, v = interface.ok ii →
      methodSet ii.ty !! go!"Error" = none ∧ methodSet ii.ty !! go!"String" = none ∧
        methodSet ii.ty !! go!"Format" = none) :
    swift.printable v :=
  fun ii h => .inr (hv ii h)

/-- A value `fmt.ArgsWf` accepts is printable. -/
theorem swift.printable_of_argsWf (v : GoInterface) (h : fmt.ArgsWf [v]) : swift.printable v :=
  fun ii hv => .inl (h ii (by simp [hv]))

/-- `log.Println(args...)` of printable arguments (Perennial's trusted model returns). -/
theorem swift.wp_PrintlnT (arg : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (h : ∀ x ∈ xs, swift.printable x) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.log ∗ arg ↦*{dq} xs }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  wp_start as Hs
  wp_end

omit [log.Assumptions] in
theorem swift.noFmt_of_methodSetIs {t : go.GoType} {ms : List (GoString × Option go.signature)}
    [go.MethodSetIs t ms] (hE : go.methodSetLookup ms go!"Error" = none)
    (hS : go.methodSetLookup ms go!"String" = none)
    (hF : go.methodSetLookup ms go!"Format" = none) :
    methodSet t !! go!"Error" = none ∧ methodSet t !! go!"String" = none ∧
      methodSet t !! go!"Format" = none := by
  have h1 := go.MethodSetIs.method_set_is (t := t) (ms := ms) go!"Error"
  have h2 := go.MethodSetIs.method_set_is (t := t) (ms := ms) go!"String"
  have h3 := go.MethodSetIs.method_set_is (t := t) (ms := ms) go!"Format"
  rw [hE] at h1; rw [hS] at h2; rw [hF] at h3
  exact ⟨h1, h2, h3⟩

omit [log.Assumptions] in
theorem swift.quorumTy_noFmt [replica.Assumptions] :
    methodSet replica.Quorum.ty !! go!"Error" = none ∧
      methodSet replica.Quorum.ty !! go!"String" = none ∧
      methodSet replica.Quorum.ty !! go!"Format" = none :=
  swift.noFmt_of_methodSetIs (by simp [go.methodSetLookup]) (by simp [go.methodSetLookup])
    (by simp [go.methodSetLookup])

omit [log.Assumptions] in
/-- A quorum value (`quorumIs`'s: `Majority`, `ThreeQuarters` or `Quorum`) has neither `Error`
nor `String`. -/
theorem swift.quorumIs_noFmt [replica.Assumptions] (q : GoInterface) (sz : Nat) (mem : w32 → Prop) :
    replica.mset.quorumIs q sz mem ⊢ ⌜∀ ii, q = interface.ok ii →
      methodSet ii.ty !! go!"Error" = none ∧ methodSet ii.ty !! go!"String" = none ∧
        methodSet ii.ty !! go!"Format" = none⌝ := by
  unfold replica.mset.quorumIs
  iintro ⟨-, (%Hq | ⟨%ql, %s, %Hq, -⟩)⟩
  · ipureintro
    intro ii hii
    rcases Hq.1 with h | h <;> rw [h] at hii <;> cases hii <;>
      exact swift.noFmt_of_methodSetIs (by decide) (by decide) (by decide)
  · ipureintro
    intro ii hii
    rw [Hq.1] at hii; cases hii
    exact swift.noFmt_of_methodSetIs (by simp [go.methodSetLookup]) (by simp [go.methodSetLookup])
      (by simp [go.methodSetLookup])

end log

end Perennial.github_com.imdea_software.swiftpaxos
