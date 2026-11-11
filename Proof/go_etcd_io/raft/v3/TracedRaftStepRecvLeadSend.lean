/-
Lean-first (no Rocq counterpart). **A leader's sends on a local path's family, at any of its states**
(2026-11-11, trace-check Q8 stage 1 slice 27c, `notes/decisions.md`, "Q8 stage 1 (slice 27c)").

The leader's response paths (`MsgAppResp`, `MsgHeartbeatResp` at its term) send through `leaderGates`'
`"Hgsapp"` (a catch-up or probe append to the responder, at `s`), `"#Hgaapp"` (the appends after
`maybeCommit`, at its outcome's state), `"#Hgrlhb"` (the read-index release's heartbeats) and the untraced
read-index responses (`"#Hghresp"`, `"#Hgrlresp"`). Each is a send line on the family `lineF` at the
state the line is logged at (raft's ghost state there, the idle server's phase of that state):
`lineF_app` (`slice 24a`'s `propGate_app` at a general state, the destination given as a voter),
`lineF_untraced` (no line), and `simIdleS_rd` (the idle server's part reads no read-only state, which
the read-index paths change).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLead
public import Proof.go_etcd_io.raft.v3.TracedRaftStepPropBundle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **The idle server's part reads neither the outbox nor the read-only state.** -/
theorem simIdleS_rd (C : List w64) (s : NState) (o : List Msg) (rd' : RdState) :
    SimIdleS C { s with outbox := o, rd := rd' } = SimIdleS C s := rfl

end pure

section sends
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An append's gate on a leader's local family at `X`**: the share pinned, the
`SendAppendEntriesRequest` line fired (`phaseStepB_msgApp_pin`, `fxPres_app` with `app_lead` and the
request's facts from raft's ghost state at `X`, `msgFacts_app_of_log`), the share unpinned at the outbox
with the request. The destination is a voter (`hto`). -/
theorem lineF_app (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (X : NState)
    (Λ : Option TraceEv → Prop) (mm : Msg) (o : List Msg) (htr : X.gh.tr = some γd) (hlead : X.role = .leader)
    (hT : uint.Z X.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound)
    (hto : mm.dst ∈ elements c.incoming)
    (hok : AppOk id (toPState X) mm) (hcm : mm.commit = X.logst.committed)
    (hmatch : uint.Z ((prvalsMatch X.prvals !! mm.dst).getD (W64 0)) ≤ uint.Z mm.index)
    (hrh : mm.rejecthint = W64 0) :
    lineF (GF := GF) γ md c r id X (fun C => SimIdleS C X) (stepLastEv Λ) o ⊢
      HookGateOpt X.gh.tr r (sendOutGate id X c MsgApp [mm])
        (lineF γ md c r id X (fun C => SimIdleS C X) (stepLastEv Λ) (o ++ [mm])) := by
  unfold lineF trFam
  rw [htr, sendOutGate_one id X c MsgApp mm (W64 9) rfl]
  iintro ⟨Hgh, ⟨%b, Hf⟩, %Hok⟩
  iapply hookGateOpt_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id X hfit $$ Hgh with ⟨%Hb, Hgh⟩
  icases trCapB_pinMem γd γ r id c b _ _ $$ Hf with ⟨%C0, %cs0, %P0, %HΦ0, Hf⟩
  icases trCapB_logger γd γ r id c b _ _ $$ Hf with ⟨%tl, #Htl, Hf⟩
  icases trCapB_pinPerm γd γ r id c b _ _ C0 (fun _ _ _ h => h.1) $$ Hf with ⟨%hperm0, Hf⟩
  obtain ⟨⟨⟨a0, -, -, hs0, -, -, bl0⟩, -⟩, hidC⟩ := HΦ0
  have hb0 : (toPState X).base = base0 := hs0.1
  icases ownStepGhost_appFacts γ md c id X hlead hb0 $$ Hgh with ⟨⟨#Hil, #Hrc, %Htle⟩, Hgh⟩
  have hb : traceNumBound = 2 ^ 61 := rfl
  have hloglen : ((toPState X).log.length : Int) < 2 ^ 63 := by
    have := plastIndex_length _ _ hs0; omega
  obtain ⟨hpk, hents⟩ := appOk_slice id (toPState X) mm hok (by rw [hs0.1]; rfl) hloglen
  have hlt := hok.2.2.2.2.1
  have hlogterm : uint.Z mm.logterm ≤ uint.Z X.term := Htle _ _ hlt
  have hTn : uint.nat X.term < traceNumBound := by word
  have hcn : uint.nat X.logst.committed < traceNumBound := Hb.1
  have hln : uint.nat (plastIndex (toPState X)) < traceNumBound := Hb.2
  have hbI : (traceNumBound : Int) = 2 ^ 61 := by rw [hb]; exact Int.natCast_pow 2 61
  have hlenL : (toPState X).log.length < traceNumBound := by
    have h3 := plastIndex_length _ _ hs0
    have : uint.Z (plastIndex (toPState X)) < traceNumBound := by word
    omega
  have hnums : mm.NumsBelow traceNumBound := by
    refine ⟨?_, by omega, ?_, ?_, ?_, ?_⟩
    · rw [hok.2.2.1]; exact hTn
    · have : uint.Z mm.logterm < traceNumBound := by omega
      word
    · have : uint.nat mm.index ≤ (toPState X).log.length := by omega
      omega
    · rw [hcm]; exact Hb.1
    · rw [hrh]; show 0 < traceNumBound; rw [hb]; omega
  have htrok : mm.TrOk := Msg.trOk_of_nums (by rw [hok.1]; decide) (by rw [hok.1]; decide) (fun _ => hnums)
  obtain ⟨ma0, hma⟩ : ∃ ma0, TraceSim.msgAbs C0 C0.length mm = some ma0 := by
    simp [TraceSim.msgAbs, hok.1]
  have hpt : ma0.type = .appendEntriesRequest := by simp [TraceSim.msgAbs, hok.1] at hma; rw [← hma]
  have hps : ma0.subtype = "app" := by simp [TraceSim.msgAbs, hok.1] at hma; rw [← hma]
  have hsrc : ma0.source = idAbs id := by
    simp [TraceSim.msgAbs, hok.1] at hma; rw [← hma]; simp [hok.2.1]
  have hcm' : mm.commit = (toPState X).commit := hcm
  ihave Hfx := fxPres_app (GF := GF) γ id (SendEvOf (W64 9) id X c mm)
    (PinAt X C0 cs0 P0 o) (PinAt X C0 cs0 (P0 ++ [ma0]) (o ++ [mm]))
    ma0 (msgAbs_canon C0 C0.length mm ma0 hma) hpt hps hsrc
    (fun C cs P h => h.1 ▸ hidC)
    (fun C _ _ h => by rw [msgAbs_dest hma, h.1]; exact (mem_confAbs C0 mm.dst).2 (hperm0.mem_iff.1 hto))
    (app_lead X C0 cs0 P0 o id mm ma0 hma hlead hok hcm')
    (pinAt_step X C0 cs0 P0 o mm ma0) $$ []
  · imodintro
    iintro %C %cs %P %h
    obtain ⟨rfl, -⟩ := h
    iapply msgFacts_app_of_log γ C id (toPState X) mm ma0 hma hok hs0.1
      (by have := hs0.2.1; rw [hs0.1] at this; exact this) hloglen
    rw [show (toPState X).term = X.term from rfl]
    iframe Hil Hrc
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGateOpt_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true (PinAt X C0 cs0 (P0 ++ [ma0]) (o ++ [mm])) (stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun _ _ _ h => h.2.2.2) $$ Hc
    ipureintro
    exact outOk_snoc Hok htrok
  iapply trCapB_hookGateOpt (some γd) γ r id c tl _ b (PinAt X C0 cs0 P0 o) _ (stepLastEv Λ) (stepLastEv Λ)
    iprop(emp) (phaseStepB_msgApp_pin id c X o mm C0 cs0 P0 ma0 hma hlead hto hok hcm' hmatch (by omega))
    (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun e _ => .inr rfl)
    (fun _ e he => sendEvOf_ok (W64 9) id _ c _ e _ he (by decide) hTn hcn hln hnums (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hf Hfx

/-- **An untraced send on a local family** (a read-index response: no line), the family at the outbox
with it. -/
theorem lineF_untraced (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (X : NState)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (mm : Msg) (o : List Msg)
    (htr : X.gh.tr = some γd) (hu : mm.ty.traced = false) :
    lineF (GF := GF) γ md c r id X Φs Λ o ⊢
      HookGateOpt X.gh.tr r none (lineF γ md c r id X Φs Λ (o ++ [mm])) := by
  have hfe : ∀ b, trFam (GF := GF) X.gh.tr γ r id c b Φs Λ (o ++ [mm]) = trFam X.gh.tr γ r id c b Φs Λ o :=
    fun b => trFam_untraced X.gh.tr γ r id c b Φs Λ o [mm] (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact hu)
  unfold lineF
  simp only [hfe]
  rw [htr]
  iintro ⟨Hgh, ⟨%b, Hf⟩, %Hok⟩
  unfold trFam
  iapply hookGateOpt_mono (some γd) r none
    iprop((ownStepGhost γ md c id X ∗ ⌜OutOk X (o ++ [mm])⌝) ∗
      trCapB (some γd) γ r id c b (PhaseAt Φs o) Λ)
  isplitr
  · iintro ⟨⟨Hgh, %Hok'⟩, Hc⟩
    iframe Hgh
    isplitl [Hc]
    · iexists b; iexact Hc
    ipureintro; exact Hok'
  iapply trCapB_gateNone γd γ r id c b _ _ Λ _ (fun _ _ _ h => h)
  iframe Hgh Hf
  ipureintro
  exact outOk_snoc Hok (Msg.trOk_of_untraced hu)

end sends

end EtcdGrove
end Perennial
