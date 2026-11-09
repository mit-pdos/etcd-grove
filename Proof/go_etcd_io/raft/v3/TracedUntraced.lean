/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 3 (2026-11-09): the untraced instances of the
node-event hooks' direct callers whose specs now take the simulation's capability
(`raft.becomeFollower.spec`, `raft.becomeCandidate.spec`, `raft.maybeCommit.spec`: one spec for both
modes, through the caller's gate `HookGate`, `notes/decisions.md`, "Q8 stage 1 (slice 3)"). An untraced caller (`s.gh.tr = none`) uses the
instance here (`X.untraced`, of the statement `X.untracedTriple`), which is the spec before slice 3:
the hook's gate `HookGate none` given by the struct's nil logger (`ownRaftPhysC_traceLogger`,
`hookGate_none`), with `Q := emp`. Not specs: each is a consequence of its function's one spec, for
the callers that stay untraced (`raft.Step`'s handlers, `stepLeader`, `switchToConfig`, `newRaft`,
`RawNode.Bootstrap`, `campaign`).

(Slice 4, 2026-11-09) The message hooks `traceSendMessage` and `traceReceiveMessage`, one spec for
both modes since slice 4, have their untraced instances here too (the specs before slice 4: the nil
logger, giving `True`), for `raft.Step`'s receipt, which stays untraced.

(Slice 5, 2026-11-09) `raft.send`, one spec for both modes since slice 5 (the hook's gate
`HookGateOpt`, the message lent back out of raft's state through `NGhost.lq`), has its untraced
instance here (the statement before slice 5: `s.gh.tr = none`, no gate), for its callers that stay
untraced.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raft__becomeCandidate
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit
public import Spec.go_etcd_io.raft.v3.traceSendMessage
public import Spec.go_etcd_io.raft.v3.traceReceiveMessage
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raft__sendTimeoutNow
public import Spec.go_etcd_io.raft.v3.raft__sendHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeatWithCtx
public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section untraced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `raft.becomeFollower.spec` at an untraced node (the statement before slice 3). -/
abbrev raft.becomeFollower.untracedTriple : Prop :=
  ∀ (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) (term lead : w64),
  uint.Z s.term ≤ uint.Z term →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeFollower"))
      (Val #term)) (Val #lead))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c V r id { becomeFollower s term lead with prvals := pvs } }}

/-- `raft.becomeFollower.spec`'s untraced instance. -/
theorem raft.becomeFollower.untraced (h : raft.becomeFollower.spec (GF := GF) (hG := hG)) :
    raft.becomeFollower.untracedTriple (GF := GF) (hG := hG) := by
  intro c V r id s term lead hle htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Hok, Hphys⟩
  iapply h c r id s term lead iprop(emp) hle (fun h' => absurd htr h') $$ [Hphys]
  · iframe Hpkg Hphys
    rw [htr]
    iapply hookGate_none r _ tl iprop(emp) Hok
    iframe Htl
  inext
  iintro %pvs ⟨Hphys, -⟩
  iapply HΦ $$ %pvs
  iexact Hphys

/-- `raft.becomeCandidate.spec` at an untraced node. -/
abbrev raft.becomeCandidate.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .leader →
  uint.Z s.term + 1 < 2 ^ 64 →
  id ∈ c.voters →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeCandidate")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { becomeCandidate id s with prvals := pvs } }}

/-- `raft.becomeCandidate.spec`'s untraced instance. -/
theorem raft.becomeCandidate.untraced (h : raft.becomeCandidate.spec (GF := GF) (hG := hG)) :
    raft.becomeCandidate.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s hrole hnw hid htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Hok, Hphys⟩
  iapply h c r id s iprop(emp) hrole hnw hid $$ [Hphys]
  · iframe Hpkg Hphys
    rw [htr]
    iapply hookGate_none r _ tl iprop(emp) Hok
    iframe Htl
  inext
  iintro %pvs ⟨Hphys, -⟩
  iapply HΦ $$ %pvs
  iexact Hphys

/-- `raft.maybeCommit.spec` at an untraced node. -/
abbrev raft.maybeCommit.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool) (N : w64), RET #b;
      ownRaftPhysCV c c.voters r id
        (if b then { s with logst := { s.logst with committed := N } } else s) ∗
      ⌜b = true → CommitOkC c (toPState s) N⌝ }}

/-- `raft.maybeCommit.spec`'s untraced instance. -/
theorem raft.maybeCommit.untraced (h : raft.maybeCommit.spec (GF := GF) (hG := hG)) :
    raft.maybeCommit.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s hlead htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Hok, Hphys⟩
  iapply h c r id s (fun _ _ => iprop(emp)) hlead $$ [Hphys]
  · iframe Hpkg Hphys
    iintro %b %N %-
    rw [htr]
    iapply hookGate_none r _ tl iprop(emp) Hok
    iframe Htl
  inext
  iintro %b %N ⟨-, Hphys, %HN, -⟩
  iapply HΦ $$ %b %N
  iframe Hphys
  ipureintro; exact HN

/-- `traceSendMessage.spec` at an untraced node (the statement before slice 4). -/
abbrev traceSendMessage.untracedTriple : Prop :=
  ∀ (r : Loc) (mp : Loc) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜TraceLoggerOk tl⌝ }}
    (App (App (Val #(functions traceSendMessage [])) (Val #r)) (Val #mp))
  {{ RET #(); True }}

/-- `traceSendMessage.spec`'s untraced instance. -/
theorem traceSendMessage.untraced (h : traceSendMessage.spec (GF := GF) (hG := hG)) :
    traceSendMessage.untracedTriple (GF := GF) (hG := hG) := by
  intro r mp tl
  iintro %Φ ⟨#Hpkg, #Htl, %Hok⟩ HΦ
  iapply h r mp tl none none iprop(True) iprop(True) $$ [Hpkg Htl]
  · iframe Hpkg Htl
    isplitr
    · ipureintro; intro _; exact Hok
    isplitr
    · iapply trOwn_none_intro
    simp only [TraceFireOpt]
    itrivial
  inext
  iintro -
  iapply HΦ
  itrivial

/-- `traceReceiveMessage.spec` at an untraced node (the statement before slice 4). -/
abbrev traceReceiveMessage.untracedTriple : Prop :=
  ∀ (r : Loc) (mp : Loc) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜TraceLoggerOk tl⌝ }}
    (App (App (Val #(functions traceReceiveMessage [])) (Val #r)) (Val #mp))
  {{ RET #(); True }}

/-- `traceReceiveMessage.spec`'s untraced instance. -/
theorem traceReceiveMessage.untraced (h : traceReceiveMessage.spec (GF := GF) (hG := hG)) :
    traceReceiveMessage.untracedTriple (GF := GF) (hG := hG) := by
  intro r mp tl
  iintro %Φ ⟨#Hpkg, #Htl, %Hok⟩ HΦ
  iapply h r mp tl none none iprop(True) iprop(True) $$ [Hpkg Htl]
  · iframe Hpkg Htl
    isplitr
    · ipureintro; intro _; exact Hok
    isplitr
    · iapply trOwn_none_intro
    simp only [TraceFireOpt]
    itrivial
  inext
  iintro -
  iapply HΦ
  itrivial

/-- `raft.send.spec` at an untraced node (the statement before slice 5). -/
abbrev raft.send.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (out : List Msg),
  (m.From' = W64 0 ∨ m.From' = id ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader) →
  SendOk id s m ents ctx out →
  SnapOut id s m sn out →
  (m.Type' = MsgApp → AppShape ⟨m, ents, sn, ctx, rs⟩) →
  rs = [] →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgOwn ml (DFrac.own 1) ⟨m, ents, sn, ctx, rs⟩ ∗
      "#Hsrc" ∷ tsSrc s.gh.sn m.Type' sn }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"send")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (sendMsgs s out) }}

/-- `raft.send.spec`'s untraced instance: the gate from the struct's nil logger. -/
theorem raft.send.untraced (h : raft.send.spec (GF := GF) (hG := hG)) :
    raft.send.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs out Hfrom Hok Hsn Hsh Hrs htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm, #Hsrc⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ml m ents sn ctx rs out iprop(emp) Hfrom Hok Hsn Hsh Hrs
    (fun h' => absurd htr h') $$ [Hphys Hm]
  · iframe Hpkg Hphys Hm Hsrc
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro ⟨Hphys, -⟩
  iapply HΦ
  iexact Hphys

/-- `raft.sendTimeoutNow.spec` at an untraced node (the statement before slice 5). -/
abbrev raft.sendTimeoutNow.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64),
  to ≠ id →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendTimeoutNow")) (Val #to))
  {{ RET #(); ownRaftPhysCV c c.voters r id s }}

/-- `raft.sendTimeoutNow.spec`'s untraced instance. -/
theorem raft.sendTimeoutNow.untraced (h : raft.sendTimeoutNow.spec (GF := GF) (hG := hG)) :
    raft.sendTimeoutNow.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s to Hto Htz htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s to iprop(emp) Hto Htz $$ [Hphys]
  · iframe Hpkg Hphys
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro ⟨Hphys, -⟩
  iapply HΦ
  iexact Hphys

/-- `raft.sendHeartbeat.spec` at an untraced node (the statement before slice 5). -/
abbrev raft.sendHeartbeat.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64) (ctx : GoSlice)
    (cl : List w8),
  to ≠ id →
  to ∈ domSet s.progress →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hctx" ∷ ctx ↦*□ cl }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendHeartbeat"))
      (Val #to)) (Val #ctx))
  {{ (cm : w64) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id
        { sendMsgs s [Msg.mkV .heartbeat id to s.term false
                        (W64 0) (W64 0) cm (W64 0) [] [] cl] with prvals := pvs } ∗
      ⌜uint.Z cm ≤ uint.Z s.logst.committed⌝ ∗
      ⌜uint.Z cm ≤ uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0))⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- `raft.sendHeartbeat.spec`'s untraced instance. -/
theorem raft.sendHeartbeat.untraced (h : raft.sendHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.sendHeartbeat.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s to ctx cl Hto Hcfg Htz htr
  iintro %Φ ⟨#Hpkg, Hphys, #Hctx⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s to ctx cl iprop(emp) Hto Hcfg Htz $$ [Hphys]
  · iframe Hpkg Hphys Hctx
    iintro %cm %_
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro %cm %pvs ⟨Hphys, %H1, %H2, %H3, -⟩
  iapply HΦ $$ %cm %pvs
  iframe Hphys
  ipureintro; exact ⟨H1, H2, H3⟩

/-- `raft.bcastHeartbeatWithCtx.spec` at an untraced node (the statement before slice 5). -/
abbrev raft.bcastHeartbeatWithCtx.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ctx : GoSlice) (cl : List w8),
  s.role = .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hctx" ∷ ctx ↦*□ cl }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastHeartbeatWithCtx"))
      (Val #ctx))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜∀ m ∈ ms, HeartbeatOk id (toPState s) m ∧ m.ctx = cl⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- `raft.bcastHeartbeatWithCtx.spec`'s untraced instance: every gate the struct's nil logger. -/
theorem raft.bcastHeartbeatWithCtx.untraced (h : raft.bcastHeartbeatWithCtx.spec (GF := GF) (hG := hG)) :
    raft.bcastHeartbeatWithCtx.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ctx cl Hlead Htz htr
  iintro %Φ ⟨#Hpkg, Hphys, #Hctx⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ctx cl iprop(emp) Hlead Htz $$ [Hphys]
  · iframe Hpkg Hphys Hctx
    isplitr
    · imodintro
      iintro %to %cm %_ %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    iempintro
  inext
  iintro %ms %pvs ⟨Hphys, %H1, %H2, -⟩
  iapply HΦ $$ %ms %pvs
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

/-- `raft.bcastHeartbeat.spec` at an untraced node (the statement before slice 5). -/
abbrev raft.bcastHeartbeat.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastHeartbeat")) (Val #()))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜∀ m ∈ ms, HeartbeatOk id (toPState s) m ∧ m.ctx = hbCtx s.rd.ro⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- `raft.bcastHeartbeat.spec`'s untraced instance: every gate the struct's nil logger. -/
theorem raft.bcastHeartbeat.untraced (h : raft.bcastHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.bcastHeartbeat.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s Hlead Htz htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s iprop(emp) Hlead Htz $$ [Hphys]
  · iframe Hpkg Hphys
    isplitr
    · imodintro
      iintro %to %cm %_ %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    iempintro
  inext
  iintro %ms %pvs ⟨Hphys, %H1, %H2, -⟩
  iapply HΦ $$ %ms %pvs
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

end untraced

end EtcdGrove
end Perennial
