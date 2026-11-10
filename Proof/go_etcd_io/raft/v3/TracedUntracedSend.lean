/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 6 (2026-11-09): the untraced instances of the
rest of the send path, one spec for both modes since slice 6 (`notes/decisions.md`, "Q8 stage 1
(slice 6)"), as `TracedUntraced.lean`'s: each `X.untraced : X.spec → X.untracedTriple`, the statement
before slice 6 (`s.gh.tr = none`, no gate), from the one spec with the gates the struct's nil logger
(`ownRaftPhysC_traceLogger`, `hookGateOpt_none`), `G := emp` and `TrNoSnap none` (`trNoSnap_none`),
for the callers that stay untraced.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Spec.go_etcd_io.raft.v3.raft__maybeSendAppend
public import Spec.go_etcd_io.raft.v3.raft__sendAppend
public import Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import Spec.go_etcd_io.raft.v3.sendMsgReadIndexResponse
public import Spec.go_etcd_io.raft.v3.releasePendingReadIndexMessages
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.raft__becomeLeader

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

/-- `raft.maybeSendAppend.spec` at an untraced node (the statement before slice 6). -/
abbrev raft.maybeSendAppend.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64) (sendIfEmpty : Bool),
  to ≠ id →
  to ∈ domSet s.progress →
  s.role = .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeSendAppend"))
      (Val #to)) (Val #sendIfEmpty))
  {{ (b : Bool) (ms : List Msg) (pvs : GMap w64 Progress), RET #b;
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- `raft.maybeSendAppend.spec`'s untraced instance. -/
theorem raft.maybeSendAppend.untraced (h : raft.maybeSendAppend.spec (GF := GF) (hG := hG)) :
    raft.maybeSendAppend.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s to sie Hto Hcfg Hl Htz htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s to sie (fun _ => iprop(emp)) Hto Hcfg Hl Htz (IdxFree.const _ _) $$ [Hphys]
  · iframe Hpkg Hphys
    isplitr
    · iintro %mm %_ %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iempintro
    rw [htr]
    iapply trNoSnap_none
  inext
  iintro %b %ms %pvs ⟨Hphys, %H1, %H2, -⟩
  iapply HΦ $$ %b %ms %pvs
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

/-- `raft.sendAppend.spec` at an untraced node (the statement before slice 6). -/
abbrev raft.sendAppend.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64),
  to ≠ id →
  to ∈ domSet s.progress →
  s.role = .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendAppend")) (Val #to))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- `raft.sendAppend.spec`'s untraced instance. -/
theorem raft.sendAppend.untraced (h : raft.sendAppend.spec (GF := GF) (hG := hG)) :
    raft.sendAppend.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s to Hto Hcfg Hl Htz htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s to (fun _ => iprop(emp)) Hto Hcfg Hl Htz (IdxFree.const _ _) $$ [Hphys]
  · iframe Hpkg Hphys
    isplitr
    · iintro %mm %_ %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iempintro
    rw [htr]
    iapply trNoSnap_none
  inext
  iintro %ms %pvs ⟨Hphys, %H1, %H2, -⟩
  iapply HΦ $$ %ms %pvs
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

/-- `raft.bcastAppend.spec` at an untraced node (the statement before slice 6). -/
abbrev raft.bcastAppend.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"bcastAppend")) (Val #()))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

/-- `raft.bcastAppend.spec`'s untraced instance: every gate the struct's nil logger. -/
theorem raft.bcastAppend.untraced (h : raft.bcastAppend.spec (GF := GF) (hG := hG)) :
    raft.bcastAppend.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s Hl Htz htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s (fun _ => iprop(emp)) Hl Htz (IdxFree.const _ _) $$ [Hphys]
  · iframe Hpkg Hphys
    isplitr
    · imodintro
      iintro %to %mm %_ %_ %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iempintro
    rw [htr]
    iapply trNoSnap_none
  inext
  iintro %ms %pvs ⟨Hphys, %H1, %H2, -⟩
  iapply HΦ $$ %ms %pvs
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

/-- `sendMsgReadIndexResponse.spec` at an untraced node (the statement before slice 6). -/
abbrev sendMsgReadIndexResponse.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc),
  s.role = .leader →
  s.term ≠ W64 0 →
  ents ≠ [] →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "#Hm" ∷ msgOwn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
    (App (App (Val #(functions sendMsgReadIndexResponse [])) (Val #r)) (Val #ml))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜SendRIResult c id s m ents s'⌝ }}

/-- `sendMsgReadIndexResponse.spec`'s untraced instance: every gate the struct's nil logger. -/
theorem sendMsgReadIndexResponse.untraced (h : sendMsgReadIndexResponse.spec (GF := GF) (hG := hG)) :
    sendMsgReadIndexResponse.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs Hl Htz Hne htr
  iintro %Φ ⟨#Hpkg, Hphys, #Hm⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ml m ents sn ctx rs (fun _ => iprop(emp)) Hl Htz Hne $$ [Hphys]
  · iframe Hpkg Hphys Hm
    isplitr
    · iempintro
    isplitr
    · iintro %_ %_ %_ %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    imodintro
    iintro %_ %to %cm %_ %_ %_ -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro %s' ⟨Hphys, %H1, -⟩
  iapply HΦ $$ %s'
  iframe Hphys
  ipureintro; exact H1

/-- `releasePendingReadIndexMessages.spec` at an untraced node (the statement before slice 6). -/
abbrev releasePendingReadIndexMessages.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  s.term ≠ W64 0 →
  (s.rd.pend ≠ [] →
     plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed
       = some s.term) →
  (∀ p ∈ s.rd.pend, p.2 ≠ []) →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s }}
    (App (Val #(functions releasePendingReadIndexMessages [])) (Val #r))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜ReleaseResult c id s s'⌝ }}

/-- `releasePendingReadIndexMessages.spec`'s untraced instance: every gate the struct's nil logger. -/
theorem releasePendingReadIndexMessages.untraced
    (h : releasePendingReadIndexMessages.spec (GF := GF) (hG := hG)) :
    releasePendingReadIndexMessages.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s Hl Htz Hcit Hpne htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s (fun _ => iprop(emp)) Hl Htz Hcit Hpne $$ [Hphys]
  · iframe Hpkg Hphys
    isplitr
    · iempintro
    isplitr
    · imodintro
      iintro %_ %_ %_ %_ -
      rw [htr]
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    imodintro
    iintro %_ %k %to %cm %_ %_ %_ %_ -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro %s' ⟨Hphys, %H1, -⟩
  iapply HΦ $$ %s'
  iframe Hphys
  ipureintro; exact H1

/-- `raft.appendEntry.spec` at an untraced node (the statement before slice 6). -/
abbrev raft.appendEntry.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (es : GoSlice)
    (ents : List EntryM) (dq : DFrac) (m : Nat),
  (ents.length : Int) < 2^61 →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      "Hes" ∷ entsPts es dq ents ∗
      "#Hrc" ∷ ⧖ m }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appendEntry")) (Val #es))
  {{ (accepted : Bool), RET #accepted;
      ⧖ (m + ents.length) ∗
      ⌜(∀ e ∈ ents, e.Data' = []) → accepted = true⌝ ∗
      entsPts es dq ents ∗
      if accepted then
        ownRaftPhysCV c c.voters r id
          (sendMsgs
            { s with logst :=
                logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }
            [selfAck id
              { s with logst :=
                  logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }])
      else
        ownRaftPhysCV c c.voters r id s }}

/-- `raft.appendEntry.spec`'s untraced instance: both gates the struct's nil logger. -/
theorem raft.appendEntry.untraced (h : raft.appendEntry.spec (GF := GF) (hG := hG)) :
    raft.appendEntry.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s es ents dq m Hsmall Hnz htr
  iintro %Φ ⟨#Hpkg, Hphys, Hes, #Hrc⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s es ents dq m iprop(emp) iprop(emp) iprop(emp) Hsmall Hnz $$ [Hphys Hes]
  · iframe Hpkg Hphys Hes Hrc
    isplitr
    · iempintro
    isplitr
    · iintro -
      rw [htr]
      iapply hookGateN_none r _ _ tl iprop(emp) Htlok
      iframe Htl
    iintro -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro %acc ⟨#Hrc', %Hacc, Hes, Hrest⟩
  iapply HΦ $$ %acc
  iframe Hrc' Hes
  isplitr
  · ipureintro; exact Hacc
  cases acc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hrest with ⟨Hp, -⟩
    iexact Hp
  · simp only [↓reduceIte]
    icases Hrest with ⟨Hp, -⟩
    iexact Hp

/-- `raft.becomeLeader.spec` at an untraced node (the statement before slice 6). -/
abbrev raft.becomeLeader.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .follower →
  s.role ≠ .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeLeader")) (Val #()))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { becomeLeader id s with prvals := pvs } ∗
      ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ }}

/-- `raft.becomeLeader.spec`'s untraced instance: every gate the struct's nil logger. -/
theorem raft.becomeLeader.untraced (h : raft.becomeLeader.spec (GF := GF) (hG := hG)) :
    raft.becomeLeader.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s Hrole Hnl Hnz htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s iprop(emp) iprop(emp) iprop(emp) iprop(emp) Hrole Hnl Hnz $$ [Hphys]
  · iframe Hpkg Hphys
    isplitr
    · iempintro
    isplitr
    · iintro -
      rw [htr]
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro -
      rw [htr]
      iapply hookGateN_none r _ _ tl iprop(emp) Htlok
      iframe Htl
    iintro -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro %pvs ⟨Hphys, %H1, -⟩
  iapply HΦ $$ %pvs
  iframe Hphys
  ipureintro; exact H1

end untraced

end EtcdGrove
end Perennial
