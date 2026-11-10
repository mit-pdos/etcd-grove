/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 7 (2026-11-10): the untraced instances of the
handlers below `raft.Step`, one spec for both modes since slice 7 (`notes/decisions.md`, "Q8 stage 1
(slice 7)"), as `TracedUntraced.lean`'s: each `X.untraced : X.spec → X.untracedTriple`, the statement
before slice 7 (`s.gh.tr = none`, no gate), from the one spec with the gates the struct's nil logger
(`ownRaftPhysC_traceLogger`, `hookGateOpt_none`) and `G := emp`, for the callers that stay untraced.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries

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

/-- `raft.handleHeartbeat.spec` at an untraced node (the statement before slice 7). -/
abbrev raft.handleHeartbeat.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq dqe : DFrac) (cap : Bool)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (cl : List w8) (rs : List Loc),
  uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) →
  m.From' ≠ id →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleHeartbeat")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (heartbeatResult id s m cl) ∗
      msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}

/-- `raft.handleHeartbeat.spec`'s untraced instance. -/
theorem raft.handleHeartbeat.untraced (h : raft.handleHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.handleHeartbeat.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml dq dqe cap m ents sn cl rs Hcommit Hfrom Htz htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ml dq dqe cap m ents sn cl rs iprop(emp) iprop(emp) Hcommit Hfrom Htz $$ [Hphys Hm]
  · iframe Hpkg Hphys Hm
    isplitr
    · iempintro
    iintro -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro ⟨Hphys, Hm, -⟩
  iapply HΦ
  iframe Hphys Hm

/-- `raft.handleAppendEntries.spec` at an untraced node (the statement before slice 7). -/
abbrev raft.handleAppendEntries.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc),
  PlogWf (entryID.mk m.LogTerm' m.Index') ents →
  uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
  (let ls := s.logst
   let es := ls.sents ++ ls.uents
   uint.Z ls.committed ≤ uint.Z m.Index' →
   PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
   plogFindConflict ls.prev es ents = W64 0 ∨
   uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) →
  m.From' ≠ id →
  m.Type' = MsgApp →
  s.role ≠ .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleAppendEntries")) (Val #ml))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜HandleAppResult id s m ents s'⌝ }}

/-- `raft.handleAppendEntries.spec`'s untraced instance. -/
theorem raft.handleAppendEntries.untraced (h : raft.handleAppendEntries.spec (GF := GF) (hG := hG)) :
    raft.handleAppendEntries.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs Hwf Hnw Hconf Hfid Hty Hnl Htz htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ml m ents sn ctx rs iprop(emp) iprop(emp) Hwf Hnw Hconf Hfid Hty Hnl Htz $$ [Hphys Hm]
  · iframe Hpkg Hphys Hm
    isplitr
    · iempintro
    iintro %s1 %mm %_ -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro %s' ⟨Hphys, %Hres, -⟩
  iapply HΦ $$ %s'
  iframe Hphys
  ipureintro; exact Hres

end untraced

end EtcdGrove
end Perennial
