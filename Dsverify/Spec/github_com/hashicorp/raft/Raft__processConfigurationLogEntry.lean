/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__processConfigurationLogEntry.lean (241f27e).
-/
/-
`raft.(*Raft).processConfigurationLogEntry`'s spec (raft-internal interface, notes/raft-iface.md;
stage 4: configuration entries).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).processConfigurationLogEntry(entry)` (stage 4; stage 3: called only on entries that are no
configuration entries, a no-op), by the main goroutine (`appendEntries`, `installSnapshot`'s scan of the
kept entries, `NewRaft`'s scan of the log), on an entry that is no deprecated peer change: for a
configuration entry (`LogConfiguration`, encoding the valid configuration `ss`) the latest becomes the
committed configuration and the decoded entry the latest, at the entry's index (`setLatestConfiguration`
in mode `b`: the caller's cell, `NewRaft`, or `isRaft`'s invariant cell); any other entry changes
nothing. Returns nil. -/
abbrev github_com.hashicorp.raft.Raft.processConfigurationLogEntry.spec : Prop :=
  ∀ (b : Bool) (r : Loc) (γ : GNames) (p : Loc) (lv : Log) (dq : DFrac) (c0 l : Configuration)
    (i0 li : w64) (p0 : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ p ↦{dq} lv ∗
     ⌜lv.Type' ≠ W8 2 ∧ lv.Type' ≠ W8 3⌝ ∗
     r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l li ∗
     (⌜lv.Type' ≠ W8 5⌝ ∨
      (∃ ss : List Server, lv.Data' ↦*□ encodeServers ss ∗ ⌜srvsOk γ ss⌝) ∗
      (if b then sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"])
          (DFrac.own 1) p0
        else inv latestCfgN (latestCfgCell r γ))) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"processConfigurationLogEntry")) (Val #p))
  {{ RET #interface.nil; p ↦{dq} lv ∗
      ((⌜lv.Type' ≠ W8 5⌝ ∗ r.[Raft, go!"configurations"] ↦ configurations.mk c0 i0 l li) ∨
       (∃ (c : Configuration) (ss : List Server), ⌜lv.Type' = W8 5 ∧ srvsOk γ ss⌝ ∗
         r.[Raft, go!"configurations"] ↦ configurations.mk l li c lv.Index' ∗
         lv.Data' ↦*□ encodeServers ss ∗ c.Servers' ↦* ss ∗
         (if b then ∃ (p1 : Loc) (c' : Configuration),
            sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"])
              (DFrac.own 1) p1 ∗ p1 ↦□ c' ∗ c'.Servers' ↦* ss
          else True))) }}

end spec

end Perennial
