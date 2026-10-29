/-
Lean-first (no Rocq counterpart).

# The store's decision on a committed configuration change (2026-10-29, track C)

A replica applies a committed conf entry if `validConf` accepts its change on the replica's
configuration, and rejects it (does not call `ApplyConfChange`) otherwise (`Replica.applyConf`,
`kv.go`). Every replica decides the same entry at the same configuration, so the decision is a
rule of the entry and the configuration before it (`kvrRule`, a raft `ConfRule`), which the
store's invariant records through raft's decision authority (`confPolicy γ kvrConfN kvrRule`,
`Proof/go_etcd_io/raft/v3/ConfPolicy.lean`): every replica's decision on the entry at a position
is the recorded one (`confPolicy_decide`).

`validConf` answers whether `confchange` accepts the change, as `AsV2` makes it, on the
configuration restored from the replica's `ConfState`, with fewer than `2^62` ids after it: raft's
`Membership.applyChange` gives a result exactly then, and the result is `Valid`
(`Membership.applyChange_valid`; the frozen design's `ConfRule.validated`, notes/spec-first-study/
raft-node-unified-candidate.md §1, which the decision switch removed from raft's API). An entry
that does not decode is rejected (`applyEntry` panics on one; the store's proof refutes it by the
committed entries' decoding, a raft law).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Proof.go_etcd_io.raft.v3.ConfPolicy

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section rule
variable [GooseExts]

open Classical in
/-- `validConf`'s answer on the change `o` at the membership `m` (see the file header). -/
def ConfOk (o : ConfChangeIM) (m : Membership) : Prop :=
  ∃ m', Membership.applyChange o m = some m' ∧ m'.Valid

open Classical in
/-- **The store's rule** (see the file header): a committed conf entry's decoded change if
`validConf` accepts it at the membership before it, else a rejection. -/
def kvrRule : ConfRule := fun _ m e =>
  match ccDecode e with
  | some o => if ConfOk o m then some o else none
  | none => none

/-- The rule's decision is allowed: an applied change has a result (what `confPolicy_decide`
takes). -/
theorem kvrRule_step (pre : List LogEntry) (m : Membership) (e : LogEntry) :
    ∃ m', (ConfDecision.ofRule (kvrRule pre m e)).step m = some m' := by
  unfold kvrRule
  split
  · rename_i o _
    by_cases h : ConfOk o m
    · obtain ⟨m', h1, h2⟩ := h
      exact ⟨m', by rw [if_pos ⟨m', h1, h2⟩]; exact h1⟩
    · exact ⟨m, by rw [if_neg h]; rfl⟩
  · exact ⟨m, rfl⟩

end rule

end kvreconf
end EtcdGrove
end Perennial
