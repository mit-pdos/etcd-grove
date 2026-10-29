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
`Membership.applyChange` gives a result exactly then (`Membership.applyChange_eq_applyGo`, Go's
`confchange` as `applyGo`, cut at `2^62` ids). An entry
that does not decode is rejected (`applyEntry` panics on one; the store's proof refutes it by the
committed entries' decoding, a raft law).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Proof.go_etcd_io.raft.v3.ConfPolicy
public import Proof.go_etcd_io.raft.v3.ConfchangeApi
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2Empty

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
  ∃ m', Membership.applyChange o m = some m'

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
    · obtain ⟨m', h1⟩ := h
      exact ⟨m', by rw [if_pos ⟨m', h1⟩]; exact h1⟩
    · exact ⟨m, by rw [if_neg h]; rfl⟩
  · exact ⟨m, rfl⟩

/-! ## The shape of the committed conf entries

Every conf entry of the committed log decodes to a change whose transition is defined for its
changes (`ConfShaped`): the store's invariant records it of the committed requested entries (what
`Reconfigure` proposes, `randomChange`: a defined transition, `MarshalsConfChange`), and raft's own
conf entries outside them are its automatic leaves, empty `ConfChangeV2`s (`opsOf` drops them), which
decode to the empty change (`ccDecodeV2_nil`). `validConf` takes the transition's definedness of the
change's `AsV2` (`ccToV2`). -/

/-- `AsV2`'s answer on a change. -/
def ccToV2 : ConfChangeIM → ConfChangeV2M
  | .v1 c => c.asV2
  | .v2 cc => cc

/-- A change's transition is defined for its changes (`EnterJoint` panics otherwise; a
`ConfChange`'s `AsV2` has one change of the automatic transition). -/
def ccTransOk (o : ConfChangeIM) : Prop :=
  enterJointOf (ccToV2 o).transition (ccToV2 o).changes.length ≠ none

/-- A conf entry's shape (see the section header). -/
def ConfShaped (e : LogEntry) : Prop := ∃ o, ccDecode e = some o ∧ ccTransOk o

theorem ccTransOk_v1 (c : ConfChangeM) : ccTransOk (.v1 c) := by
  simp [ccTransOk, ccToV2, ConfChangeM.asV2, enterJointOf]

/-- `validConf` answers `ConfOk` of the change's `AsV2`, which is the change's. -/
theorem confOk_toV2 (o : ConfChangeIM) (m : Membership) : ConfOk (.v2 (ccToV2 o)) m ↔ ConfOk o m := by
  cases o with
  | v1 c => simp only [ConfOk, ccToV2]; rw [Membership.applyChange_asV2]
  | v2 cc => rfl

/-- A proposed conf change's entry (`ProposeConfChange`'s update) is shaped. -/
theorem confShaped_proposed (o : ConfChangeIM) (t : w64) (bs : List w8)
    (hm : MarshalsConfChange (some o) bs) (ht : ccTransOk o) :
    ∀ e ∈ opsOf [⟨t, confChangeEntryType (some o), bs⟩], e.isConfChange → ConfShaped e := by
  intro e he _
  have he' : e = ⟨t, confChangeEntryType (some o), bs⟩ := by
    unfold opsOf at he; simp only [List.filter] at he; split at he <;> simp_all
  subst he'
  refine ⟨o, ?_, ht⟩
  cases o with
  | v1 c =>
    simp only [MarshalsConfChange] at hm
    simp [ccDecode, confChangeEntryType, hm]
  | v2 cc =>
    simp only [MarshalsConfChange] at hm
    simp [ccDecode, confChangeEntryType, hm]

/-- A normal proposal's entry carries no conf entry. -/
theorem confShaped_normal (t : w64) (d : List w8) :
    ∀ e ∈ opsOf [⟨t, W32 0, d⟩], e.isConfChange → ConfShaped e := by
  intro e he hc
  have he' : e = ⟨t, W32 0, d⟩ := by
    unfold opsOf at he; simp only [List.filter] at he; split at he <;> simp_all
  subst he'
  exfalso; rcases hc with h | h <;> simp only at h <;> word

/-- **Every committed conf entry is shaped**, if the committed requested entries' are: the others
are raft's automatic leaves (see the section header). -/
theorem confShaped_of_ops (l ops : List LogEntry) (hp : opsOf l <+: ops)
    (hops : ∀ e ∈ ops, e.isConfChange → ConfShaped e) :
    ∀ e ∈ l, e.isConfChange → ConfShaped e := by
  intro e he hc
  by_cases hf : e.isFiller
  · exfalso
    have := LogEntry.isFiller_normal e hf
    rcases hc with h | h <;> rw [this] at h <;> word
  by_cases hv : e.isEmptyV2
  · obtain ⟨hd, ht⟩ := hv
    refine ⟨.v2 ConfChangeV2M.empty, ?_, ?_⟩
    · simp [ccDecode, ht, hd, ccDecodeV2_nil]
    · simp [ccTransOk, ccToV2, ConfChangeV2M.empty, enterJointOf]
  exact hops e (hp.subset (List.mem_filter.mpr ⟨he, by simp [hf, hv]⟩)) hc

end rule

end kvreconf
end EtcdGrove
end Perennial
