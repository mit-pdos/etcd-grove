/-
Port of election_proof/spec_raft__becomeCandidate.v (feb5c73d4).

Lean notes:
* Rocq's `pvs` is untyped; its type is `GMap w64 Progress`, that of `NState.prvals`.
  `prole.Leader` is `PRole.leader`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `becomeCandidate` is `reset` plus the role transition; the panic branch
(`state = StateLeader`) is discharged from the role hypothesis. (PR raft#86) The new term is
`r.nextTerm()`'s, `nextTermOf r.Term x` for a draw `x`: the next epoch (upper 48 bits) with a
random low half. It must not wrap (`reset`'s term does not move back), so the node is not in
the last epoch: `r.Term + 2^16 < 2^64` (until PR raft#86, `r.Term + 1 < 2^64`; the new term
was `r.Term + 1`). `nextTermOf_bounds` puts the new term in `(r.Term, r.Term + 2^17)`. -/
abbrev raft.becomeCandidate.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .leader →
  uint.Z s.term + 2 ^ 16 < 2 ^ 64 →
  -- (2026-10-13) only a voter campaigns (`ownRaftPhys`'s `Hvoter`)
  id ∈ c.voters →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeCandidate")) (Val #()))
  {{ (x : w64) (pvs : GMap w64 Progress), RET #();
      ownRaftPhysCV c c.voters r id { becomeCandidate id s (nextTermOf s.term x) with prvals := pvs } }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.becomeCandidate.spec` by `raft.becomeCandidate.spec_simple`. -/
abbrev raft.becomeCandidate.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .leader →
  uint.Z s.term + 2 ^ 16 < 2 ^ 64 →
  id ∈ cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeCandidate")) (Val #()))
  {{ (x : w64) (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id { becomeCandidate id s (nextTermOf s.term x) with prvals := pvs } }}

open Iris.ProofMode in
theorem raft.becomeCandidate.spec_simple
    (H : raft.becomeCandidate.spec (GF := GF) (hG := hG)) :
    raft.becomeCandidate.specS (GF := GF) (hG := hG) := by
  intro cfg r id s Hl Ht Hid
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s Hl Ht (by rw [CfgM.voters_simple]; exact Hid) $$ [$Hpkg $Hphys]
  inext
  iintro %x %pvs Hphys
  iapply HΦ $$ %x %pvs [Hphys]
  iapply ownRaftPhysC_toS $$ Hphys

end spec

end EtcdGrove
end Perennial
