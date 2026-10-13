/-
Port of `election_proof/spec_raft__reset.v` (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `pvs` is written out
(`GMap w64 Progress`, as `NState.prvals` forces it); `prvals_match`, `reset_matched`,
`log_last` are `prvalsMatch`, `resetMatched`, `logLast` (`Defs.lean`).
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

/-- `reset term` clears the vote iff the term changes, clears `lead` and the vote
tally, and re-initializes the non-election state; `resetTo` (`Defs.lean`) is exactly
that. `r.step` is untouched, so `becomeFollower` -- which assigns it *before* calling
`reset` -- gets it back as it left it. The term does not move back (2026-10-10:
`raft.wp_store_Term`'s premise; every caller resets to the current term or a later
one). -/
abbrev raft.reset.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (term : w64),
  uint.Z s.term ≤ uint.Z term →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysC c r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"reset")) (Val #term))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhysC c r id { resetTo s term with prvals := pvs } ∗
      -- every peer's `Match` is `0`, the node's own `lastIndex()` (`resetMatched`,
      -- `Defs.lean`): the Visit closure writes a fresh `Progress{Match: 0, ...}` and then
      -- `pr.Match = lastIndex()` for `r.id`. `becomeLeader` needs it (`Step.win`'s
      -- `LeaderMatchOk`).
      ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.reset.spec` by `raft.reset.spec_simple`. -/
abbrev raft.reset.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (term : w64),
  uint.Z s.term ≤ uint.Z term →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"reset")) (Val #term))
  {{ (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id { resetTo s term with prvals := pvs } ∗
      ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ }}

open Iris.ProofMode in
theorem raft.reset.spec_simple
    (H : raft.reset.spec (GF := GF) (hG := hG)) :
    raft.reset.specS (GF := GF) (hG := hG) := by
  intro cfg r id s term Hle
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s term Hle $$ [$Hpkg $Hphys]
  inext
  iintro %pvs ⟨Hphys, %Hm⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ
  iframe Hphys
  ipureintro; exact Hm

end spec

end EtcdGrove
end Perennial
