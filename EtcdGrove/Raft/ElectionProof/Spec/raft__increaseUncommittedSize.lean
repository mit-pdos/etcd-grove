/-
Port of `election_proof/spec_raft__increaseUncommittedSize.v`.

Lean notes:
* The comment's second paragraph ("Stated against the bare struct points-to rather
  than `ownRaftPhys`") is kept verbatim from Rocq although the Rocq statement itself,
  ported faithfully here, is on `ownRaftPhys`; the Rocq comment is stale.
* The reference `raft__increaseUncommittedSizeⁱᵐᵖˡ` is to the Lean generated code
  `raft.increaseUncommittedSize.impl`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.increaseUncommittedSize(ents)`: charge a batch against the uncommitted-entries
budget, and say whether it fits (`raft.increaseUncommittedSize.impl`,
`Perennial/Code/go_etcd_io/raft/v3.lean`).

The body is

    s := payloadsSize(ents)
    if r.uncommittedSize > 0 && s > 0 && r.uncommittedSize+s > r.maxUncommittedSize {
        return false
    }
    r.uncommittedSize += s
    return true

so with an all-empty batch (`payloadsSize` is then `0`, see `spec_payloadsSize.v`) the
*middle* conjunct is false whatever the budget holds, the reject path is
**unreachable**, and the field is incremented by zero. That is the fact `appendEntry`
needs to show its own `return false` -- and hence `becomeLeader`'s `logger.Panic` --
is dead code. Like `payloadsSize`, it is stated only for the empty-payload case; the
general statement would have to talk about the budget arithmetic, which no caller on
the election path exercises.

Stated against the bare struct points-to rather than `ownRaftPhys`, for two reasons.
It is the minimal ownership the body needs (it touches `uncommittedSize` and
`maxUncommittedSize` and nothing else), and `appendEntry` calls this *between* two
`raftLog` calls that are stated at a fixed log split -- re-sealing `ownRaftPhys` across
it would existentially re-quantify the split and lose the last index it just read. The
new `uncommittedSize` is existential because the value written,
`old + payloadsSize(ents)`, is not worth naming: no predicate in this development
mentions the field. -/
abbrev raft.increaseUncommittedSize.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (es : GoSlice)
    (ents : List raftpb.Entry) (dq : DFrac),
  (∀ e ∈ ents, sint.Z e.Data'.len = 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hes" ∷ es ↦*{dq} ents }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"increaseUncommittedSize"))
      (Val #es))
  {{ RET #true; ownRaftPhys cfg r id s ∗ es ↦*{dq} ents }}

end spec

end EtcdGrove
end Perennial
