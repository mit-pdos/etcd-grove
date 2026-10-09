/-
Port of election_proof/spec_raft__increaseUncommittedSize.v (feb5c73d4).

Lean notes:
* The reference `raft__increaseUncommittedSizeⁱᵐᵖˡ` is to the Lean generated code
  `raft.increaseUncommittedSize.impl`.
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

/-- `r.increaseUncommittedSize(ents)`: charge a batch against the uncommitted-entries
budget, and say whether it fits (`raft.increaseUncommittedSize.impl`,
`Code/go_etcd_io/raft/v3.lean`).

The body is

    s := payloadsSize(ents)
    if r.uncommittedSize > 0 && s > 0 && r.uncommittedSize+s > r.maxUncommittedSize {
        return false
    }
    r.uncommittedSize += s
    return true

so with an all-empty batch (`payloadsSize` is then `0`, see `spec_payloadsSize.v`) the
*middle* conjunct is false whatever the budget holds and the reject path is
**unreachable**. That is the fact `appendEntry` needs to show its own `return false` --
and hence `becomeLeader`'s `logger.Panic` -- is dead code, and it is what the
postcondition's implication says.

Since 2026-10-01 the triple takes an *arbitrary* batch (until then it required the
all-empty one and returned `RET #true`), because `appendEntry` was widened to arbitrary
`EntryNormal` proposals and has a reachable drop path. The result is a bare
`ok : Bool`: the exact reject condition reads `r.uncommittedSize` and
`r.maxUncommittedSize`, neither of which `NState` holds, so it cannot be stated against
`ownRaftPhys`; what *can* be stated is the empty-batch implication above. On either
path the struct is at the same `s`: the accept path writes
`uncommittedSize := old + payloads`, a field `ownRaftPhys` does not pin, and the reject
path writes nothing.

Stated against `ownRaftPhys` and the batch, which is all the body touches
(`uncommittedSize`, `maxUncommittedSize`, and `payloadsSize`'s read of the slice). The
new `uncommittedSize` is not named because no predicate in this development mentions
the field. -/
abbrev raft.increaseUncommittedSize.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (es : GoSlice)
    (ents : List raftpb.Entry) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hes" ∷ es ↦*{dq} ents }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"increaseUncommittedSize"))
      (Val #es))
  {{ (ok : Bool), RET #ok;
      ownRaftPhys cfg r id s ∗ es ↦*{dq} ents ∗
      -- an all-empty batch is never rejected
      ⌜(∀ e ∈ ents, sint.Z e.Data'.len = 0) → ok = true⌝ }}

end spec

end EtcdGrove
end Perennial
