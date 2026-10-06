/-
Port of `election_proof/spec_unstable__maybeTerm.v`.

Lean notes:
* Rocq's `(#t, #ok)` is `PairV #t #ok`; the chained `a ≤ b < c` is a conjunction.
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

/-- `u.maybeTerm(i)`: the term of index `i` if the unstable suffix covers it. `ok` pins
down exactly which indices those are, which is what `raftLog.term` needs in order to
decide whether to fall through to `Storage`.

As with the other two `maybe*` methods, on a bare `*unstable` and with
`snapshot = nil` as a premise. The `i >= offset` branch calls `maybeLastIndex`, which
is why that is a postulate here. -/
abbrev unstable.maybeTerm.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry) (i : w64),
  uv.snapshot' = null →
  uint.Z uv.offset' + (uents.length : Int) < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"maybeTerm")) (Val #i))
  {{ (t : w64) (ok : Bool), RET (PairV #t #ok);
      ownUnstable u uv uents ∗
      ⌜ok = true ↔ (uint.Z uv.offset' ≤ uint.Z i ∧
                    uint.Z i < uint.Z uv.offset' + (uents.length : Int))⌝ }}

end spec

end EtcdGrove
end Perennial
