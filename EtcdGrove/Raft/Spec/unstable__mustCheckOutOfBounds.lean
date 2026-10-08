/- Port of election_proof/spec_unstable__mustCheckOutOfBounds.v (feb5c73d4). -/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `u.mustCheckOutOfBounds(lo, hi)`: panics unless
`u.offset <= lo <= hi <= u.offset + len(u.entries)`.

Both `Panicf` calls have to be shown unreachable, since `Logger.wp_logf` does not cover
them; that is what the range premise is for. The no-wrap premise is what lets
`offset + len(entries)` be computed without overflow. On a bare `*unstable` with the
entry slice beside it, like the `maybe*` specs; any fraction, since it only reads the
slice's length. -/
abbrev unstable.mustCheckOutOfBounds.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (lo hi : w64),
  uint.Z us.offset ≤ uint.Z lo ∧ uint.Z lo ≤ uint.Z hi ∧
    uint.Z hi ≤ uint.Z us.offset + (us.ents.length : Int) →
  uint.Z us.offset + (us.ents.length : Int) < 2^64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"mustCheckOutOfBounds"))
      (Val #lo)) (Val #hi))
  {{ RET #(); ownUnstable u us }}

end spec

end EtcdGrove
end Perennial
