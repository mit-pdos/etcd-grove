/-
Port of `election_proof/spec_traceBecomeFollower.v`.
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

/-- `traceBecomeFollower(r)`: a tracing hook, and a **no-op** -- Goose translates it to
`λ: <> <>, exception_do (do: #())`. See `spec_traceReceiveMessage.v`; `becomeFollower`
is the caller.

**It owns nothing** (changed 2026-09-23). Goose translates the hook to
`exception_do (do: #())`: it reads nothing and writes nothing, so the honest triple
takes no resource and gives none back. Until then it carried a piece of the raft
struct in and out (`own_raft_misc`), which was a spec on a raw piece of the struct --
exactly what the one-predicate rule (notes/decisions.md, "Three layers") rules out --
and was left that way only to spare the callers a re-seal. Owning nothing spares them
the re-seal *and* obeys the rule. This is a fact about the no-op build that is
translated; the tracing build reads `r` and would need a real spec on `ownRaftPhys`. -/
abbrev traceBecomeFollower.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions traceBecomeFollower [])) (Val #r))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
