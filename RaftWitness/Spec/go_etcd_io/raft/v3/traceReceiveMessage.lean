/-
Port of `election_proof/spec_traceReceiveMessage.v` (feb5c73d4).
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

/-- `traceReceiveMessage(r, m)`: a tracing hook, and a **no-op**.

Goose translates it to `λ: <> <>, exception_do (do: #())`, so this is a two-line proof
and not an assumption; it was an axiom until 2026-09-16 purely because nobody had
looked at the generated body. The spec carries `own_raft_misc` in and out so that the
call composes where `Step` makes it, without claiming anything about the rest of the
struct.

**It owns nothing** (changed 2026-09-23). Goose translates the hook to
`exception_do (do: #())`: it reads nothing and writes nothing, so the honest triple
takes no resource and gives none back. Until then it carried a piece of the raft
struct in and out (`own_raft_misc`), which was a spec on a raw piece of the struct --
exactly what the one-predicate rule (notes/decisions.md, "Three layers") rules out --
and was left that way only to spare the callers a re-seal. Owning nothing spares them
the re-seal *and* obeys the rule. This is a fact about the no-op build that is
translated; the tracing build reads `r` and would need a real spec on `ownRaftPhys`. -/
abbrev traceReceiveMessage.spec : Prop :=
  ∀ (r : Loc) (mp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (App (Val #(functions traceReceiveMessage [])) (Val #r)) (Val #mp))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
