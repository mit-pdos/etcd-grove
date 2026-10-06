/-
Port of `election_proof/spec_traceReplicate.v`.
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

/-- `traceReplicate(r, es...)`: a tracing hook, and a **no-op** -- Goose translates it
to `λ: <> <>, exception_do (do: #())` (`new/code/go_etcd_io/raft/v3.v:6364`). Same
shape as `spec_traceSendMessage.v`; `appendEntry` is the caller, and it hands the entry
slice over only so that the triple has a resource to thread (the body touches nothing).

**It owns nothing** (changed 2026-09-23). Goose translates the hook to
`exception_do (do: #())`: it reads nothing and writes nothing, so the honest triple
takes no resource and gives none back. Until then it carried the entries slice in and
out, which it never touches; the other five hooks carried a raw piece of the raft
struct (`own_raft_misc`), and all six now own nothing (notes/decisions.md, "Three
layers"). This is a fact about the no-op build that is translated; the tracing build
reads `r` and would need a real spec on `ownRaftPhys`. -/
abbrev traceReplicate.spec : Prop :=
  ∀ (r : Loc) (es : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (App (Val #(functions traceReplicate [])) (Val #r)) (Val #es))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
