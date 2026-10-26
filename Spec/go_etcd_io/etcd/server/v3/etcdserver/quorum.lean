/-
`quorum` (`util.go`: `num/2 + 1`). Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `quorum(num)`: some count (`num / 2 + 1`; `isConnectedToQuorumSince` only compares with it). -/
abbrev quorum.spec : Prop :=
  ∀ (num : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.quorum)) (Val #num))
  {{ (q : w64), RET #q; True }}

end spec

end EtcdGrove
end Perennial
