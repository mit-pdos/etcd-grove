/- Lean-first (no Rocq counterpart).

`deliverable(m)` (cluster.go): whether the transport passes `m` on; `true` only for a
message that is `Deliverable` (`Cluster.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

/-- See the file header. -/
abbrev deliverable.spec : Prop :=
  ∀ (m : raftpb.Message),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.deliverable)) (Val #m))
  {{ (b : Bool), RET #b; ⌜b = true → Deliverable m⌝ }}

end spec

end register
end EtcdGrove
end Perennial
