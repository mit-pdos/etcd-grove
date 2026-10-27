/-
**Facts the server's link takes as terms** (rafthttp stage 6f, `etc/gen-link.py`'s `=` callees):
statements a rafthttp proof takes as a hypothesis that are not a Go function's spec.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Pipe

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove

open Iris

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- `writerToResponse` is an interface type: a target of `errors.As` (the pipeline handler's
`errors.As(err, &writerErr)`). -/
theorem rafthttp_writerToResponse_asTarget :
    errors.AsTarget go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.writerToResponse.ty :=
  Or.inl ⟨_, (go.underlying_unfold (t := go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.writerToResponse.ty)).trans
    go.is_underlying⟩

end

end EtcdGrove
end Perennial
