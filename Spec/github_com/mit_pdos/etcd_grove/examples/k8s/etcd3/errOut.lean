/- Lean-first (no Rocq counterpart).

`errOut(err)` (k8s_etcd3.go): the output `y` of an error whose kind is known (`errIs err y`:
`Proof/.../k8setcd3/Calls.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev errOut.spec : Prop :=
  ∀ [go_etcd_io.etcd.client.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] (err : GoInterface) (y : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      errIs err y }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errOut)) (Val #err))
  {{ RET #y; True }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
