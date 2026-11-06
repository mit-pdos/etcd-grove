/-
`togRPCError`'s triple without its description (k8s etcd3 7c-2): `togRPCError.spec` at
`P := fun _ => True`, what its callers that do not look at the description take. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`togRPCError(err)`** of an error it can take (`srvErrIs`): a non-nil error (its spec at
`P := fun _ => True`, `errMsgP_of_srvErrIs`). -/
theorem v3rpc.togRPCError_plain (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.srvErrIs err }}
      (App (Val (@! v3rpc.togRPCError)) (Val #err))
    {{ (e : GoInterface), RET #e; ⌜e ≠ GoInterface.nil⌝ }} := by
  wp_start_folded as #Herr
  ihave #HP := v3rpc.errMsgP_of_srvErrIs err $$ Herr
  wp_apply hTog (fun _ => True) err $$ [] as %e ⟨%Hne, -⟩
  · iframe #
  iapply HΦ
  ipureintro; exact Hne

end lemmas

end EtcdGrove
end Perennial
