/-
`grpc.MaxCallSendMsgSize(n)` (`google.golang.org/grpc`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `grpc.MaxCallSendMsgSize(n)` returns some call option (a `MaxSendMsgSizeCallOption`). -/
abbrev grpc.MaxCallSendMsgSize.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.MaxCallSendMsgSize)) (Val #n))
  {{ (o : GoInterface), RET #o; True }}

end spec

end EtcdGrove
end Perennial
