/-
`credentials.NewPerRPCCredentialBundle()` (`client/v3/credentials`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
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

/-- `credentials.NewPerRPCCredentialBundle()` returns a non-nil bundle (`&perRPCCredentialBundle{}` as a
`PerRPCCredentialsBundle`). -/
abbrev credentials.NewPerRPCCredentialBundle.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials }}
    (App (Val (@! go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle)) (Val #()))
  {{ (b : GoInterface), RET #b; ⌜b ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
