/-
The trust boundary: `authStore.selectPassword` (names only: bcrypt and base64). Why it is true of the Go code is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__selectPassword

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

axiom auth.authStore.selectPassword.wp_proof : auth.authStore.selectPassword.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
