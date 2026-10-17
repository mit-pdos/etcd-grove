/-
Unfinished (unchanged by PR etcd#22338; the spec is pr-verify/etcd-22560's postulate, a `sorry`
here, where `stop` is translated with bodies): `simpleTokenTTLKeeper.stop` returns. What is
missing: the channel protocol of `stopc`/`donec` with `run` (`keeperChans`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.simpleTokenTTLKeeper__stop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.simpleTokenTTLKeeper.stop.wp_proof :
    auth.simpleTokenTTLKeeper.stop.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
