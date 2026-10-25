/-
`checkClusterCompatibilityFromHeader(lg, localID, header, cid)` (`http.go`; rafthttp stage 4): the
pipeline and stream handlers' version and cluster check of a request's headers. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Pipe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The handlers' header check**, on a received request's headers: `nil`, or one of the two
errors it reports (`errIncompatibleVersion`, `ErrClusterIDMismatch`), or a panic (`semver`'s
`MustParse` of an unparsable version header). -/
abbrev rafthttp.checkClusterCompatibilityFromHeader.spec : Prop :=
  ∀ (lg : Loc) (localID cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (hm : Loc)
    (hs : List (GoString × GoString)),
  lg ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      http.hdrAt hm hs }}
    (App (App (App (App (Val (@! rafthttp.checkClusterCompatibilityFromHeader)) (Val #lg))
      (Val #localID)) (Val #hm)) (Val #cid))
  {{ (r : val), RET r;
      ⌜r = #GoInterface.nil ∨ ∃ p, r = PanicV p⌝ ∨
      ∃ e : GoInterface, ⌜r = #e⌝ ∗
        (globalAddr rafthttp.errIncompatibleVersion ↦□ e ∨
         globalAddr rafthttp.ErrClusterIDMismatch ↦□ e) }}

end spec

end EtcdGrove
end Perennial
