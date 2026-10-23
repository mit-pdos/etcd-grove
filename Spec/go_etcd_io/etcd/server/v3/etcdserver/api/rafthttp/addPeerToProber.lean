/-
`addPeerToProber(lg, p, id, us, name, rttSec)` (`probing_status.go`, untranslated; rafthttp stage 6c):
the trust boundary (D34, the user's choice: the prober an axiom). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport

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

/-- **`addPeerToProber(lg, p, id, us, name, rttSec)`**: it returns, `us` only read. -/
abbrev rafthttp.addPeerToProber.spec : Prop :=
  ∀ (lg : Loc) (p : GoInterface) (id : GoString) (us : GoSlice) (dq : DFrac) (ss : List GoString)
    (name : GoString) (h : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      us ↦*{dq} ss }}
    (App (App (App (App (App (App (Val (@! rafthttp.addPeerToProber)) (Val #lg)) (Val #p))
      (Val #id)) (Val #us)) (Val #name)) (Val #h))
  {{ RET #(); us ↦*{dq} ss }}

end spec

end EtcdGrove
end Perennial
