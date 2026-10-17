/-
`(*EtcdServer).publishV3(timeout)` (`server.go`), with its body since etcd-io/etcd#22525 (until then
names-only, an axiom that it returns): the publish loop, with the PR's snapshot check. One of the
goroutines `Start` attaches. Lean-first; see `InvPublish.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvPublish

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.publishV3(d)`** (the member `id` with attributes `a`, URLs `cus`, in the cluster `c`;
the snapshot notifier `n`): from the request path's view and a request goroutine's resources (a
`leadTimeMu` reader slot, the auth reader `E.RD`, a `lgMu` reader slot, given back), all the
notifier's reader slots (for the snapshot check's goroutines) and the right to close `s.readych`,
it returns either with `s.readych` still open (the server is stopping) or with `s.readych` closed
and the member's attributes published (`pubDone`: its own request applied, or the membership seen
to hold them after a snapshot). -/
abbrev EtcdServer.publishV3.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (c : Loc) (id : w64)
    (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (cus : List GoString)
    (n : Loc) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvPubFields s E ρ c id a cus n ∗
      srvLeadTimeReader s ∗ E.RD ∗ srvLgReader s ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), notifyReader n) ∗
      srvReady s iprop(⌜pubDone c id a cus⌝) .Pending }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"publishV3")) (Val #d))
  {{ RET #(); srvLeadTimeReader s ∗ E.RD ∗ srvLgReader s ∗
      (srvReady s iprop(⌜pubDone c id a cus⌝) .Pending ∨
       srvReady s iprop(⌜pubDone c id a cus⌝) .Done ∗ ⌜pubDone c id a cus⌝) }}

end spec

end EtcdGrove
end Perennial
