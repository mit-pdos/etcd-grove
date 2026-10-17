/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/NewMessage.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.NewMessage
public import Spec.go_etcd_io.etcd.pkg.v3.ioutil.NewExactReadCloser
public import Spec.google_golang_org.protobuf.proto.SizeMessage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.pkg.v3
  go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.NewMessage.wp_proof
    (hE : ioutil.NewExactReadCloser.spec (GF := GF) (hG := hG))
    (hS : proto.SizeMessage.spec (GF := GF) (hG := hG)) :
    snap.NewMessage.spec (GF := GF) (hG := hG) := by
  intro rs dq ms rc rcSize
  wp_start as Hm
  ihave #Pio : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil $$ []
  · iPkgInit
  ihave #Ppr : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_auto
  wp_apply hE rc rcSize as %x ⟨%e, %Hx, He⟩
  wp_apply hS rs dq ms $$ [Hm] as %sz ⟨Hm, %Hsz⟩
  · iframe Hm
  wp_apply chan.wp_make2 (V := Bool) (W64 1) $$ [] as %ch %γ ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  subst Hx
  wp_alloc m as Hmsg
  wp_auto
  iapply HΦ
  iexists e, sz, ch, γ
  iframe Hmsg He Hm Hch Hown
  ipureintro; exact ⟨Hsz, Hcap⟩
  done

end proof

end EtcdGrove
end Perennial
