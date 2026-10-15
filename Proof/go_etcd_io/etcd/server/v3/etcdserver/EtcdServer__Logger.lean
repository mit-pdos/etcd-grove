/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Logger.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.Logger.wp_proof : EtcdServer.Logger.spec (GF := GF) (hG := hG) := by
  intro s l
  wp_start as ⟨#Hlg, %Hnn, Hrd⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvLgReader at Hrd
  icases Hrd with ⟨%mu, #Hmu, Hh⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hh] as ⟨Hlk, HP⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk] as Hh
  · inext; itrivial
  iapply HΦ
  iframe %Hnn
  iunfold srvLgReader
  iexists mu
  iframe Hmu Hh

end proof

end EtcdGrove
end Perennial
