/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/newConditionalProgressRequestor.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newConditionalProgressRequestor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newConditionalProgressRequestor.wp_proof :
    newConditionalProgressRequestor.spec (GF := GF) (hG := hG) := by
  intro n clk ri
  wp_start
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  wp_apply sync.wp_NewCond (interface.mk (go.GoType.PointerType sync.Mutex.ty)
    #(prMuxAddr «$r0_ptr»)) $$ [$Hsync] as %cp #Hcond
  ipersist cond
  ipersist notifier
  ipersist requestInterval
  ipersist clock
  imod sync.init_Mutex (prLockInv (GF := GF) «$r0_ptr») ⊤ (prMuxAddr «$r0_ptr») $$ mux
    [waiting stopped] with #Hmu
  · inext
    unfold prLockInv
    iexists _, _
    iframe
  imodintro
  iapply HΦ
  unfold isProgressRequestor isPrRun
  iframe #

end proof

end EtcdGrove
end Perennial
