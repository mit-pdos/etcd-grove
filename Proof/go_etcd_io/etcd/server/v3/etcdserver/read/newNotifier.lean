/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/newNotifier.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.newNotifier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

theorem read.newNotifier.wp_proof : read.newNotifier.spec (GF := GF) (hG := hG) := by
  intro γr
  wp_start
  imod mono_nat_own_alloc 0 with ⟨%γn, Hauth, -⟩
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#Hch, -, Hoc⟩
  wp_alloc nc as Hnc
  iStructNamed Hnc
  ipersist c
  imod alloc_broadcast_chan (notified nc γn γr) γ ch $$ Hch Hoc with Hbc
  icases bcast_pending_unknown _ _ _ $$ Hbc with ⟨Hbc, #Hbu⟩
  wp_auto
  iapply HΦ
  iexists γn
  iframe Hauth
  isplitr
  · iunfold notifierIs; iexists ch; iframe c; iunfold bcastChan; iexists γ; iexact Hbu
  · iunfold notifierOwn; iexists ch, γ, GoInterface.nil; iframe c Hbc err

end proof

end EtcdGrove
end Perennial
