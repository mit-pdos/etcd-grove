/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/closeNotifier__Close.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.closeNotifier__Close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
theorem rafthttp.closeNotifier.Close.wp_proof :
    rafthttp.closeNotifier.Close.spec (GF := GF) (hG := hG) := by
  intro n γ P
  wp_start as ⟨Hcl, HP⟩
  iunfold cnClose at Hcl
  icases Hcl with ⟨%dc, %γc, #Hdc, Hdb⟩
  imod inv_alloc cnN ⊤ iprop(P ∨ cnTok γ) $$ [HP] with #Hinv
  · inext; ileft; iexact HP
  (try wp_auto)
  wp_apply (wp_broadcast_chan_close _ γc (cnQ γ P)) $$ [Hdb] as -
  · iframe; unfold cnQ; imodintro; iexact Hinv
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
