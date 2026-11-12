/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.filterNoPut

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.filterNoPut.wp_proof : v3rpc.filterNoPut.spec (GF := GF) (hG := hG) := by
  intro e ev
  wp_start as #Hev
  iunfold mvcc.evIs at Hev
  icases Hev with ⟨%p, %q, %st, %uf, %sc, %Hn, #He, -, -⟩
  icases mvcc.event_fields _ _ _ $$ He with ⟨#HT, -, -⟩
  wp_auto
  iapply HΦ
  ipureintro
  unfold mvcc.evType
  have h10 : decide (W32 1 = W32 0) = false := by decide
  have h01 : decide (W32 0 = W32 1) = false := by decide
  cases ev.del <;> simp [h10, h01]

end proof

end EtcdGrove
end Perennial
