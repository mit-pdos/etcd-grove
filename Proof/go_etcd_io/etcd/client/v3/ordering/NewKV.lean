/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ordering/NewKV.lean`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ordering.NewKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.ordering

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

theorem NewKV.wp_proof : NewKV.spec (GF := GF) (hG := hG) := by
  intro kv vf R
  wp_start as #HR0
  iapply wp_fupd
  wp_auto
  wp_alloc kvp as Hkvp
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hkvp
  iStructNamed Hkvp
  ipersist KV
  ipersist orderViolationFunc
  imod sync.init_RWMutex (kvOrderingLockInv (hG := hG) kvp R) (revMuAddr kvp)
    $$ [prevRev] revMu with Htoks
  · inext
    unfold kvOrderingLockInv
    iexists W64 0
    iframe; iexact HR0
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m := ⟨_, rfl⟩
  rw [hm]
  imodintro
  iapply HΦ $$ %kvp
  isplitr [Htoks]
  · unfold isKvOrdering
    iframe #
    ipureintro; exact Hnn
  unfold kvOrderingHandle
  iexact Htoks

end proof

end ordering
end EtcdGrove
end Perennial
