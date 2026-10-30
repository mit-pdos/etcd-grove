module
public import Spec.go_etcd_io.bbolt.TxStats__GetSpillTime
public import Proof.go_etcd_io.bbolt.Atomics
public import Spec.go_etcd_io.bbolt.atomicLoadDuration

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem TxStats.GetSpillTime.wp_proof (hLoad : atomicLoadDuration.spec (GF := GF) (hG := hG)) :
    TxStats.GetSpillTime.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  icases (TxStats.TxStats_access_load_SpillTime l v dq).access_strict $$ Hl with ⟨Hf, Hclose⟩
  wp_auto
  wp_apply hLoad $$ [$Hf] as Hf
  iapply HΦ
  iapply Hclose $$ Hf

end proof

end bbolt
end EtcdGrove
end Perennial
