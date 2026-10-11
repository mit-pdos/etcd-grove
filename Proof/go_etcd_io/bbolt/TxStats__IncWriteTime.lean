module
public import Spec.go_etcd_io.bbolt.TxStats__IncWriteTime
public import Proof.go_etcd_io.bbolt.Atomics
public import Spec.go_etcd_io.bbolt.atomicAddDuration

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

theorem TxStats.IncWriteTime.wp_proof (hAdd : atomicAddDuration.spec (GF := GF) (hG := hG)) :
    TxStats.IncWriteTime.spec (GF := GF) (hG := hG) := by
  intro l v delta
  wp_start as Hl
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  icases (TxStats.TxStats_access_store_WriteTime l v (v.WriteTime' + delta)).access_strict $$ Hl
    with ⟨Hf, Hclose⟩
  wp_auto
  wp_apply hAdd $$ [$Hf] as Hf
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iapply Hclose $$ Hf

end proof

end bbolt
end EtcdGrove
end Perennial
