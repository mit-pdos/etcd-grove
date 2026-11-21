/- Snapshot reads use the open bbolt read transaction even after the writer commits. -/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__UnsafeForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeForEach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.snapshot.UnsafeForEach.wp_proof
    (visit : backend.unsafeForEach.spec (GF := GF) (hG := hG)) :
    backend.snapshot.UnsafeForEach.spec (GF := GF) (hG := hG) := by
  intro sp tx γ γd q D bk bi fn I E
  wp_start as ⟨#Ha, Hl, #Hb, HI, #Hf⟩
  iunfold snapAt at Ha
  icases Ha with ⟨%sc, %dc, %γsc, %γdc, #Htx, -⟩
  wp_auto
  wp_apply (visit tx γd q (bbolt.TxView.ro D) bk bi fn I E (by simp [bbolt.TxView.ro])) $$ [$Hl $HI]
    as %err ⟨Hl, Hres⟩
  · rw [show (bbolt.TxView.ro D).cur = D from rfl]
    iframe #
  iapply HΦ
  iframe

end proof
end EtcdGrove
end Perennial
