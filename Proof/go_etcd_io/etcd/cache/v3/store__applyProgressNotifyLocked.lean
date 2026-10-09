/-
Proof of `Spec/store__applyProgressNotifyLocked.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.store__applyProgressNotifyLocked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem store.applyProgressNotifyLocked.wp_proof :
    store.applyProgressNotifyLocked.spec (GF := GF) (hG := hG) := by
  intro s γ cap lr revision
  wp_start as ⟨#Hs, Hrev⟩
  unfold isStore
  iNamed Hs
  wp_auto
  wp_if_destruct
  · wp_end
  · wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
    rw [show (if lr = W64 0 then lr else revision) = revision by rw [ite_eq_right_iff]; intro h; exact absurd h Hif]
    wp_end

end proof

end EtcdGrove
end Perennial
