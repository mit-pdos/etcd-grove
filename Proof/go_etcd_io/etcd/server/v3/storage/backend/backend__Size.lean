/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Size.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Size

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.backend.Size.wp_proof : backend.backend.Size.spec (GF := GF) (hG := hG) := by
  intro γ P WR b
  wp_start as #Hb
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  unfold isBackend
  icases Hb with ⟨%t, %rt, %tm, %db, %lg, %h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hm, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 _ (DFrac.own 1) $$ [] [HΦ]
  · iexact Hat
  unfold metricsInv
  iinv Hm with >Hi Hclose
  icases Hi with ⟨%a, %c, %d, %e, Ha, Hc, Hd, He⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists a
  iframe Ha
  iintro Ha
  imod Hmask with -
  imod Hclose $$ [Ha Hc Hd He] with -
  · inext; iexists a, c, d, e; iframe
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
