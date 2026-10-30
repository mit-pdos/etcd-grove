module
public import Spec.go_etcd_io.bbolt.DB__Stats

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

variable [AllG GF]

theorem DB.Stats.wp_proof :
    DB.Stats.spec (GF := GF) (hG := hG) := by
  intro dbl sp sv dq q P
  wp_start as ⟨Hsp, Hmu, Hs⟩
  ihave #Hsy : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  wp_auto
  by_cases Hn : sp = null
  · subst Hn
    try wp_auto
    rw [if_pos rfl] at *
    iapply HΦ
    iframe
  · icases Hs with (%Hn' | Hs)
    · exact (Hn Hn').elim
    rw [if_neg Hn] at *
    rw [decide_eq_false Hn]
    try wp_auto
    wp_apply sync.RWMutex.wp_RLock _ _ $$ [$Hmu] as ⟨Hrl, HP⟩
    try wp_auto
    wp_apply sync.RWMutex.wp_RUnlock _ _ $$ [$Hrl $HP] as Hmu
    try wp_auto
    iapply HΦ
    iframe
    try (iright; iexact Hs)

end proof

end bbolt
end EtcdGrove
end Perennial
