/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__safePending.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__safePending

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.batchTx.safePending.wp_proof :
    backend.batchTx.safePending.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t u
  wp_start as ⟨#Hb, #Ht, Hopn, Hu⟩
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #Hlim, #Hh, #Hhs, #Hm, #Hdb0, %HP⟩
  · iframe #
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hown, Hfree⟩
  unfold batchFree
  icases Hfree with (⟨%st, %db, Hph, Hg, %Hfo, HWR⟩ | #Hbs)
  · unfold batchPhys batchGhostAt
    icases Hph with ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩
    icases Hg with ⟨Hv, %n, %w, %u0, Hrvs, Ha, Hmo, Hus, Hopn', %Hbg⟩
    icombine Hu Hus gives % ⟨_, Hueq⟩
    subst Hueq
    ihave #Hlb := monoNatLbOwn_get γ.wbc 1 w $$ Hmo
    ihave Hlbr : (⌜st.pend = W64 0⌝ ∨ monoNatLbOwn γ.wbc (u + 1)) $$ []
    · by_cases hp : st.pend = W64 0
      · ileft; ipureintro; exact hp
      · iright
        have := (Hbg.2.2.2.2.2.2.2.2 rfl).2 hp
        iapply monoNatLbOwn_le (u + 1) (by omega) $$ Hlb
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hown Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu Hv Hrvs Ha Hmo Hus Hopn' HWR]
    · inext
      ileft
      iexists st, db
      iframe HWR
      isplitl [Htxf Hpend Hdel HW Hhkf Hhk Hdb Hwtx Hmu]
      · iexists hk
        iframe
        iframe #
      isplitl
      · iframe Hv
        iexists n, w, u
        iframe
        ipureintro
        exact Hbg
      · ipureintro
        exact Hfo
    try wp_auto
    iapply HΦ
    iframe
  · unfold bStopped
    icombine Hopn Hbs gives %Hcb
    exact absurd Hcb.2 (by decide)

end proof

end EtcdGrove
end Perennial
