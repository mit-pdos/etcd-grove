/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__lockedReadTx.lean`. Lean-first (no Rocq
counterpart; D22k (A)).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__lockedReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.lockedReadTx.wp_proof :
    auth.authStore.lockedReadTx.spec (GF := GF) (hG := hG) := by
  intro st R M
  wp_start as ⟨#Hinv, Hrd, HR⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, -, -, -, -, -⟩
  iunfold beRd at Hrd
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold beP at HP
  icases HP with ⟨%be, %γc, Hbe, #Hbeok, Hcu⟩
  ihave #Hbeok' := Hbeok
  iunfold authBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HRT⟩
  subst Hbi
  wp_auto
  wp_apply HRT as %tx Htx
  ihave Htx := authReadTxOk_rd _ R M γc $$ Htx
  icases Htx with ⟨%ti, %Hti, %Hs, #HRL, -, #Hreads⟩
  subst Hti
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
  iapply HRL $$ %sync.rfrac [HR Hcu]
  · iframe HR Hcu
  inext
  iintro ⟨%sta, Htok, #Hsnap, Hcu⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hbe Hcu] as Hrd
  · inext; iunfold beP; iexists _, γc; iframe Hbe Hbeok Hcu
  iapply HΦ
  iunfold beRd
  iframe Hrd
  iunfold authReadTxLocked
  iexists ti
  isplitr
  · ipureintro; rfl
  iexists sta, Hs
  iframe Htok
  iframe #

end proof

end EtcdGrove
end Perennial
