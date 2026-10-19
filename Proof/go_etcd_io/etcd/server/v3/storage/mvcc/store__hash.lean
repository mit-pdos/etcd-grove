/-
Proof of `Spec/.../mvcc/store__hash.lean`, of the code of etcd-io/etcd#22609. Lean-first (no Rocq
counterpart).

`currentRev` is read under `s.revMu.RLock()`, from `revMuInv`'s part of its points-to (the
writer holds the other); the code before the PR read it with no lock, which no part of the store
invariant allows (`issues/etcd-mvcc-hash-currentrev-unlocked.md`). `s.b` is read under
`s.mu.RLock()`, though the invariant holds it read-only (`isStore`'s `Hb`: `Restore`, which
replaces it, is out of scope), so the proof does not depend on that lock.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__hash
public import Spec.time.Duration__Seconds
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.hash.wp_proof
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG)) :
    mvcc.store.hash.spec (GF := GF) (hG := hG) := by
  intro s γ log₀
  wp_start as ⟨#Hs, #Hho, Hrd, Hwt, #Hc0⟩
  iunfold mvcc.idxCert at Hc0
  icases Hc0 with ⟨-, -, -, #Hl0, -⟩
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReaderC at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  iunfold mvcc.storeHashOk at Hho
  icases Hho with ⟨%bh, #Hbh, #HHash⟩
  icombine Hb Hbh gives %Hbeq
  subst Hbeq
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, -, -, #HForce, -⟩
  cases Hbi
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, ⟨%hSecM, #HSecG, #HSecS⟩, -⟩
  iunfold histSpec at HSecS
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply time.wp_Now as %t0 -
  (try wp_auto)
  -- `s.mu.RLock()`; `b := s.b`; `b.ForceCommit()`; `s.mu.RUnlock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, HmuP⟩
  (try wp_auto)
  wp_apply HForce $$ [$HrtR $Hwt] as HrtR
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hmul $HmuP] as HmuR
  (try wp_auto)
  -- `b.Hash(schema.DefaultIgnores)`: the trust boundary
  wp_apply HHash as %h %err -
  (try wp_auto)
  -- `s.revMu.RLock()`; `revision = s.currentRev`; `s.revMu.RUnlock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HrevMuR] as ⟨Hrevl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.revMuInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.revMuInv at HP
  icases HP with ⟨%log, %ntok, %c, HP⟩
  iNamed HP
  ihave %Hpre := mono_list_auth_lb_valid γ.idx.log _ _ _ $$ Hlog Hl0
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrevl Hrev Hbucket Hclog Hcert Htoks Hlog Hcmp Hcrev]
    as HrevMuR
  · inext
    iunfold mvcc.revMuInv
    iexists log, ntok, c
    simp only [named]
    iframe Hrev Hbucket Hclog Htoks Hlog Hcmp Hcrev
    iframe #
    ipureintro; exact ⟨Hne, Hbudget, Hc⟩
  (try wp_auto)
  -- `hashSec.Observe(time.Since(start).Seconds())`
  wp_apply time.wp_Since as %d -
  (try wp_auto)
  -- (`Duration`'s method: its underlying `int64` is no interface)
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_apply hSec as %f -
  (try wp_auto)
  wp_apply HSecS
  (try wp_auto)
  iapply HΦ
  isplitl [HmuR HrevMuR HtiR HrtR]
  · iunfold mvcc.storeReaderC
    iexists ti2
    simp only [named]
    iframe HmuR HrevMuR HtiR HrtR HidxR
  iexists log
  iframe Hcert
  ipureintro
  exact ⟨Hpre.2, Hne, rfl⟩

end proof

end EtcdGrove
end Perennial
