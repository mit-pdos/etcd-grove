/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/NewServerStats.lean` (`server.go`;
until prove-ps2-v2stats, 2026-11-21, the trust boundary): a fresh `ServerStats`, its start times
`time.Now()`, its two rate queues allocated (`back = -1`), each queue's `RWMutex` made the owner of
its fields (`v2stats.isStatsQueue`) and the stats' mutex the owner of the stats
(`v2stats.ssLockR`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewServerStats
public import Perennial.Spec.time.Now

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Assumptions]

/-- A fresh ring's invariant. -/
theorem v2stats.sqOk_zero (bk : w64) (hb : sint.Z bk = -1) :
    v2stats.sqOk (zero_val (GoArray Loc 200)).arr (W64 0) (W64 0) bk := by
  have h0 : sint.Z (W64 0) = 0 := by decide
  unfold v2stats.sqOk
  rw [h0, hb]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by decide, ?_⟩
  intro k hk0 hk1
  omega

/-- A fresh queue (`&statsQueue{back: -1}`) made a rate queue: its `RWMutex` made the owner of its
fields (only the writers' guard kept). -/
theorem v2stats.sq_init (q : Loc) (v : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.statsQueue)
    (hit : v.items' = zero_val _) (hs : v.size' = W64 0) (hf : v.front' = W64 0)
    (hb : sint.Z v.back' = -1) (hr : v.rwl' = zero_val _) :
    (q ↦ v : IProp GF) ⊢ |={⊤}=> v2stats.isStatsQueue q := by
  obtain ⟨it, sz, fr, bk, tot, rwl⟩ := v
  simp only at hit hs hf hb hr
  subst hit hs hf hr
  iintro Hq
  iStructNamed Hq
  imod sync.init_RWMutex (v2stats.sqP (GF := GF) q) (E := ⊤) (v2stats.sqRwlAddr q)
    $$ [items size front back totalReqSize] rwl with Hslots
  · inext
    iunfold v2stats.sqP
    iexists (zero_val _, W64 0, W64 0, bk, tot)
    iunfold v2stats.sqBody
    iframe
    isplitr
    · ipureintro; exact v2stats.sqOk_zero bk hb
    iapply BigSepL.bigSepL_forall_elim
    iintro %k %y %Hk
    have hy : y = null := by
      have hz : (zero_val (GoArray Loc 200)).arr = List.replicate 200 null := rfl
      have := List.mem_of_getElem? Hk
      simp only [hz] at this
      exact List.eq_of_mem_replicate this
    iunfold v2stats.sqSlot
    ileft; ipureintro; exact hy
  ihave ⟨-, #Hg⟩ := sync.ownRWMutex_slots_guard (v2stats.sqRwlAddr q) (v2stats.sqP (GF := GF) q)
    $$ Hslots
  imodintro
  iunfold v2stats.isStatsQueue
  iexact Hg

theorem v2stats.NewServerStats.wp_proof (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    v2stats.NewServerStats.spec (GF := GF) (hG := hG) := by
  intro name id
  wp_start
  iapply wp_fupd
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  (try wp_auto)
  irename «$r0» => Hs
  generalize «$r0_ptr» = p at *
  ihave %Hnn := typedPointsto_not_null $$ Hs
  iStructNamed Hs
  wp_apply wp_Now as %t -
  (try wp_auto)
  irename: (_ ↦ (_ : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.statsQueue)) => Hq1
  imod v2stats.sq_init _ _ rfl rfl rfl (by simp only; decide) rfl $$ Hq1 with #Hq1
  irename: (_ ↦ (_ : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.statsQueue)) => Hq2
  imod v2stats.sq_init _ _ rfl rfl rfl (by simp only; decide) rfl $$ Hq2 with #Hq2
  imod sync.init_Mutex (v2stats.ssLockR p _ _) ⊤ (v2stats.ssMutexAddr p) $$ Mutex [serverStats]
    with #Hmu
  · inext
    iunfold v2stats.ssLockR
    iexists _
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  iunfold v2stats.isServerStats
  iexists _, _
  iframe #

end proof

end EtcdGrove
end Perennial
