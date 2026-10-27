/-
Proof of `Spec/.../mvcc/store__setupMetricsReporter.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__setupMetricsReporter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.setupMetricsReporter.wp_proof :
    mvcc.store.setupMetricsReporter.spec (GF := GF) (hG := hG) := by
  intro s b dq
  wp_start as Hb
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, #G0, #G1, #G2, #G3, #G4⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  -- reporter 0: its lock, the closure stored, unlocked
  wp_apply (sync.RWMutex.wp_Lock_guard _ _) $$ [$G0] as ⟨Hl0, HP0⟩
  iunfold reportP at HP0
  icases HP0 with ⟨%f0, Hf0⟩
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hl0 Hf0]
  · inext; iunfold reportP; iexists _; iframe
  (try wp_auto)
  -- reporter 1: its lock, the closure stored, unlocked
  wp_apply (sync.RWMutex.wp_Lock_guard _ _) $$ [$G1] as ⟨Hl1, HP1⟩
  iunfold reportP at HP1
  icases HP1 with ⟨%f1, Hf1⟩
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hl1 Hf1]
  · inext; iunfold reportP; iexists _; iframe
  (try wp_auto)
  -- reporter 2: its lock, the closure stored, unlocked
  wp_apply (sync.RWMutex.wp_Lock_guard _ _) $$ [$G2] as ⟨Hl2, HP2⟩
  iunfold reportP at HP2
  icases HP2 with ⟨%f2, Hf2⟩
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hl2 Hf2]
  · inext; iunfold reportP; iexists _; iframe
  (try wp_auto)
  -- reporter 3: its lock, the closure stored, unlocked
  wp_apply (sync.RWMutex.wp_Lock_guard _ _) $$ [$G3] as ⟨Hl3, HP3⟩
  iunfold reportP at HP3
  icases HP3 with ⟨%f3, Hf3⟩
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hl3 Hf3]
  · inext; iunfold reportP; iexists _; iframe
  (try wp_auto)
  -- reporter 4: its lock, the closure stored, unlocked
  wp_apply (sync.RWMutex.wp_Lock_guard _ _) $$ [$G4] as ⟨Hl4, HP4⟩
  iunfold reportP at HP4
  icases HP4 with ⟨%f4, Hf4⟩
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  wp_apply (sync.RWMutex.wp_Unlock_guard _ _) $$ [$Hl4 Hf4]
  · inext; iunfold reportP; iexists _; iframe
  (try wp_auto)
  iapply HΦ
  iframe Hb

end proof

end EtcdGrove
end Perennial
