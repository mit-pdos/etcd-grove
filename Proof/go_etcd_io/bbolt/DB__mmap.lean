/-
The proof of `Mmap/Remap`'s `DB.mmap.spec` (U4d, `notes/bbolt-proof-plan.md`): `mmaplock.Lock()`
(through its guard, `Pm 1`), `defer mmaplock.Unlock()`, `db.mmapUnlocked(minsz)`
(`Mmap/RemapBody`'s `DB.mmapUnlocked.spec`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.RemapBody
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `mmaplock`'s guard (`isBoltCoreP`). -/
theorem BC.core_mmaplock (K : BC) :
    K.core (GF := GF) ⊢ sync.isRWMutexGuard K.db.[DB, go!"mmaplock"] (Pm K.B K.db) := by
  unfold BC.core isBoltCoreP
  iintro ⟨-, -, -, -, -, -, -, #H, -⟩
  iexact H

instance Pm_timeless (B : BNs) (db : Loc) (q : Qp) : Timeless (Pm (GF := GF) B db q) := by
  have : ∀ ms : MapSt, Timeless (mapFields (GF := GF) db (DFrac.own q.half) ms) := by
    intro ms; rcases ms with _ | ⟨b, l⟩ <;> simp only [mapFields] <;> infer_instance
  unfold Pm; infer_instance

theorem DB.mmap.wp_proof (hU : DB.mmapUnlocked.spec (GF := GF) (hG := hG)) :
    DB.mmap.spec (GF := GF) (hG := hG) := by
  intro K tx r m X w minsz hmin hmL hdp hlf hlr
  wp_start as ⟨Hw, Hdb⟩
  icases wtxW_core K tx r m X $$ Hw with ⟨#Hcore, Hw⟩
  ihave #Hguard := BC.core_mmaplock K $$ Hcore
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
  · unfold BC.core isBoltCoreP
    icases Hcore with ⟨-, -, -, $, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hsync $Hguard] as ⟨Hlocked, >HP⟩
  try wp_auto
  wp_apply hU K tx r m X w minsz hmin hmL hdp hlf hlr $$ [Hw Hdb HP] as %err ⟨HP, Hres⟩
  · iframe
  try wp_auto
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlocked HP]
  · iexact HP
  try wp_auto
  iapply HΦ
  simp only [WX.rebase]
  iexact Hres

end proof

end bbolt
end EtcdGrove
end Perennial
