/-
`ReleaseLockTo`'s update (W9 of `notes/wal-fsext-plan.md`): at a ghost step, `walInv` opened, the
client's update committed with the WAL's `unl` mark raised (`walInvBody_unl`; the mark is bookkeeping,
plan §6 Q1). Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtPin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **An update raising the `unl` mark of the WAL in `dir`**, committed at a ghost step: the mark
raised to `p d`, `d` the client's state (any premise `Pre d` of the client's). -/
theorem walInv_unlAU (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (p : WalDur → Nat) (Pre : WalDur → Prop) (Q : WalDur → IProp GF) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      (AU <{ ∃∃ d : WalDur, walDiskAt (W := W) dir d ∗ ⌜Pre d⌝ }> @ walAuMask, ∅
        <{ walDiskAt (W := W) dir { d with unl := max d.unl (p d) }, COMM Q d }>) ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ ∃ d, Q d := by
  iintro #Hinv Hnc Hau
  imod walInv_open C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  ihave Hau := atomic_update_mask_weaken walAuMask_sub_top' $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%dc, ⟨Ho, %hpre⟩, Hucl⟩
  unfold walDiskAt walDirIs
  icases Ho with ⟨%M, HM, %HMd⟩
  icases walInvBody_mapLe C Mr R jr r s M $$ Hb HM with ⟨%HMs, Hb, HM⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
  obtain ⟨ds, hsd, hle⟩ : ∃ ds, s.wal !! dir = some ds ∧ walDurLe dc ds := by
    have h1 := HMs dir
    rw [hM0] at h1
    obtain ⟨ds, hds, hle1⟩ := (walOptLe_some_iff _ _).1 h1
    exact ⟨ds, hds, walDurLe_trans hle0 hle1⟩
  imod walInvBody_unl C Mr R jr r s dir (p dc) M $$ Hb HM with ⟨-, Hb, HM, -⟩
  have hsd' := unlSt_lookup_self s dir (p dc) ds hsd
  imod Hcommit $$ [HM] with HQ
  · iexists (unlSt s dir (p dc)).wal
    iframe HM
    ipureintro
    simp only [hsd', walOptLe]
    exact walDurLe_unl _ hle
  imod Hcl $$ [Hb] with -
  · iexists _; iexact Hb
  imodintro
  iframe Hnc
  iexists dc
  iexact HQ

end iris

end WalFs
end EtcdGrove
end Perennial
