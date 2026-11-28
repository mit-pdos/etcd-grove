/-
(hraft_robust R3) The spec of `disk.(*Disk).persist` (`disk.go`, `d.mu` held, or `d` not yet shared): `durable.Write` of the image's encoding, with the caller's atomic updates of `durable`'s state.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Inv

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

/-- `d.persist()`: writes `encImg I` to `d`'s file; the caller gives `durable.Write`'s two atomic updates (the
rename, then the sync), knowing that the encoding fits a Go slice. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.spec : Prop :=
  ∀ (g : DiskGen) (d : Loc) (I : DiskImg) (stg : w64) (qc : Qp),
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk -∗
    d.[Disk, go!"file"] ↦□ g.f.name -∗ ⌜g.f.Ok⌝ -∗ Fs.osInv -∗ Fs.osSharedInv g.R -∗ DurFs.durInv g.γd g.f -∗
    diskMem d I stg -∗ DurFs.durHandle g.γd g.f g.R -∗ Fs.osCallPerm (Fs.callKey g.R g.f.d) qc -∗
    (⌜(encImg I).length < 2 ^ 63⌝ -∗
      AU <{ ∃∃ s : DurFs.DurSt, DurFs.durSt (GF := GF) g.γd s }> @ DurFs.durAuMask, ∅
        <{ DurFs.durSt (GF := GF) g.γd ⟨some (encImg I), some s.cur⟩, COMM
          DurFs.durWriteSync (GF := GF) g.γd iprop(DurFs.durHandle g.γd g.f g.R -∗
            Fs.osCallPerm (Fs.callKey g.R g.f.d) qc -∗ diskMem d I stg -∗ Φ #()) }>) -∗
    WP (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"persist")) (Val #())) {{ Φ }}

end sec

end Perennial
