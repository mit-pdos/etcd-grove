/-
(hraft_robust R3) The spec of `disk.(*Snaps).persist` (`snap.go`, `s.mu` held, or `s` not yet shared): `durable.Write` of the image's encoding, with the caller's atomic updates of `durable`'s state.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SnapInv

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

/-- `s.persist()`: writes `encSnap S` to `s`'s file; the caller gives `durable.Write`'s two atomic updates (the
rename, then the sync), knowing that the encoding fits a Go slice; `s`'s fields as they were. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.persist.spec : Prop :=
  ∀ (g : SnapGen) (s : Loc) (S : SnapImg) (has : Bool) (mv : SnapshotMeta) (dt : GoSlice) (qc : Qp),
  ⊢ ∀ Φ : val → IProp GF,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk -∗
    s.[Snaps, go!"file"] ↦□ g.f.name -∗ ⌜g.f.Ok⌝ -∗ Fs.osInv -∗ Fs.osSharedInv g.R -∗ DurFs.durInv g.γd g.f -∗
    snapsMemAt s S has mv dt -∗ DurFs.durHandle g.γd g.f g.R -∗ Fs.osCallPerm (Fs.callKey g.R g.f.d) qc -∗
    (⌜(encSnap S).length < 2 ^ 63⌝ -∗
      AU <{ ∃∃ st : DurFs.DurSt, DurFs.durSt (GF := GF) g.γd st }> @ DurFs.durAuMask, ∅
        <{ DurFs.durSt (GF := GF) g.γd ⟨some (encSnap S), some st.cur⟩, COMM
          DurFs.durWriteSync (GF := GF) g.γd iprop(DurFs.durHandle g.γd g.f g.R -∗
            Fs.osCallPerm (Fs.callKey g.R g.f.d) qc -∗ snapsMemAt s S has mv dt -∗ Φ #()) }>) -∗
    WP (App (Val (s @!! go.GoType.PointerType Snaps.ty @!! go!"persist")) (Val #())) {{ Φ }}

end sec

end Perennial
