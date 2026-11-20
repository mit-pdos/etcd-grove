/-
`WalHS.split_rest0`, `tailOk_rest0` and `WalHS.split_flush`, out of `WAL__sync.lean`'s proofs so that the
sync variants (`WAL__syncNoErr`, `WAL__CloseU`) import them without the proofs (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutTail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenWLocked
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeG
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__flush
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriterW
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailFdatasync
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Duration
public import Spec.time.Duration__Seconds_ptr
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

/-- **A handle with every record encoded**: its writer's and page writer's bytes are the tail's
stream past `o0`. -/
theorem WalHS.split_rest0 [GooseExts] {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr)
    (hr : h.rest = 0) :
    h.out ++ h.pend = (tailStream Mr h.H h.md h.cuts).drop h.o0 ∧
      h.o0 + (h.out ++ h.pend).length = (tailStream Mr h.H h.md h.cuts).length := by
  obtain ⟨h1, h2, -⟩ := hs
  have he : h.encRecs Mr = tailRecs Mr h.H h.md h.cuts := by
    unfold WalHS.encRecs; rw [hr, Nat.sub_zero, List.take_length]
  rw [he, ← tailStream_recs] at h1 h2
  have hl : ((tailStream Mr h.H h.md h.cuts).take h.o0).length = h.o0 := by
    rw [List.length_take]; omega
  constructor
  · conv => rhs; rw [← h1]
    rw [List.append_assoc, List.drop_left' hl]
  · have := congrArg List.length h1
    simp only [List.length_append] at this ⊢
    omega

/-- The tail's guard holds of everything the encoder has accepted, inside the size. -/
theorem tailOk_rest0 [GooseExts] {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr)
    (hr : h.rest = 0) (hsz : h.o0 + h.out.length + h.pend.length ≤ h.sz) :
    tailOk Mr h.H h.md h.cuts h.o0 h.sz (h.out ++ h.pend) := by
  refine ⟨?_, ?_⟩
  · rw [(WalHS.split_rest0 hs hr).1]; exact List.prefix_refl _
  · simp only [List.length_append]; omega

/-- The split after a flush. -/
theorem WalHS.split_flush [GooseExts] {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr) :
    WalHS.Split Mr { h with out := h.out ++ h.pend, pend := [] } := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨?_, h2, h3⟩
  have he : WalHS.encRecs Mr { h with out := h.out ++ h.pend, pend := [] } = h.encRecs Mr := rfl
  simp only [he, List.append_nil, List.append_assoc] at h1 ⊢
  exact h1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]


end proof

end EtcdGrove
end Perennial
