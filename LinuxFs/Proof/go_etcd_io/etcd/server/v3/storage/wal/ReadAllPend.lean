/- Lean-first (no Rocq counterpart).

# The read tail as a pending handle tail (W3/W5 of `notes/wal-fsext-plan.md`, twenty-fifth session)

`walTailP_ofRead`: `walTailW_ofRead` over the pending registration (`walInvRegisterPendLaw`): the
decoder's stream state of the last file, the pending token `walPendTok dir γ k` and the tail record give
`walTailP … lay.wr g.om.size [] k true tm`, `tm` what `ZeroToEnd.specWalTail` takes: `TailMetaR` and the
zero length word at the write position (`readAll_tailZeroWord`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllReg
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandlePend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics] [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The read tail as the handle's pending tail** (see the file header). -/
theorem walTailP_ofRead (f : Loc) (fd : w64) (name dir : GoString) (γ : GName) (g : SegG) (d : WalDur)
    (lay : WalLay) (k : Nat) (hfd : 0 ≤ fd.toInt) (hm : TailMetaR g.om g.bs)
    (hz : ∀ j, j < 8 → (g.bs.getD (lay.wr + j) (0, [])).1 = 0) (hsz : g.om.size ≤ 0xffffffff000) :
    os.ownFile f fd name (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (openFd g.ino (walReadFlag true)) ∗
      os.ownOff f (W64 (lay.wr : Int)) ∗ walPendTok (W := W) dir γ k ∗
      osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs ∗
      (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay g.ino none)) ⊢
    walTailP (W := W) f fd name dir γ g.ino d.H d.metadata lay.cuts lay.wr g.om.size [] k true
      (fun m bs => TailMetaR m bs ∧ ∀ j, j < 8 → (bs.getD (lay.wr + j) (0, [])).1 = 0) := by
  iintro ⟨Hf, Hfd, Ho, Hk, Hm, Hb, Hv⟩
  unfold walTailP
  rw [openFd_write]
  rw [show ((lay.wr : Int) + (([] : List w8).length : Int)) = (lay.wr : Int) by simp]
  iframe Hf Ho Hk
  isplitl [Hfd]
  · iexists true; iexact Hfd
  iexists g.om, g.bs
  iframe Hm Hb
  isplitr
  · ipureintro; exact ⟨rfl, ⟨hm, hz⟩, by omega, hfd, by simpa using hm.loWr lay.wr⟩
  · unfold tailG; iexact Hv

end handle

end WalFs
end EtcdGrove
end Perennial

end
