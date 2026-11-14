/- Lean-first (no Rocq counterpart).

# Laws of the sealed handle (W6; the package's own proofs `import all` `Handle.lean`)

- `walOpenWF_iff`: the client handle is a quiescent internal handle with its cuts budget.
- `walHandleIn_lenLb`: a length lower bound of the open WAL is at most the handle's history
  (`walLenLb_tail_le` over the tail record the handle holds in `walTailW`); `Sync` needs it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailLenLb
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The client handle unsealed.** -/
theorem walOpenWF_iff (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    walOpenWF (W := W) P Mr w dir ⊣⊢ ∃ h : WalHS, walHandleIn (W := W) P Mr w dir h ∗ ⌜h.Done⌝ ∗ ⧗ h.pc :=
  .rfl

/-- **A length lower bound is at most the handle's history** (at an update; see the file header). -/
theorem walHandleIn_lenLb (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (P : WalPbIn GF) (E : CoPset) (hE : ↑walN ⊆ E) (w : Loc) (dir : GoString) (h : WalHS) (n : Nat) :
    ⊢ walAreaOk C Mr R jr r -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walHandleIn (W := W) P Mr w dir h -∗ walLenLb (W := W) w dir n -∗
      |={E}=> notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walHandleIn (W := W) P Mr w dir h ∗
        ⌜n ≤ h.H.length⌝ := by
  letI := walAllG (W := W)
  iintro #Harea Hnc Hh #Hn
  unfold walAreaOk
  icases Harea with ⟨#Hinv, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Ht, Hrest⟩
  unfold walTailW
  icases Ht with ⟨Hf, Hfd, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  imod walLenLb_tail_le C Mr R jr r E hE w dir h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) n $$ Hinv Hnc Hk [Hv] Hn
    with ⟨Hnc, Hk, Hv, %hn⟩
  · unfold tailVar; iexact Hv
  unfold tailVar
  imodintro
  iframe Hnc
  isplitl
  · iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hrest
    iframe Hf Hfd Hoff Hk
    iexists m, bs
    iframe Hm Hb Hv
    ipureintro; exact hp
  · ipureintro; exact hn

end handle

end WalFs
end EtcdGrove
end Perennial
