/- Lean-first (no Rocq counterpart).

# The handle with room before `maxBytes` (unit `noioerr`, `notes/wal-units/noioerr.md`)

`walOpenWFR P Mr w dir k` (sealed): `walOpenWF` whose tail's stream, written and pending
(`o0 + |out| + |pend|`), ends at least `k` bytes before `maxBytes` (ext4's `s_maxbytes`, `fsExt`'s file size
bound). The no-error specs (`Close.specNoErr`, `SaveSnapshot.specNoErr`) take it: a write that reaches
`maxBytes` fails with `EFBIG` whether or not `NoIoErr` holds (no write can succeed there), so an error-free
flush needs the stream to end before it. How a client comes by it (a law from `Create`'s post, the fresh
tail's headers being far below `maxBytes`; from `Save`'s cut; or a public measure of the tail) is open:
`notes/wal-units/noioerr.md`, second session, "Decisions left for the user". `walOpenWFR_wf`: it is a
`walOpenWF`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws

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

/-- See the file header. -/
@[no_expose] def walOpenWFR (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (k : Nat) :
    IProp GF :=
  iprop(∃ h : WalHS, walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⌜h.Done⌝ ∗ ⌜h.md.length < 2 ^ 41⌝ ∗
    ⧗ h.pc ∗ ⌜h.o0 + h.out.length + h.pend.length + k ≤ maxBytes⌝)

/-- The room handle unfolded (for the package's proofs). -/
theorem walOpenWFR_iff (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (k : Nat) :
    walOpenWFR (W := W) P Mr w dir k ⊣⊢
      ∃ h : WalHS, walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⌜h.Done⌝ ∗ ⌜h.md.length < 2 ^ 41⌝ ∗
        ⧗ h.pc ∗ ⌜h.o0 + h.out.length + h.pend.length + k ≤ maxBytes⌝ :=
  .rfl

/-- **A handle with room is a handle.** -/
theorem walOpenWFR_wf (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (k : Nat) :
    walOpenWFR (W := W) P Mr w dir k ⊢ walOpenWF P Mr w dir := by
  refine (walOpenWFR_iff P Mr w dir k).1.trans ?_
  refine BI.Entails.trans ?_ (walOpenWF_iff P Mr w dir).2
  iintro ⟨%h, Hh, %hD, %hmd, Hr, -⟩
  iexists h
  iframe Hh Hr
  ipureintro; exact ⟨hD, hmd⟩

end handle

end WalFs
end EtcdGrove
end Perennial

end
