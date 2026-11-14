/- Lean-first (no Rocq counterpart).

# `ReadAll`'s tail registration, not yet zeroed (I3b, `wal-tc17`; W3/W5's `walInvRegisterTailLaw`
restated)

`walInvRegisterTailLaw` (formerly `ReadAllReg.lean`'s, removed once `ReadAll` switched, 2026-11-14) handed out the key
and `TailMeta` of the tail it registered, which a crash's tail does not have (F-Z, `TailZ`, `PastZ`).
**`walInvRegisterPendLaw`** (a hypothesis of `WAL.ReadAll.wp_proof`) is its restatement over the pending registration
(`walTailsRes_registerPend`): the pending token `walPendTok dir γ |lay.old|` in place of the key,
`TailMetaR` in place of `TailMeta`, and `TailZ0 lay ∧ |lay.old| = gl.om.size` added
(`walAbsD_old_exact`). Its proof (the look of `walInvBody_readState` with the registration inside)
is blocked on two facts the invariant does not keep of an unregistered tail (W1 log, twenty-seventh
session, findings C and D): its last segment unmapped (`gl.om.maps = ∅`, for `TailMetaR`) and its
record boundary (`TailBound`, `walTailsRes`'s per-tail fact, which `walTailsRes_registerPend` needs).
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

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **The look at the invariant before `ReadAll`'s loop, registering the tail, not yet zeroed** (see
the file header). -/
def walInvRegisterPendLaw (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : Prop :=
  ∀ (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH) (gs : List SegG) (gl : SegG),
    (∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino)) →
    (∃ kk, (walNames hj0.cur).drop kk = gs.map (·.name)) →
    (∀ g ∈ gs, g.om.size = g.bs.length) → gs.getLast? = some gl →
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walDirKey (W := W) dir j X -∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) ∅ -∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ∗
      ∃ (d : WalDur) (lay : WalLay) (kk : Nat) (γ : GName),
        walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗
        walPendTok (W := W) dir γ lay.old.length ∗
        (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay gl.ino none)) ∗
        ⌜lay.j = j ∧ WalAbsD C Mr d lay hj0.cur ∧ TailExact lay ∧
          lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ lay.segs.drop kk = gs ∧
          TailMetaR gl.om gl.bs ∧ TailZ0 lay ∧ lay.old.length = gl.om.size⌝

end iris

end WalFs
end EtcdGrove
end Perennial

end
