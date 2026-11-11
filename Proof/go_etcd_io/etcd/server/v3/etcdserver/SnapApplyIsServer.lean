/-
**The server's view after `applySnapshot`** (D22 receiver epochs, S8d, step 2 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`): `isServer` at the snapshot's names.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Step 2: `isServer` at the snapshot's names** `γ' = snapγ γ π0 d'.γB`, `TM' = metaTM d'.γB P`,
`E' = snapE …` (persistent, from the old view and the walk's `HCI'` and hook). (Strict M1,
2026-11-06: the store restored in place, so its KV invariants are the old ones, `srvAtomics_snapE`
by `rfl`; the new backend at the store's write invariant `mvccW d'.gx`, the batch lock's invariant
the epoch's `E'.Pk`; until then the store's names at the restored physical names and the mode
law.) (The mvcc merge, 2026-11-06: in the server's auth mode `on`, `isServerM`, as `lean`'s P6.2.) -/
theorem snap_isServer (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (π0 : ApplyPhys) (P : backend.BParams)
    (d' : mvcc.KBReal) (g : GoFunc) (al ast lp cl : Loc) (hP : d'.P = P) (hgnn : g ≠ func.nil)
    (hcK : ciKeys d'.P) (hhP : storage.hooksParams d'.P) (hk : Loc) :
    isServerM on s γ ci TM E ρ γr ∗ srvClusterAddr s ↦□ cl ∗
      isServerCI s (snapγ γ π0 d'.γB) ci ∗ hookSpec (snapγ γ π0 d'.γB) ci (metaTM d'.γB P) #g ∗
      -- (2026-11-02, branch `snap-window`) the new backend's hooks, the server's `s.beHooks`
      backend.hooksAt d'.be (storage.hooksIface hk) ∗ structFieldRef EtcdServer go!"beHooks" s ↦□ hk ∗
      backend.isBackend d'.γB d'.P (mvcc.api.mvccW d'.gx)
        (batchLockInv (snapγ γ π0 d'.γB) (metaTM d'.γB P)) d'.be ⊢
    isServerM on s (snapγ γ π0 d'.γB) ci (metaTM d'.γB P)
      (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be) ρ γr := by
  subst hP
  unfold isServerM srvFieldsAtM
  iintro ⟨⟨%Hrd, #Hci, Hv, #Hat, #Hgen, #Hrn, %Hrdb⟩, #Hcl, #Hci', #Hhook, #HhkAt, #HbhF, #HB⟩
  icases Hv with ⟨%v, Hf⟩
  icases Hf with ⟨#Hlg, #Hlgn, #Hw, #Hwi, %HP, %Henv, #Hhk, #Hles, #Hlok, #Hfc, #Hal,
    #Hclv, #Hrc, #Hq, #Hlm, #Hmid, #Hli, #He, #Ht, #Hn, #Has, #Hbeh⟩
  -- (2026-11-02) the new backend with the server's hooks: the old one's hooks are `s.beHooks`
  iunfold srvBeHooked at Hbeh
  icases Hbeh with ⟨%d0, %bh, %lgh, %gx0, -, #HbhF0, #Hbh, -, -⟩
  icombine HbhF HbhF0 gives %Hbh0
  subst Hbh0
  ihave #Hbeh' : srvBeHooked s (snapγ γ π0 d'.γB) ci
      (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB d'.P) ci d' g d'.γB al ast lp cl d'.be) $$ []
  · iunfold srvBeHooked
    iexists d', hk, lgh, d'.gx
    iframe HbhF Hbh HhkAt HB
    ipureintro
    exact ⟨rfl, hcK, hhP, rfl⟩
  icombine Hcl Hclv gives %Heq
  subst Heq
  have hok : srvEnvOk s (snapγ γ π0 d'.γB) ci
      (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB d'.P) ci d' g d'.γB al ast lp v.cluster d'.be) v.cluster :=
    ⟨Henv.1, rfl, d'.γB, _, rfl, rfl, d', al, ast, lp, rfl, rfl, rfl⟩
  rw [srvAtomicsM_snapE, srvGenAt_snapE]
  isplitr
  · ipureintro; exact Hrd
  isplitr
  · iexact Hci'
  isplitr
  · iexists { v with hook := #g }
    simp only
    rw [show waitInvM on v.w ρ (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB d'.P) ci d' g d'.γB al ast lp
      v.cluster d'.be) = waitInvM on v.w ρ E from rfl]
    -- (the lease-expiry plan's X4) `lessorOk` at the environment's flag and auth mode, unchanged
    rw [snapE_lg, snapE_authMode]
    iframe #
    ipureintro
    exact ⟨⟨rfl, rfl, hgnn⟩, hok⟩
  iframe #
  ipureintro; exact Hrdb

end proof
end EtcdGrove
end Perennial
