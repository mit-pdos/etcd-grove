/-
**The names after `applySnapshot`** (D22 receiver epochs, S8d, 2026-10-26; step 1 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`, "S8d, where it stopped"): the protocol's
names `γ'` at the snapshot's backend, its batch lock's meta resource `TM'`, the apply thread's state
`st'` after `ci.SetBackend`'s load, and the environment `E'` on the new backend, with the facts the
post's assembly and its step lemmas (`SnapApply{IsServer,Opts,KV,Rest,Closer}.lean`) read off them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-- **The protocol's names at the snapshot's backend** `γB` (`snapWalkPost`'s
`γ.withPh (futPhys π0 γB)`). -/
abbrev snapγ (γ : ApplyNames) (π0 : ApplyPhys) (γB : backend.BNames) : ApplyNames :=
  γ.withPh (futPhys π0 γB)

/-- **The apply thread's state after the swap** (`snapWalkPost`'s `applyThread`): loaded at the
snapshot's index `i`, everything through `i` processed, nothing in flight. -/
abbrev snapSt (γ' : ApplyNames) (i : w64) : ApplyState :=
  stLoaded γ' { k := W64 0, p := i, eff := i, pending := false }

theorem snapSt_k (γ : ApplyNames) (π0 : ApplyPhys) (γB : backend.BNames) (i t : w64)
    (hm : π0.m0 = (i, t)) : (snapSt (snapγ γ π0 γB) i).k = i := by
  have h0 : (snapγ γ π0 γB).m0 = π0.m0 := rfl
  unfold snapSt stLoaded; simp only [↓reduceIte, h0, hm]

theorem snapSt_pending (γ' : ApplyNames) (i : w64) : (snapSt γ' i).pending = false := by
  unfold snapSt stLoaded; split <;> rfl

/-- The consistent index after the swap is the snapshot's (`srvSnapApplied`'s `ciEff`). -/
theorem snapSt_ciEff (γ : ApplyNames) (π0 : ApplyPhys) (γB : backend.BNames) (i t : w64)
    (hm : π0.m0 = (i, t)) : ciEff (snapγ γ π0 γB) (snapSt (snapγ γ π0 γB) i).k = i := by
  have h0 : (snapγ γ π0 γB).m0 = π0.m0 := rfl
  rw [snapSt_k γ π0 γB i t hm]; unfold ciEff; split
  · rename_i h; subst h; rw [h0, hm]
  · rfl

/-- `srvSnapApplied`'s `loopOk` at the snapshot's index. -/
theorem snapSt_loopOk (γ : ApplyNames) (π0 : ApplyPhys) (γB : backend.BNames) (i t : w64)
    (hm : π0.m0 = (i, t)) : loopOk (snapγ γ π0 γB) (snapSt (snapγ γ π0 γB) i) i := by
  refine ⟨snapSt_pending _ i, ?_⟩
  rw [snapSt_ciEff γ π0 γB i t hm]
  have : (snapSt (snapγ γ π0 γB) i).p = i := by unfold snapSt stLoaded; split <;> rfl
  rw [this]; omega

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply environment on the snapshot's backend** (`AEnv.onBe`): the store's names at the
restored physical names `p'`, the batch lock's invariant at the new names `γ'` with the meta
resource `TM'`, the new post-lock hook `g`, the consistent index's resources at `γ'`, and the rest
buckets' resource and write right of the new backend `γB` with the server's objects on its real
backend `be` (`srvObjsOn`). -/
def snapE (E : apply.AEnv GF) (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (ci : Loc)
    (p' : mvcc.PhysNames) (g : GoFunc) (γB : backend.BNames) (al ast lp cl be : Loc) :
    apply.AEnv GF :=
  E.onBe p' (batchLockInv γ' TM') #g (srvCiC γ' ci)
    (srvRestOwnH γB cl (srvObjsOn al ast lp cl be)) (srvRestRWH γB (srvObjsOn al ast lp cl be))

section snapE
variable (E : apply.AEnv GF) (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (ci : Loc)
  (p' : mvcc.PhysNames) (g : GoFunc) (γB : backend.BNames) (al ast lp cl be : Loc)

@[simp] theorem snapE_s : (snapE E γ' TM' ci p' g γB al ast lp cl be).s = E.s := rfl
@[simp] theorem snapE_γ : (snapE E γ' TM' ci p' g γB al ast lp cl be).γ = E.γ.withPhys p' := rfl
@[simp] theorem snapE_P :
    (snapE E γ' TM' ci p' g γB al ast lp cl be).P = batchLockInv γ' TM' := rfl
@[simp] theorem snapE_f : (snapE E γ' TM' ci p' g γB al ast lp cl be).f = #g := rfl
@[simp] theorem snapE_RD : (snapE E γ' TM' ci p' g γB al ast lp cl be).RD = E.RD := rfl
@[simp] theorem snapE_γrev : (snapE E γ' TM' ci p' g γB al ast lp cl be).γrev = E.γrev := rfl
@[simp] theorem snapE_authMode :
    (snapE E γ' TM' ci p' g γB al ast lp cl be).authMode = E.authMode := rfl
@[simp] theorem snapE_authOn :
    (snapE E γ' TM' ci p' g γB al ast lp cl be).authOn = E.authOn := rfl
@[simp] theorem snapE_FS : (snapE E γ' TM' ci p' g γB al ast lp cl be).FS = E.FS := rfl
@[simp] theorem snapE_ciC : (snapE E γ' TM' ci p' g γB al ast lp cl be).ciC = srvCiC γ' ci := rfl
@[simp] theorem snapE_RO : (snapE E γ' TM' ci p' g γB al ast lp cl be).RO =
    srvRestOwnH γB cl (srvObjsOn al ast lp cl be) := rfl
@[simp] theorem snapE_RW : (snapE E γ' TM' ci p' g γB al ast lp cl be).RW =
    srvRestRWH γB (srvObjsOn al ast lp cl be) := rfl
@[simp] theorem snapE_γbe : (snapE E γ' TM' ci p' g γB al ast lp cl be).γbe = E.γbe := rfl

/-- The store's names on the new backend are its real backend's (`p'.kb`, `snapWalkPost`'s). -/
theorem snapE_kb (d' : mvcc.KBReal) (h : p'.kb = some d') :
    (snapE E γ' TM' ci p' g γB al ast lp cl be).γ.kb = some d' := h

/-- **The step `applySnapshot` makes** is a `beSucc` (`srvSnapApplied`'s). -/
theorem snapE_beSucc (γ : ApplyNames) (π0 : ApplyPhys) :
    beSucc γ E (snapγ γ π0 γB) (snapE E (snapγ γ π0 γB) TM' ci p' g γB al ast lp cl be) :=
  ⟨rfl, p', _, _, _, _, _, rfl⟩

/-! What the server's view reads of the environment is its logical names', kept (`isServer`'s
parts; step 2). -/

theorem waitInv_snapE (w : GoInterface) (ρ : ReqNames) :
    waitInv w ρ (snapE E γ' TM' ci p' g γB al ast lp cl be) = waitInv w ρ E := rfl

theorem srvAtomics_snapE (s : Loc) (γr : ReadNames) :
    srvAtomics s (snapE E γ' TM' ci p' g γB al ast lp cl be) γr = srvAtomics s E γr := rfl

theorem srvGenAt_snapE (s : Loc) (ρ : ReqNames) :
    srvGenAt s (snapE E γ' TM' ci p' g γB al ast lp cl be) ρ = srvGenAt s E ρ := rfl

/-- The revisions' authority is of the logical names (step 4). -/
theorem revAuth_snapE (log : mvcc.Log) :
    revAuth (snapE E γ' TM' ci p' g γB al ast lp cl be) log = revAuth E log := rfl

/-- The store's readers are of the logical names (step 4). -/
theorem storeReader_snapE :
    mvcc.storeReader (GF := GF) (snapE E γ' TM' ci p' g γB al ast lp cl be).s
      (snapE E γ' TM' ci p' g γB al ast lp cl be).γ = mvcc.storeReader E.s E.γ := rfl

/-- The write budget is of `γbe` (step 7). -/
theorem srvWTPool_snapE (γp : GName) :
    srvWTPool (snapE E γ' TM' ci p' g γB al ast lp cl be) γp = srvWTPool E γp := rfl

end snapE

end defs

end EtcdGrove
end Perennial
