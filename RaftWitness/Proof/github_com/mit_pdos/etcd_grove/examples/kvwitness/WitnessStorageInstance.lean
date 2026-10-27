/-
Lean-first (no Rocq counterpart). (2026-10-20, witness support)

**The store's witness storage meets raft's storage contract** (`isWitnessStorage`,
`Proof/go_etcd_io/raft/v3/InvWitnessStorage.lean`), for any ghost counterpart `P` of its state
and any namespace `N`: the contract is not a trust boundary for the store. A read
(`GetWitnessState`) runs the caller's shift under the lock and hands out a read of the stored
state (`isWRead`), whose `GetState` and `Update` are the contract's `isWState`; `Close` does
nothing.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.WitnessStore__GetWitnessState
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.WitnessStore__Close
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.witnessRead__GetState
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.witnessRead__Update

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section inst
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- The store's witness storage at `s`, as a raft `WitnessStorage` interface value. -/
def kvWStoreIface (s : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType rWStoreTy) #s

/-- A read of the store is the contract's `WitnessState` of the state it saw. -/
theorem wRead_isWState
    (wp_GetState : kvwitness.witnessRead.GetState.spec (GF := GF) (hG := hG))
    (wp_Update : kvwitness.witnessRead.Update.spec (GF := GF) (hG := hG))
    (r s : Loc) (N : Namespace) (P : WHS → IProp GF) (p : Loc) (σ : WHS) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness -∗
      isWRead r s P p σ -∗
      isWState (interface.mkOk (go.GoType.PointerType rWReadTy) #r) N P σ := by
  iintro #Hpkg #Hr
  ihave #Hr' := Hr
  iunfold isWRead at Hr'
  icases Hr' with ⟨-, -, #Hp, -⟩
  unfold isWState
  iexists (⟨go.GoType.PointerType rWReadTy, #r⟩ : GoInterfaceOk), p
  isplitr
  · ipureintro; rfl
  isplitr
  · unfold whsOpt; iright; iexact Hp
  isplitr
  · imodintro
    iintro %Φ
    imodintro
    iintro - HΦ
    wp_apply wp_GetState r s P p σ $$ [$Hpkg $Hr]
    iapply HΦ; itrivial
  imodintro
  iintro %q %σ' %Ψ %Φ
  imodintro
  iintro ⟨#Hq, Hsh⟩ HΦ
  wp_apply wp_Update r s P p σ N q σ' Ψ $$ [$Hpkg $Hr $Hq $Hsh] as %err Hres
  iapply HΦ $$ Hres

/-- **The store's witness storage is a raft `WitnessStorage`**, at any `P` and `N`. -/
theorem kvWStore_isWitnessStorage
    (wp_GetWitnessState : kvwitness.WitnessStore.GetWitnessState.spec (GF := GF) (hG := hG))
    (wp_Close : kvwitness.WitnessStore.Close.spec (GF := GF) (hG := hG))
    (wp_GetState : kvwitness.witnessRead.GetState.spec (GF := GF) (hG := hG))
    (wp_Update : kvwitness.witnessRead.Update.spec (GF := GF) (hG := hG))
    (s : Loc) (N : Namespace) (P : WHS → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness -∗
      isWStore s P -∗ isWitnessStorage (kvWStoreIface s) N P := by
  iintro #Hpkg #Hw
  unfold isWitnessStorage kvWStoreIface
  iexists (⟨go.GoType.PointerType rWStoreTy, #s⟩ : GoInterfaceOk)
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %Ψ %Φ
    imodintro
    iintro Hsh HΦ
    wp_apply wp_GetWitnessState s P N Ψ $$ [$Hpkg $Hw $Hsh]
      as %sv %err ⟨%Herr, %r, %p, %σ, %Hsv, #Hr, HΨ⟩
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Herr
    iexists σ
    iframe HΨ
    subst Hsv
    iapply wRead_isWState wp_GetState wp_Update r s N P p σ $$ Hpkg Hr
  imodintro
  iintro %Φ
  imodintro
  iintro - HΦ
  wp_apply wp_Close s $$ [$Hpkg]
  iapply HΦ; itrivial

end inst

end EtcdGrove
end Perennial
