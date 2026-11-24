/-
**A placeholder watch environment** (phase 7 S2's interface, 2026-11-24): `client.WEnv.none`, the watch
environment a client that never watches passes to `etcdstart.NewClient.spec` (whose `V` is the
caller's choice: the in-process examples pick `srvWEnv` of their member's watch server; a client on
a machine of its own has no server's heap to pick it from). Null locations, `default` names, `False`
predicates (its model `EtcdModel.none`: every predicate `False`, so every law holds vacuously):
nothing is assumed, and `client_Put_own`/`client_Get_own` discard the watcher conjunct.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An apply environment with nothing in it** (null handle, `default` names, `False` predicates). -/
def apply.AEnv.none : apply.AEnv GF where
  kv := GoInterface.nil
  γ := default
  γs := ⟨default, default, default, default⟩
  Nx := fun _ => iprop(False)
  Pk := fun _ => iprop(False)
  f := func.nil
  RD := iprop(False)
  γrev := default
  authMode := .off
  FS := iprop(False)
  ciC := fun _ _ => False
  RO := fun _ => iprop(False)
  RW := iprop(False)
  γbe := default
  Cp := fun _ => iprop(False)
  BkTie := fun _ => iprop(False)

/-- **A watch server with nothing in it.** -/
def v3rpc.WSrv.none : v3rpc.WSrv GF := ⟨null, apply.AEnv.none, null, default, W64 0, W64 0, null, W64 0⟩

/-- **Watch facts with nothing in them.** -/
def v3rpc.SrvW.none : v3rpc.SrvW GF :=
  ⟨GoInterface.nil, default, nroot, fun _ => iprop(False), fun _ => iprop(False)⟩

/-- **A model of etcd with every predicate `False`** (its laws hold vacuously). -/
def EtcdModel.none : EtcdModel GF where
  etcdState := fun _ _ _ => iprop(False)
  etcdState_agree := by intros; iintro ⟨H, -⟩; iexfalso; iexact H
  etcdState_revs := by intros; iintro H; iexfalso; iexact H
  etcdState_keys := by intros; iintro H; iexfalso; iexact H
  etcdState_vals := by intros; iintro H; iexfalso; iexact H
  etcdState_create_persist := by intros; iintro ⟨H, -⟩; iexfalso; iexact H
  etcdState_modrev_det := by intros; iintro ⟨H, -⟩; iexfalso; iexact H
  etcdState_modrev_persist := by intros; iintro ⟨H, -⟩; iexfalso; iexact H
  etcdReachedAt := fun _ => iprop(False)
  etcdReachedAt_timeless := fun _ => inferInstance
  etcdReadAt := fun _ => iprop(False)
  etcdReadAt_persistent := fun _ => inferInstance
  etcdReadAt_timeless := fun _ => inferInstance
  etcdRevToken := fun _ => iprop(False)
  etcdRevToken_excl := by intros; iintro ⟨H, -⟩; iexact H
  EtcdStep := fun _ _ _ _ => iprop(False)
  EtcdStep_persistent := fun _ _ _ _ => inferInstance
  EtcdStep_timeless := fun _ _ _ _ => inferInstance
  etcdStep_transfer := by intros; iintro ⟨H, -⟩; iexfalso; iexact H
  etcdStep_compose := by intros; iintro ⟨H, -⟩; iexfalso; iexact H
  etcdStep_restrict := by intros; iintro H; iexfalso; iexact H
  etcdStep_delete_present := by intros; iintro ⟨H, -⟩; iexfalso; iexact H

/-- **The placeholder watch environment** (see the file header). -/
def client.WEnv.none : client.WEnv GF :=
  ⟨v3rpc.WSrv.none, [], [], null, null, [], null, EtcdModel.none, fun _ => iprop(False),
    fun _ => ([], v3rpc.WSrv.none), 0, default, v3rpc.SrvW.none, fun _ => v3rpc.SrvW.none⟩

end defs

end EtcdGrove
end Perennial
