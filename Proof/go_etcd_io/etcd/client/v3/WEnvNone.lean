/-
**A placeholder watch environment** (phase 7 S2's interface, 2026-11-24): `client.WEnv.none`, the watch
environment a client that never watches passes to `etcdstart.NewClient.spec` (whose `V` is the
caller's choice: the in-process examples pick `srvWEnv` of their member's watch server; a client on
a machine of its own has no server's heap to pick it from). Null locations, `default` names, `False`
predicates: nothing is assumed, and `client_Put_own`/`client_Get_own` discard the watcher conjunct.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An apply environment with nothing in it** (null handle, `default` names, `False` predicates). -/
def apply.AEnv.none : apply.AEnv GF where
  kv := GoInterface.nil
  γ := default
  γs := default
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

/-- **The placeholder watch environment** (see the file header). -/
def client.WEnv.none : client.WEnv GF :=
  client.srvWEnv v3rpc.WSrv.none v3rpc.SrvW.none default [] [] null null [] null default

end defs

end EtcdGrove
end Perennial
