/-
**What the server keeps of its uber-applier's base auth layer** (the auth plan's E3k,
2026-10-27). Lean-first (no Rocq counterpart).

`newApplierV3`'s applier is an auth applier over the quota applier over the backend; its auth
layer's structure and its store and lessor fields (`baseAuth`, `InvUber.lean`) are part of the
uber-applier's persistent description (`uberIs`). `uberBaseAuth ua E au le`: the `UberApplier`
`ua` whose base applier's store is `au` and lessor `le`, what the server keeps (`srvUberBase`)
for the apply thread's KV triples at the latest state (`uberKVL_of_base`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `UberApplier` `ua` whose base applier's store is `au` and lessor `le`** (persistent). -/
def apply.uberBaseAuth (ua : GoInterface) (E : apply.AEnv GF) (au le : GoInterface) : IProp GF :=
  iprop(∃ (p : Loc) (opts : ApplierOptions),
    ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p ∧ opts.AuthStore' = au ∧
      opts.Lessor' = le⌝ ∗ apply.uberIs E p opts)

instance apply.uberBaseAuth_persistent (ua : GoInterface) (E : apply.AEnv GF) (au le : GoInterface) :
    Persistent (apply.uberBaseAuth ua E au le) := by
  unfold apply.uberBaseAuth; infer_instance

end defs

end EtcdGrove
end Perennial
