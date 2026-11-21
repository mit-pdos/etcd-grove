/-
**An error's message** (`v3rpc.errMsgP err P`: `err.Error()` returns a message with `P`). Moved down
from `api/v3rpc/InvKV.lean` (auth-mediation M2, 2026-11-20), name unchanged, so that the server
package's membership contracts (`MemberContracts.lean`) can state it: `PromoteMember` labels a metric
with an error's message, which must be valid UTF-8. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`err.Error()` returns a message with `P`** (persistent; k8s etcd3 7c-2): what a caller of
`togRPCError` knows of the message its default case makes a description of
(`status.Error(codes.Unknown, err.Error())`). `srvErrIs` gives it at `P := fun _ => True`
(`errMsgP_of_srvErrIs`). -/
def errMsgP (err : GoInterface) (P : GoString → Prop) : IProp GF :=
  iprop(∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei⌝ ∗
    {{ True }} (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
    {{ (msg : GoString), RET #msg; ⌜P msg⌝ }})

instance errMsgP_persistent (err : GoInterface) (P : GoString → Prop) :
    Persistent (errMsgP (GF := GF) err P) := by
  unfold errMsgP; infer_instance

end defs

end v3rpc
end EtcdGrove
end Perennial
