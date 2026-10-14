/-
The rafthttp transport as the request path sees it (unit P1b, 2026-10-14). Lean-first (no Rocq
counterpart). `rafthttp` is names-only: `isTransporter tr` is a contract (a premise the server's
fields carry for `s.r.transport`), not a proof of rafthttp.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The transport `tr`** (a `rafthttp.Transporter`, not nil; trust boundary: rafthttp is
names-only), as `isConnectedSince` uses it: `tr.ActiveSince(id)`, from any goroutine, returns
some time (the zero time if `id` is not connected; rafthttp's `ActiveSince` reads its peer
table under a lock). -/
def rafthttp.isTransporter (tr : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ id : w64,
      {{ True }} (App (Val #(methods ti.ty go!"ActiveSince" ti.v)) (Val #id))
      {{ (t : _root_.Perennial.time.Time), RET #t; True }}))

instance rafthttp.isTransporter_persistent (tr : GoInterface) :
    Persistent (rafthttp.isTransporter (GF := GF) tr) := by
  unfold rafthttp.isTransporter; infer_instance

end defs

end EtcdGrove
end Perennial
