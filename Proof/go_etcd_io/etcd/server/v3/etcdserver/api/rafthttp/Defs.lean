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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The transport `tr`, read with `Rd`** (a `rafthttp.Transporter`, not nil; the request path's
contract of `s.r.transport`): `tr.ActiveSince(id)` returns some time (the zero time if `id` is not
connected), and (rdslot, 2026-11-22) `tr.ActivePeers()` some count, each from any goroutine that
holds `Rd`, which it gives back. rafthttp's transport gives it with `Rd` one of its lock's reader
tokens (`trState_net_gen`: both methods read-lock the peer table). (Until rdslot, `{{ True }}`, and
`ActiveSince` alone: an axiom that read-locked without a reader token.) -/
def rafthttp.isTransporter (tr : GoInterface) (Rd : IProp GF) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ id : w64,
      {{ Rd }} (App (Val #(methods ti.ty go!"ActiveSince" ti.v)) (Val #id))
      {{ (t : _root_.Perennial.time.Time), RET #t; Rd }}) ∗
    □ ({{ Rd }} (App (Val #(methods ti.ty go!"ActivePeers" ti.v)) (Val #()))
      {{ (n : w64), RET #n; Rd }}))

instance rafthttp.isTransporter_persistent (tr : GoInterface) (Rd : IProp GF) :
    Persistent (rafthttp.isTransporter (GF := GF) tr Rd) := by
  unfold rafthttp.isTransporter; infer_instance

end defs

end EtcdGrove
end Perennial
