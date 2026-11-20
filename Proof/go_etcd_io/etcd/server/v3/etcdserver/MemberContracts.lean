/-
**The membership operations' names-only callees, as contracts** (auth-mediation M2, 2026-11-20):
`mayAddMember`, `mayPromoteMember` (the strict reconfiguration checks) and `configure` for the
add, update and promote changes, as `AuthGuard.lean`'s `mayRemoveOk`/`configureRemoveOk` for the
removal. `configure` is called only after a passing admin check: its contract takes the token
`adminRes` of the request's auth info. The change carries `json.Marshal`'s bytes (`Context`), of
which nothing is claimed (`Spec/encoding/json/MarshalMember.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- A member's two string slices (`PeerURLs`, `ClientURLs`) under the fractions `dp`, `dc`. -/
def memberSlices (memb : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (dp dc : DFrac) (ps cs : List GoString) : IProp GF :=
  iprop(memb.RaftAttributes'.PeerURLs' ↦*{dp} ps ∗ memb.Attributes'.ClientURLs' ↦*{dc} cs)

/-- **`s.mayAddMember(memb)`** (the strict reconfiguration check) over the caller's `Pm` and the
member's slices (it formats the member when it logs a refusal), answering `Qm`, the slices back. -/
def mayAddOk (s : Loc) (memb : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (dp dc : DFrac) (ps cs : List GoString) (Pm : IProp GF) (Qm : GoInterface → IProp GF) :
    IProp GF :=
  iprop({{ Pm ∗ memberSlices memb dp dc ps cs }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"mayAddMember")) (Val #memb))
    {{ (err : GoInterface), RET #err; Qm err ∗ memberSlices memb dp dc ps cs }})

instance mayAddOk_persistent (s : Loc) (memb : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (dp dc : DFrac) (ps cs : List GoString) (Pm : IProp GF) (Qm : GoInterface → IProp GF) :
    Persistent (mayAddOk s memb dp dc ps cs Pm Qm) := by
  unfold mayAddOk; infer_instance

/-- **`s.mayPromoteMember(id)`** (the learner's readiness and the strict reconfiguration check)
over the caller's `Pm`, answering `Qm`. -/
def mayPromoteOk (s : Loc) (id : w64) (Pm : IProp GF) (Qm : GoInterface → IProp GF) : IProp GF :=
  iprop({{ Pm }} (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"mayPromoteMember"))
    (Val #id)) {{ (err : GoInterface), RET #err; Qm err }})

instance mayPromoteOk_persistent (s : Loc) (id : w64) (Pm : IProp GF)
    (Qm : GoInterface → IProp GF) : Persistent (mayPromoteOk s id Pm Qm) := by
  unfold mayPromoteOk; infer_instance

/-- **`s.configure(ctx, &cc)`** for a change of type `ty` of the node `id` carrying some bytes,
guarded: with the token `adminRes` of the request's auth info, the caller's `Pre` (the strict check's
passing answer, or nothing) and the change (`cc ↦ ccv`, its `Type` pointing at `ty`, its `NodeId` at
`id`, its `Context` some bytes), over the caller's `Pin`, answering `Qin`. -/
def configureCcOk (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (ty : go_etcd_io.raft.v3.raftpb.ConfChangeType) (id : w64) (Pin Pre : IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF) : IProp GF :=
  iprop(∀ (ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo) (cc tp np : Loc) (bsl : GoSlice)
      (b : List w8) (ccv : go_etcd_io.raft.v3.raftpb.ConfChange),
    {{ Pin ∗ E.RD ∗ adminRes E.authMode ai ∗ Pre ∗ cc ↦ ccv ∗
        ⌜ccv.Type' = tp ∧ ccv.NodeId' = np ∧ ccv.Context' = bsl⌝ ∗
        tp ↦ ty ∗ np ↦ id ∗ bsl ↦* b }}
      (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"configure"))
        (Val #(GoInterface.ok ctx))) (Val #cc))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); E.RD ∗ Qin sl err }})

instance configureCcOk_persistent (s : Loc) (E : apply.AEnv GF) (ctx : GoInterfaceOk)
    (ty : go_etcd_io.raft.v3.raftpb.ConfChangeType) (id : w64) (Pin Pre : IProp GF)
    (Qin : GoSlice → GoInterface → IProp GF) :
    Persistent (configureCcOk s E ctx ty id Pin Pre Qin) := by
  unfold configureCcOk; infer_instance

/-- The change type `AddMember` proposes: `ConfChangeAddLearnerNode` (3) for a learner,
`ConfChangeAddNode` (0) otherwise. -/
def addChangeType (learner : Bool) : go_etcd_io.raft.v3.raftpb.ConfChangeType :=
  if learner then W32 3 else W32 0

end defs

end EtcdGrove
end Perennial
