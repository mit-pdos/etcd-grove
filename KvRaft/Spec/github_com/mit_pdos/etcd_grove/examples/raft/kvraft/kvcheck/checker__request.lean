/-
`c.request(id, kind, payload)` (kvcheck.go): `kvraft.Request` to the replica `id`'s address over
kvraft's wire protocol (`isCheckerP`, `kvraft/Proto.lean`): the payload's fact for the request's kind
(`reqOk`) in; with `ok`, the answer `b'` and its fact (`ansOk`, a step later: what a `Read` leaves).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Net kvraft

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

/-- See the file header. -/
abbrev checker.request.spec : Prop :=
  ∀ (F : KvFacts GF) (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) (id : w64) (kind : w8)
    (payload : GoSlice) (pl : List w8) (dqp : DFrac),
  1 ≤ uint.nat id → uint.nat id ≤ ls.length → (pl.length : Int) + 17 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck ∗
      isCheckerP F c γ ls ∗ payload ↦*{dqp} pl ∗ reqOk F id kind pl }}
    (App (App (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker.ty @!! go!"request"))
      (Val #id)) (Val #kind)) (Val #payload))
  {{ (b : GoSlice) (ok : Bool), RET (PairV #b #ok); payload ↦*{dqp} pl ∗
      (⌜ok = false⌝ ∨ ∃ b' : List w8, ⌜ok = true⌝ ∗ b ↦* b' ∗ ▷ ansOk F id kind pl b') }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
