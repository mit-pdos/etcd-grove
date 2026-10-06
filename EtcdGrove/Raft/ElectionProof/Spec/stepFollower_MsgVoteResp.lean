/-
Port of `election_proof/spec_stepFollower_MsgVoteResp.v`.

Lean notes:
* The Rocq spec name `wp_stepFollower_MsgVoteResp` (a case of `stepFollower`, not a
  function of its own) is kept as `stepFollower_MsgVoteResp.spec`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `stepFollower` on a `MsgVoteResp`: nothing at all.

`stepFollower.impl` (`Perennial/Code/go_etcd_io/raft/v3.lean`) is a single type switch
over `m.Type` with arms for `MsgProp`, `MsgApp`, `MsgHeartbeat`, `MsgSnap`,
`MsgTransferLeader`, `MsgForgetLeader`, `MsgTimeoutNow`, `MsgReadIndex` and
`MsgReadIndexResp`. `MsgVoteResp` is none of those, so control falls off the end of the
switch to the function's trailing `return nil` without reading or writing a single
field of the raft struct.

Hence: state completely unchanged, no message sent, `nil` error. That is the whole
content of the spec, and it is what makes `Step`'s `MsgVoteResp` branch refine
`Step.refl` when the receiver is a follower.

No premise beyond the message type is needed. In particular the role is not mentioned:
the body never looks at `r.state`, so the triple holds for any `s`. (A caller reaching
this function through `r.step` does know `s.role = .follower`, from `ownRaftPhys`'s
`Hstepfn` conjunct and `stepFuncOf`; it simply does not have to pass it on.) -/
abbrev stepFollower_MsgVoteResp.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message),
  m.Type' = MsgVoteResp →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (App (Val #(functions stepFollower [])) (Val #r)) (Val #m))
  {{ (err : GoInterface), RET #err;
      ownRaftPhys cfg r id s ∗ ⌜err = interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
