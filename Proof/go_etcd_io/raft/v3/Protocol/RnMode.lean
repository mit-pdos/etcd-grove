/-
Antithesis parity (#33, `notes/antithesis-parity-design.md` §1.1, §1.3, §2). **The two kinds of
guard and the messages `Msg` does not have**, as plain records (no Iris, no Goose state), for the
end relations (`Protocol/InputEnd.lean`), the RawNode scope (`RawNodeAt.lean`) and the Sim:
* `NodeK`: a node's `Config` flags the end relations read (design R2, a *node constant*);
* `RnMode`: the features a RawNode spec's exact effect covers (design R2, a *scope mode*); `{}` is
  the first harness's scope;
* `XTy`/`XMsg`: `MsgTransferLeader` and `MsgTimeoutNow`, which have no `MsgType` constructor
  (`mtypeOf`'s `none` arm): type, sender, receiver and term, all the binding reads of them.
-/
module

public import Perennial.Std.Word

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove

/-- A node's `Config` flags the end relations read (`newRaft` copies them, nothing writes them):
`PreVote`, `CheckQuorum`, `StepDownOnRemoval`. -/
structure NodeK where
  prevote : Bool := false
  cq : Bool := false
  sdr : Bool := false
deriving DecidableEq, Inhabited

/-- The features a RawNode spec's exact effect covers (design R2, §2). `{}` is the first harness's
scope (`raft_antithesis_robust_basic`'s). -/
structure RnMode where
  prevote : Bool := false
  cq : Bool := false
  reads : Bool := false
  transfer : Bool := false
  forwarding : Bool := false
  snapshots : Bool := false
  confChanges : Bool := false
  async : Bool := false
  /-- `Server ⊋ InitVoters`: a node outside its configuration. -/
  nonVoters : Bool := false
deriving DecidableEq, Inhabited

/-- The two message types `Msg` has no constructor for. -/
inductive XTy where
  | transferLeader
  | timeoutNow
deriving DecidableEq, Inhabited

/-- A `MsgTransferLeader` or `MsgTimeoutNow`: what the binding checks of it (`isUnmodelled`). -/
structure XMsg where
  ty : XTy
  src : w64
  dst : w64
  term : w64
deriving DecidableEq, Inhabited

end EtcdGrove
end Perennial
