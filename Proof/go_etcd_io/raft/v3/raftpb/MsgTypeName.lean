/-
**The names of raft's message types** (Q9 of `notes/trace-validation-plan.md`, 2026-11-09): what
`MessageType.String` returns (`raftpb.msgTypeString`, the result of
`Spec/go_etcd_io/raft/v3/raftpb/MessageType__String.lean`), its value at each message type, and the
law that gives a `String` method meeting an exact spec of this form `fmt`'s weak spec
(`fmt.stringMethodSpec_of_wp`: rafthttp's logs, which needed only some string, take it from there).
-/
module

public import Spec.fmt.Errorf
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.strconv.FormatIntDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- What `t.String()` returns: `MessageType_name`'s entry at `t` (the type's name, `"MsgApp"`, ...),
else `t` in decimal (`strconv.Itoa(int(t))`, protobuf-go's `EnumStringOf`'s fallback; `int(t)`
sign-extends the `int32`). -/
def raftpb.msgTypeString (t : w32) : GoString :=
  match go_etcd_io.raft.v3.raftpb.msgTypeNames !! t with
  | some s => s
  | none => fmtInt (W64 (sint.Z t)) (W64 10)

/-- The name of every message type: `MessageType_name`'s 24 entries. -/
theorem raftpb.msgTypeString_names (t : w32) (s : GoString)
    (h : go_etcd_io.raft.v3.raftpb.msgTypeNames !! t = some s) : raftpb.msgTypeString t = s := by
  unfold raftpb.msgTypeString; rw [h]

/-- The names of the message types raft's trace logs (`makeTracingMessage`'s
`m.GetType().String()`), and of the others raft sends between nodes. -/
theorem raftpb.msgTypeString_MsgApp : raftpb.msgTypeString (W32 3) = go!"MsgApp" := by
  unfold raftpb.msgTypeString go_etcd_io.raft.v3.raftpb.msgTypeNames; simp
theorem raftpb.msgTypeString_MsgAppResp : raftpb.msgTypeString (W32 4) = go!"MsgAppResp" := by
  unfold raftpb.msgTypeString go_etcd_io.raft.v3.raftpb.msgTypeNames; simp
theorem raftpb.msgTypeString_MsgVote : raftpb.msgTypeString (W32 5) = go!"MsgVote" := by
  unfold raftpb.msgTypeString go_etcd_io.raft.v3.raftpb.msgTypeNames; simp
theorem raftpb.msgTypeString_MsgVoteResp : raftpb.msgTypeString (W32 6) = go!"MsgVoteResp" := by
  unfold raftpb.msgTypeString go_etcd_io.raft.v3.raftpb.msgTypeNames; simp
theorem raftpb.msgTypeString_MsgHeartbeat : raftpb.msgTypeString (W32 8) = go!"MsgHeartbeat" := by
  unfold raftpb.msgTypeString go_etcd_io.raft.v3.raftpb.msgTypeNames; simp
theorem raftpb.msgTypeString_MsgHeartbeatResp :
    raftpb.msgTypeString (W32 9) = go!"MsgHeartbeatResp" := by
  unfold raftpb.msgTypeString go_etcd_io.raft.v3.raftpb.msgTypeNames; simp

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The weak form**: a no-argument method `m` of an `int32`-based type `ty` that returns a
string `f x` from a persistent precondition `P` (an exact spec, as `MessageType.String`'s from its
package's `isPkgInit`) has, given `P`, `fmt`'s `fmt.stringMethodSpec` (it returns some string,
needing nothing more), which `fmt`'s and zap's specs ask of an argument's `String()`. -/
theorem fmt.stringMethodSpec_of_wp (ty : go.GoType) (m : GoString) (P : IProp GF) [Persistent P]
    (f : w32 → GoString)
    (h : ∀ x : w32, {{ P }} (App (Val (x @!! ty @!! m)) (Val #())) {{ RET #(f x); True }})
    (x : w32) :
    P ⊢ fmt.stringMethodSpec (interface.mk ty #x) m := by
  iintro #HP
  unfold fmt.stringMethodSpec
  imodintro
  iintro %Φ HΦ
  iapply h x $$ HP
  inext
  iintro -
  iapply HΦ

end law

end EtcdGrove
end Perennial
