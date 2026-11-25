/-
# kvraft's wire encoding of raft's messages, pure (2026-11-21)

What `putMsg` (`examples/raft/kvraft/wire.go`) writes, as a function of the message's model
(`MsgSt`, `Proof/go_etcd_io/raft/v3/PbModel.lean`), over kvdurable's codec (`Codec.lean`:
`putB`, `encEntries`, `encSnap`, `encConf`):

* `encMsg st`: its type (8 bytes, the `int32` sign-extended as Go's `uint64(m.GetType())`), to,
  from, term, log term, index, commit and vote (8 bytes each), reject (one byte, `1` for `true`),
  reject hint (8 bytes), its context (`putB`), its entries' number (8 bytes), each entry
  (`encEntries`), then its snapshot (one byte `0` for none; `1` then `encSnap`). Its responses are
  not written.

`MsgWf st`: a message `getMsg` reads back: a type raft has (`raftpb.msgTypeNames`, the table the
decoder looks the type up in, non-negative), entries and a snapshot `getMsgEntry`/`getSnapshot` read
back (an entry of any type: `MsgEntWf`), a context and an entry list of Go slices' lengths.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec
public import KvRaft.Proof.go_etcd_io.raft.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove.kvraft

open go_etcd_io.raft.v3

/-- The byte of a boolean: `1` for `true`, `0` for `false` (`autoB`'s). -/
abbrev boolB (b : Bool) : w8 := autoB b

/-- `putMsg`'s snapshot part: `0`, or `1` and the snapshot. -/
def encSnapOpt : Option SnapshotM → List w8
  | none => [W8 0]
  | some s => W8 1 :: encSnap s

/-- `putMsg`: see the file header. -/
def encMsg [GooseExts] (st : MsgSt) : List w8 :=
  u64Le (W64 (sint.Z st.msg.Type')) ++ (u64Le st.msg.To' ++ (u64Le st.msg.From' ++
    (u64Le st.msg.Term' ++ (u64Le st.msg.LogTerm' ++ (u64Le st.msg.Index' ++
    (u64Le st.msg.Commit' ++ (u64Le st.msg.Vote' ++ (boolB st.msg.Reject' ::
    (u64Le st.msg.RejectHint' ++ (putB st.ctx ++ (u64Le (W64 st.ents.length) ++
    (encEntries st.ents ++ encSnapOpt st.snap))))))))))))

/-- An entry of a message `getMsgEntry` reads back: of any type, its data of a Go slice's length. -/
def MsgEntWf [GooseExts] (e : EntryM) : Prop := (e.Data'.length : Int) < 2 ^ 63

/-- A message `getMsg` reads back (see the file header). -/
def MsgWf [GooseExts] (st : MsgSt) : Prop :=
  (raftpb.msgTypeNames !! (W32 (sint.Z st.msg.Type'))).isSome ∧ 0 ≤ sint.Z st.msg.Type' ∧
  (∀ e ∈ st.ents, MsgEntWf e) ∧ (st.ents.length : Int) < 2 ^ 63 ∧
  (st.ctx.length : Int) < 2 ^ 63 ∧ (∀ s, st.snap = some s → SnapWf s)

theorem encEntries_snoc [GooseExts] (l : List EntryM) (e : EntryM) :
    encEntries (l ++ [e]) = encEntries l ++ encEntry e := by
  induction l with
  | nil => simp [encEntries]
  | cons a r ih => simp [encEntries, ih, List.append_assoc]

end EtcdGrove.kvraft
end Perennial
