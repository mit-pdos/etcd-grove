# raft: a `ConfChangeV2` with an undefined `Transition` is committed, then panics every node that applies it

**Status**: open (not reported upstream; an undocumented precondition: applications that build
their `ConfChangeV2`s from the three named transitions never meet it).

**Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):

- `raftpb/confchange.go:82-104` (`ConfChangeV2.EnterJoint`): with joint consensus (a transition
  other than `Auto`, or more than one change), a `Transition` other than `Auto`,
  `JointImplicit`, `JointExplicit` reaches `panic(fmt.Sprintf("unknown transition: %+v", c))`.
- `raft.go:1296-1333` (`stepLeader`, `MsgProp`): a conf-change entry is checked only for a pending
  conf change and for joint-state consistency (`cc.AsV2().Changes`); its `Transition` is not
  checked, so the leader appends it and it is committed.
- `raft.go:1939-1950` (`applyConfChange`, reached from `RawNode.ApplyConfChange` and
  `node.ApplyConfChange`) calls `cc.EnterJoint()`.
- `node.go:141-152` (`Node.ProposeConfChange`) and `raftpb/raft.proto` (`ConfChangeTransition`)
  document neither the restriction nor the panic. `ConfChangeTransition` is an `int32` enum, so
  any value can be built (or decoded from an older or newer peer's bytes).

**What happens**: `ProposeConfChange(pb.ConfChangeV2{Transition: 7, Changes: [AddNode 2]})`
returns `nil`; the entry is committed; `ApplyConfChange` on it panics with `unknown transition:
{Transition:7 ...}`. Every node applies the same committed entry, so every node panics, and
again on every restart (the entry is in the log). Reproduction (in package `raft`):

```go
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A ConfChangeV2 with an undefined Transition is accepted by the leader, committed, and
// panics in ApplyConfChange (ConfChangeV2.EnterJoint) on every node that applies it.
func TestUnknownTransitionPanicsOnApply(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	if err != nil {
		t.Fatal(err)
	}
	if err := rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	for rn.raft.state != StateLeader {
		rd := rn.Ready()
		s.Append(rd.Entries)
		rn.Advance(rd)
	}
	cc := pb.ConfChangeV2{
		Transition: pb.ConfChangeTransition(7),
		Changes:    []pb.ConfChangeSingle{{Type: pb.ConfChangeAddNode, NodeId: 2}},
	}
	if err := rn.ProposeConfChange(cc); err != nil {
		t.Fatalf("proposal refused: %v", err)
	}
	for i := 0; i < 10; i++ {
		rd := rn.Ready()
		s.Append(rd.Entries)
		for _, e := range rd.CommittedEntries {
			if e.Type != pb.EntryConfChangeV2 {
				continue
			}
			var got pb.ConfChangeV2
			if err := got.Unmarshal(e.Data); err != nil {
				t.Fatal(err)
			}
			if len(got.Changes) == 0 {
				continue
			}
			defer func() {
				if r := recover(); r != nil {
					t.Logf("ApplyConfChange panicked: %v", r)
				} else {
					t.Fatalf("no panic")
				}
			}()
			rn.ApplyConfChange(got)
			return
		}
		rn.Advance(rd)
	}
	t.Fatal("the conf change was never committed")
}
```

Output: `ApplyConfChange panicked: unknown transition: {Transition:7 Changes:[{Type:ConfChangeAddNode NodeId:2}] Context:[]}`.

**Expected**: either the proposal is refused (`ErrProposalDropped`, or the entry replaced by an
empty normal entry, as `stepLeader` does for a conf change it refuses), or the precondition is
documented on `ProposeConfChange`/`ConfChangeV2` (an application may avoid the panic by
treating such an entry as a noop and not calling `ApplyConfChange`, which the documentation
allows, but nothing tells it to).

**How the proof handles it**: `ConfChangeV2.EnterJoint`'s spec
(`Spec/go_etcd_io/raft/v3/raftpb/ConfChangeV2__EnterJoint.lean`) states the panic: its result is
`enterJointOf c.Transition (len c.Changes)` (`InvConfChangeMsg.lean`), `none` (a panic) in this
case. A spec of `applyConfChange` will need a premise excluding it.

**Possible fixes**: in `stepLeader`, refuse a `ConfChangeV2` whose `Transition` is undefined (as
for the other refused conf changes); or have `EnterJoint` return an error instead of panicking.

**Found**: 2026-10-13, specifying `ConfChangeV2.EnterJoint` (reconfiguration, stage 0).
