Title: A ConfState with a field unknown to this version makes a follower panic on restoring a snapshot

### What happened?

A follower stepping a `MsgSnap` whose snapshot's `ConfState` has the voters `[1, 2]` and a field unknown to this version of `raftpb` panics, although it restores exactly the voters `[1, 2]` (output trimmed to the two configurations compared):

```
--- FAIL: TestRestoreFromSnapMsgUnknownField (0.00s)
panic: ConfStates not equivalent after sorting:
	&raftpb.ConfState{..., Voters:[]uint64{0x1, 0x2}, Learners:[]uint64(nil), VotersOutgoing:[]uint64(nil), LearnersNext:[]uint64(nil), ..., unknownFields:[]uint8{0x98, 0x6, 0x1}, ...}
	&raftpb.ConfState{..., Voters:[]uint64{0x1, 0x2}, Learners:[]uint64(nil), VotersOutgoing:[]uint64(nil), LearnersNext:[]uint64(nil), ..., unknownFields:[]uint8(nil), ...}
```

No raft version adds a field to `ConfState` today, so the example adds an unknown field by hand; once one does, this would affect any node reading a `ConfState` written by a newer raft, in a snapshot from a newer leader during an upgrade or in its own storage after a downgrade.

### What did you expect to happen?

The follower restores the snapshot, as it does the same snapshot without the unknown field (`TestRestoreFromSnapMsg`): a field this version does not know does not change the configuration it restores.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestRestoreFromSnapMsgUnknownField`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-confstate-unknown-fields-panic/raft_test.go) on branch [`upamanyus/etcd-raft:fix/raft-confstate-unknown-fields-panic`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-confstate-unknown-fields-panic), off `main` (638f42739). On `main` it panics as above.

### Anything else we need to know?

A node started with a `MemoryStorage` whose snapshot has such a `ConfState` panics in the same way, so it cannot restart (reproduced with a test that is not on the branch).

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
