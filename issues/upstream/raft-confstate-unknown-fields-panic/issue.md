Title: Raft panics on a snapshot whose ConfState has a field unknown to this version

### What happened?

A follower stepping a `MsgSnap` whose snapshot's `ConfState` has the voters `[1, 2]` and a field unknown to this version of `raftpb` panics; the same snapshot without that field is restored. The test below sends that message (output trimmed, `...` marking the cuts):

```
--- FAIL: TestRestoreFromSnapMsgUnknownField (0.00s)
panic: ConfStates not equivalent after sorting:
	&raftpb.ConfState{..., Voters:[]uint64{0x1, 0x2}, Learners:[]uint64(nil), VotersOutgoing:[]uint64(nil), LearnersNext:[]uint64(nil), ..., unknownFields:[]uint8{0x98, 0x6, 0x1}, sizeCache:0}
	&raftpb.ConfState{..., Voters:[]uint64{0x1, 0x2}, Learners:[]uint64(nil), VotersOutgoing:[]uint64(nil), LearnersNext:[]uint64(nil), ..., unknownFields:[]uint8(nil), sizeCache:0}
```

No raft version adds a field to `ConfState` yet, so the test adds one by hand. Once a version does, this will affect any node of an older version that receives a snapshot from a node of the newer version, as during a rolling upgrade.

### What did you expect to happen?

The follower should restore the snapshot, as it does the same snapshot without the unknown field: a field this version does not know should not stop it from restoring the voters `[1, 2]`.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestRestoreFromSnapMsgUnknownField`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-confstate-unknown-fields-panic/raft_test.go#L2757-L2776) on branch [`upamanyus/etcd-raft:fix/raft-confstate-unknown-fields-panic`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-confstate-unknown-fields-panic), off `main` (638f42739). On `main` it panics as above.

### Anything else we need to know?

A node whose storage holds a snapshot with such a `ConfState`, as after a downgrade, panics in the same way when it starts, so it cannot restart (reproduced with a test that is not on the branch).

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
