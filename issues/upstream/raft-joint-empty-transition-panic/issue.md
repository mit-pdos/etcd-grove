Title: An empty ConfChangeV2 with a joint transition is accepted in a joint config, and every node panics applying it

### What happened?

In a joint configuration, the leader accepts `ConfChangeV2{Transition: ConfChangeTransitionJointExplicit}` with no changes, and `ApplyConfChange` on the committed entry panics. In a simple configuration, the leader refuses the same proposal (output trimmed):

```
=== RUN   TestRawNodeProposeEmptyJointConfChange/joint=false
raft2026/10/16 22:58:23 INFO: 1 ignoring conf change transition:ConfChangeTransitionJointExplicit at config voters=(1): not in joint state; refusing empty conf change
=== RUN   TestRawNodeProposeEmptyJointConfChange/joint=true
raft2026/10/16 22:58:23 INFO: 1 switched to configuration voters=(1)&&(1) learners=(2)
--- FAIL: TestRawNodeProposeEmptyJointConfChange (0.00s)
    --- PASS: TestRawNodeProposeEmptyJointConfChange/joint=false (0.00s)
    --- FAIL: TestRawNodeProposeEmptyJointConfChange/joint=true (0.00s)
panic: config is already joint [recovered, repanicked]
```

Every node applies the committed entry, so every node panics, and again on every restart. This affects any application proposing a `ConfChangeV2` with no changes and the `JointExplicit` or `JointImplicit` transition while the configuration is joint.

### What did you expect to happen?

The leader refuses the proposal in both configurations, replacing it with an empty entry as for other refused conf changes: `raft.proto` documents the proposal that leaves a joint configuration as "a ConfChangeV2 with only and optionally the Context field populated", which this one is not.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestRawNodeProposeEmptyJointConfChange`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-joint-empty-transition-panic/rawnode_test.go) on branch [`upamanyus/etcd-raft:fix/raft-joint-empty-transition-panic`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-joint-empty-transition-panic), off `main` (638f42739): a single voter enters a joint configuration with `JointExplicit` and one change, then proposes the empty `JointExplicit` change. On `main`, `joint=false` passes and `joint=true` panics as above.

### Anything else we need to know?

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
