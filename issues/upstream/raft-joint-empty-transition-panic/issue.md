Title: Every node panics applying an empty ConfChangeV2 with a joint transition proposed in a joint config

### What happened?

With a single voter, node 1, which leads:

1. Node 1 is proposed `ConfChangeV2{Transition: ConfChangeTransitionJointExplicit, Changes: [AddLearnerNode 2]}`; it commits, and node 1 applies it, entering the joint configuration `voters=(1)&&(1) learners=(2)`.
2. After that, node 1 is proposed `ConfChangeV2{Transition: ConfChangeTransitionJointExplicit}`, with no changes. Node 1 accepts the proposal, and the entry commits.
3. `ApplyConfChange` on the committed entry panics with `config is already joint`.

The test below runs these steps (output trimmed):

```
--- FAIL: TestRawNodeProposeEmptyJointConfChange (0.00s)
        	Error:      	func (assert.PanicTestFunc)(0x72a8a0) should not panic
        	            		Panic value:	config is already joint
```

Every node applies the committed entry, so every node panics, and again after a restart. This affects any application that proposes, in a joint configuration, a `ConfChangeV2` with no changes and the `JointExplicit` or `JointImplicit` transition.

### What did you expect to happen?

Node 1 should refuse the proposal in step 2, as it refuses an empty conf change in a configuration that is not joint, so that every committed conf change applies: `raft.proto` documents the proposal that leaves a joint configuration as "a ConfChangeV2 with only and optionally the Context field populated", which this one is not.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestRawNodeProposeEmptyJointConfChange`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-joint-empty-transition-panic/rawnode_test.go#L344-L382) on branch [`upamanyus/etcd-raft:fix/raft-joint-empty-transition-panic`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-joint-empty-transition-panic), off `main` (638f42739). On `main` it fails as above.

### Anything else we need to know?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
