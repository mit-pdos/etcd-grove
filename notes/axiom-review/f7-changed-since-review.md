# The 14 F7 auth drafts: what changed since their last review (F7 S3 step 1, 2026-11-26)

Branch `etcd-safe-f7` @ `008060bf60`. File `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/AuthViewDist.lean`
(AVD). Read-only diff; for the coordinator's fresh reviews of the changed ones.

**Reviewed commits.** Every one of the 14 drafts was last reviewed at `6d9d9fd662` (`f7-rerev-a.md`: `New_user`, the
KV/Txn calls, the five admin calls; `f7-rerev-c.md`: the four lease calls). The combined review at `5b15e37521`
(`f7-combined.md`) reviewed only `NewServer.specG_dist_proposed` and `Serve_dist_proposed`, not the drafts.

**Method.** `git diff 6d9d9fd662 008060bf60` of AVD (24 lines, two commits: `9a3a07ef29`, the F2 merge, and
`eb138f6f8c`, F7 step 3), and of every file whose definitions the drafts name: `S2Interim.lean` (`DistView`: docstring
only), `ClientViewDist.lean` (`view.leaseClientAt` unchanged; the F2 lease drafts moved out to their own pairs),
`KVClientDist.lean` (unchanged), `MemberLessor.lean` (the drafts name nothing of it), and the in-process vocabulary under
`Proof/go_etcd_io/etcd/{client,server}` (`auth/Reads`, `LeaseCheck`, `v3rpc/AuthService`, `ServerKVOn`, `InvAuthConn`,
`InvOp`, ...: no definition the drafts name was modified; the changes there since the review are additions:
`NewServer`/`NewLessor`/`NewTokenProvider` specs and proofs, `KVAuthModel` lemmas).

## Per draft

| draft | since `6d9d9fd662` |
|---|---|
| `New_user_dist` | unchanged |
| `KV_PutOn_dist` | unchanged (`writeAuD`, `writeCheckedD`, `opGrantD` unchanged) |
| `KV_DeleteOn_dist` | unchanged until 2026-11-27; then the premise `auth.reqShape` added (a weakening, `onpairs-deleteon.md`) |
| `Txn_CommitOn_dist` | unchanged (`txnReadCheckedD`, `authFloorD`, `writeCheckedD` unchanged) |
| **`KV_GetOn_dist`** | **changed**: its success arm's `readCheckedD` and `readAuthedD` (re-review A's N1, applied after `6d9d9fd662` and before `5b15e37521`; never reviewed) |
| `Auth_UserAdd_dist` | unchanged |
| `Auth_UserGrantRole_dist` | unchanged |
| `Auth_RoleAdd_dist` | unchanged |
| `Auth_RoleGrantPermission_dist` | unchanged |
| `Auth_AuthEnable_dist` | unchanged |
| `Lease_GrantOn_dist` | unchanged |
| `Lease_RevokeOn_dist` | unchanged |
| `Lease_TimeToLiveKeysOn_dist` | comment only (`Serve_dist_proposed` → `Serve_dist` in a `--` line) |
| `Lease_LeasesOn_dist` | unchanged |

**Outside the drafts, the tie they rely on (condition C of `f7-rerev-a.md`, "given the proposed Serve" of
`f7-rerev-c.md`) changed:** `Serve_dist_proposed` was adopted as `Serve_dist.spec` and `NewServer.specG_dist` took the
proposed text plus `etcdURLsFit U.peer → etcdURLsFit U.client →` (F7 step 3, `eb138f6f8c`; recorded in
`f7-diff-vs-inprocess.md`, "Final texts"). The file header's vocabulary paragraph now names `Serve_dist`/`memberUpOnL`
instead of `Serve_dist_proposed`/`memberUpOn` (comment only). The reviews' conditions name the proposed Serve; a reviewer
should confirm the adopted `Serve_dist.spec`'s auth-on arm still holds the member's auth store at `Γ.au mid` and its
lessor at `Γ.ls mid` (`memberUpOnL`, `Spec/.../etcd/dist/ServeDist.lean`).

## The one changed draft: `KV_GetOn_dist`'s helpers

```diff
 /-- **What a successful auth-on read tells the caller of its check, cluster-level**: the principal it
-was bound to may read `[key, end)` at the auth state after a requested prefix `L` extending `L₀`. -/
-def readAuthedD (γk : KVNames) (P : Option GoString) (L₀ : List EntryModel) (o : OpFull) : Prop :=
-  ∃ (user e : GoString) (rv : Nat) (L : List EntryModel), userOk P user ∧ L₀ <+: L ∧
+was bound to may read `[key, end)` at the auth state after the requested prefix `L` extending `L₀`
+(`readCheckedD` gives `srvReqLogLb γR L` with it: `L` is committed; re-review A's N1, 2026-11-26). -/
+def readAuthedD (γk : KVNames) (P : Option GoString) (L₀ L : List EntryModel) (o : OpFull) : Prop :=
+  ∃ (user e : GoString) (rv : Nat), userOk P user ∧ L₀ <+: L ∧
     apply.authEndOf o.base.rangeEnd e ∧
     auth.permitted (srvAuthAtLog γk srvAuthSt0 L) ⟨user, rv⟩ o.key e .read
@@
 /-- **A successful linearizable range's check** (persistent; `v3rpc.rangeAuthed` at the cluster):
 member `mid` of the endpoints served it, its verdict (`rangeClassFrom`) passed for `info` at its auth
 state of index `m` (published, `authFloorD`'s floor above `L₀`), `info`'s user one `P` may be bound to; and
-the cluster-level check (`readAuthedD`). -/
+the cluster-level check (`readAuthedD`) at a requested prefix `L ⊒ L₀` that is a lower bound of the
+requested log (`srvReqLogLb γR L`, re-review A's N1, 2026-11-26: so `L` is committed, not any extension). -/
 def readCheckedD [NetProtoGS] (eps : List GoString) (Γ : DistView)
     (γR : ServerRaftNames) (P : Option GoString) (L₀ : List EntryModel) (o : OpFull) : IProp GF :=
-  iprop(∃ (mid : w64) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat),
-    servedBy eps Γ mid ∗ ⌜userOk P info.Username' ∧ readAuthedD Γ.kv P L₀ o⌝ ∗
+  iprop(∃ (mid : w64) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat) (L : List EntryModel),
+    servedBy eps Γ mid ∗ ⌜userOk P info.Username' ∧ readAuthedD Γ.kv P L₀ L o⌝ ∗ srvReqLogLb γR L ∗
     apply.rangeClassFrom (.on (Γ.au mid)) m info o ∗ authFloorD Γ γR mid L₀ m)
```

What it does: the success arm is **stronger** (the prefix `L` at which the read was permitted is now a lower bound of
the requested log, `srvReqLogLb γR L`, where before it was any extension of `L₀`). A stronger post of an axiom is the
direction a review must check (it asserts more of Go): the claim is that the member's permission check ran at an auth
state that is the history's after a committed prefix. N1 called the old form a precision gap, not a soundness one; the new
form has not been reviewed.
