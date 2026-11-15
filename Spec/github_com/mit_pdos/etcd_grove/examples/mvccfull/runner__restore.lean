/- Lean-first (no Rocq counterpart).

`x.restore(l, f)` (`examples/mvccfull/mvccfull.go`): the follower, behind the leader, installs a
snapshot at the leader's point, as the server's `applySnapshot` does. A builder (`newMember` over the
next builder's file, `buildPathM`, fresh) applies the log up to the leader's count (`apply`, not
leading) and is shut (`inc_retire`, `shut`: its file's data the image of the leader's history there,
its lease bucket the live leases'). The follower's bounds are raised to the builder's (`revHi`,
`cmpHi`; the new `revHi`, the builder's revision, below `2 ^ 62` from `writerCtx`'s
`Ops < 2 ^ 38`); a backend is opened on the builder's file (`openBackend`, `etcdStorage_open.law` at the
image); the follower's lessor recovers from it (`lessor.Recover`: its owner part at the builder's
live leases, the ids ever granted extended, `logOk_recover`); the store restores onto it
(`KV.Restore.contract`, the follower's history a prefix of the builder's and its compaction revision
not above: `runM_mono`); the hook set on it; the old backend closed (its census with `Restore`'s
`storageRest`). The model fields, `revLo`, `cmpLo` follow; the checks (`Rev`, `FirstRev`,
`checkLeases`) pass; the `restores` counter. The readers and streams run throughout (the follower's
incarnation is the same store). Afterwards the follower is at the leader's count, one more build. (`writerOwn`'s `ops.length ≤ Ops`: the
builder's file is then among the unused ones, and its grants have write-back tokens; `writerCtx`'s
`Ops < 2 ^ 38`: the snapshot backend's `Ops + 1` kept tokens fit in its fresh stock.)
The closure passed to `Recover` captures the store (`kv := f.kv`, `a4c071c7dd`), so its
`mvccDeleter` triple is about a constant, not the field the writer rewrites at a restart.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev runner.restore.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)] (x : Loc) (ks : List GoString)
    (cfg : Config) (wr : List w64) (h : Loc) (γ : FullNames) (mp0 mp1 : Loc) (f0 f1 : GoFunc)
    (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp),
  v1.ops < v0.ops → backend.dbOpenOk → backend.dbCloseOk →
  sint.Z (limOf cfg) ≤ 2 ^ 57 → batchLimitOk (cblOf cfg) →
  {{ writerCtx (GF := GF) x ks cfg wr h γ.h ∗
      envVerifyOff ∗ threadTok ∗ writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs }}
    (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"restore") (Val #mp0)) (Val #mp1))
  {{ RET #(); threadTok ∗
      ∃ v1' : MemS, ⌜v1'.ops = v0.ops ∧ v1'.ι = v1.ι ∧ v1'.kv = v1.kv ∧ v1'.lp = v1.lp⌝ ∗
        writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1' nv (nb + 1) q qs }}

end spec

end mvccfull
end EtcdGrove
end Perennial
