/-
`(*lessor).Revoke` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`, `notes/leases-plan.md` (L2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **`le.Revoke(id)`** (unit T3, 2026-10-25), by the lease owner (the apply thread: its resource
at the item map of the state after `log`, and its revokers), at the watchable store `ws` (inner store `st`, names
`γw`, its lessor's `γl`) whose range deleter `rd` the lessor holds (`rdOwn`, `rdIs`), by the
store's sole writer at the committed log `log` (`watchWriter`, a reader slot, a write token, the
post-lock hook on `Pre` and the critical-section contract, as `watchableStore.Write` takes them,
and the certificates of a commit of deletions), over the real backend `d` (the lessor's `le.b`
its `*backend`: `lessorBeOn`), with the right to write the tracked buckets at `r` (`storeRb`):
* `id` not live: `ErrLeaseNotFound`, nothing changed (`Pre` back);
* `id` live: the keys the item map puts on `id`, in ascending order, deleted at one revision (none
  if there are none: no revision), the lease's record deleted from the `Lease` bucket in the
  same backend transaction (the tracked buckets' `lease` without its key, the id's 8 big-endian
  bytes), `id` out of the live set and its `revokec` closed: the sole writer at the new log, the
  owner's resource at its state's item map, `Post`.
The state's size bound is `sort.StringSlice.Sort`'s premise on the keys. -/
abbrev lease.lessor.Revoke.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64) (rd : GoFunc) (ws st : Loc) (γw : mvcc.WsNames)
    (log : mvcc.Log) (L : List w64) (d : mvcc.KBReal) (r : GMap GoString backend.BktData)
    (P Pre Q Post : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ lessorInv lp γl ∗
      ⌜γw.st.leases = γl ∧ γw.st.kb = some d⌝ ∗
      rdOwn γl rd ∗ mvcc.rdIs rd ws st γw ∗
      mvcc.storeReader st γw.st ∗ mvcc.storeWT γw.st ∗ mvcc.watchWriter γw log ∗
      ⌜log.length + 4 ≤ 2 ^ 63 ∧ (mvcc.stateAfter log).length ≤ 2 ^ 62⌝ ∗
      mvcc.hookIs γw.st P f ∗ mvcc.csContract P f Pre Q Post ∗
      leaseOwn γl L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗ leaseRevokers γl L ∗
      mvcc.storeRb γw.st r ∗ lessorBeOn lp d.be ∗
      □ (∀ pend : List mvcc.Change, ⌜∀ c ∈ pend, c.isDel = true⌝ -∗
        mvcc.certOkNext γw.st log pend) }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Revoke")) (Val #id))
  {{ (err : GoInterface), RET #err; rdOwn γl rd ∗ mvcc.storeReader st γw.st ∗
      mvcc.hookIs γw.st P f ∗ lessorBeOn lp d.be ∗
      ((⌜id ∉ L⌝ ∗
          (∃ e : GoInterfaceOk, globalAddr ErrLeaseNotFound ↦□ GoInterface.ok e ∗
            ⌜err = GoInterface.ok e⌝) ∗
          mvcc.storeWT γw.st ∗ mvcc.watchWriter γw log ∗ Pre ∗
          leaseOwn γl L (mvcc.leaseItemsOf (mvcc.stateAfter log)) ∗ leaseRevokers γl L ∗
          mvcc.storeRb γw.st r) ∨
       (⌜id ∈ L ∧ err = GoInterface.nil⌝ ∗
        ∃ ks : List GoString,
          ⌜ks.Nodup ∧
            (∀ k : GoString, k ∈ ks ↔
              (mvcc.leaseItemsOf (mvcc.stateAfter log)).lookup (LeaseItem.mk k) = some id) ∧
            (∀ (i j : Nat) (ki kj : GoString), ks[i]? = some ki → ks[j]? = some kj → i < j →
              go.GoStringLe ki kj)⌝ ∗
          mvcc.watchWriter γw (mvcc.commitLog log (ks.map mvcc.Change.del)) ∗ Post ∗
          leaseOwn γl (L.filter (· != id))
            (mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog log (ks.map mvcc.Change.del)))) ∗
          leaseRevokers γl (L.filter (· != id)) ∗
          mvcc.storeRb γw.st (mvcc.rbDel r mvcc.leaseName (u64Le id).reverse))) }}

end spec

end EtcdGrove
end Perennial
