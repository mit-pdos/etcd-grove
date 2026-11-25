/-
`Main(k)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, `notes/auth-lease-s4-draft.md` §2): `k`
etcd members started in process with auth on (the simple token provider) in the revocable lease mode,
each serving its raft handler on its own peer listener and its gRPC API on its client address, then the
lease set-up and checks across them (`run`). Lean-first (no Rocq counterpart). authN's `Main.spec` with
the lease premises.

**The triple:** for a member count `1 ≤ k ≤ 1000`, from the package's `isPkgInit`, the members' start
bundles (`startOf (members k)`), the main thread's token and `Main`'s named premises
(`etcd_authlease.premises`), `Main(k)` does not panic and returns `Ok` or `Failed`.

**The pure premises:** authN's (the `k` members' ids `ids` in the members' order and the bootstrap log Go
computes, putgetN's `BootFacts`), and the lease premises of `etcd_leaseexpiryN`'s `Main`: the ids' 15 low
bits distinct (`leaseIdsApart`), the peers' `/leases/internal` answers (`leasePeersOk`), and no lease
granted in the run expiring before it ends (`lease.leasesNoExpiry`, the deployment premise of the
revocable mode with auth on).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry),
  1 ≤ k → k ≤ 1000 → ids.length = k →
  etcd_putgetN.BootFacts ids ps ctxs boot → leaseIdsApart ids →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk → lease.leasesNoExpiry →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗
      ([∗list] m ∈ startOf (members k), etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      threadTok ∗ premises k N ids ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Main)) (Val #(W64 k)))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1⌝ }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
