/-
`MainChecked(k1, clients, ops, n1, nw, nops, n2, cnw, cnops, k2, k3, k4, k5)`
(`examples/etcd/all/checked.go`; the pure-premises plan's P4, 2026-11-24): `Main` on parameters it
checks first (`ParamsOk`; out of range it returns, running nothing), with fault schedules of `n1` and
`n2` steps it draws itself (`cluster3.RandomSchedule`). The closed theorem's program since then: its
statement has no premise on the member counts, the workloads or the schedules.

**The triple:** `Main`'s (`Main.lean`), over the member counts as the `uint64`s the program passes
(`uint.nat k`), without its premises on the counts' ranges and the workloads' bounds, and without the
schedules; the clusters' start bundles are needed only when the parameters are in range (`paramsOk`:
the bundle is behind `⌜paramsOk …⌝ -∗`, since out of range a program's addresses may not be distinct
and no bundle exists).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.ParamsOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

/-- **The eleven clusters' start bundles** (`Main.spec`'s, at the member counts `uint.nat kᵢ`). -/
def startBundle (k₁ k₂ k₃ k₄ k₅ : w64) : IProp GF :=
  iprop(
  ([∗list] m ∈ etcd_txnlinfaultsN.startOf (etcd_txnlinfaultsN.members (uint.nat k₁)),
    etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
  ([∗list] b ∈ etcd_txnlinfaultsN.bridges (uint.nat k₁), netAddrFree (GF := GF) b) ∗
  cluster3.startRes (GF := GF) etcd_partition.clusterCfg ∗
  etcdstart.memberStartRes (GF := GF) go!"compactkv" ⟨none, some go!"127.0.0.1:23794"⟩ ∗
  etcdstart.memberStartRes (GF := GF) go!"putgetc" ⟨none, some go!"127.0.0.1:23791"⟩ ∗
  etcdstart.memberStartRes (GF := GF) go!"cachekv" ⟨none, some go!"127.0.0.1:23873"⟩ ∗
  ([∗list] m ∈ etcd_authN.startOf (etcd_authN.members (uint.nat k₂)),
    etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
  ([∗list] m ∈ etcd_authlease.startOf (etcd_authlease.members (uint.nat k₃)),
    etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
  ([∗list] m ∈ etcd_leaseN.startOf (etcd_leaseN.members (uint.nat k₄)),
    etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
  cluster3.startRes (GF := GF) etcd_leasecatchup.clusterCfg ∗
  ([∗list] m ∈ etcd_restartN.members (uint.nat k₅),
    etcdstart.memberStartRes (GF := GF) m.Name' ⟨some m.Peer', none⟩) ∗
  etcdstart.memberStartRes (GF := GF) etcd_restart1.name {})

/-- See the file header. -/
abbrev MainChecked.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat)
    (k₁ : w64) (ids₁ ps₁ : List w64) (ctxs₁ : List (List w8)) (boot₁ : List LogEntry)
    (pid₁ pid₂ pid₃ : w64) (psP : List w64) (ctxsP : List (List w8)) (bootP : List LogEntry)
    (cwId : w64) (ctxsCW : List (List w8)) (bootCW : List LogEntry)
    (cId : w64) (ctxsC : List (List w8)) (bootC : List LogEntry)
    (kvId : w64) (ctxsK : List (List w8)) (bootK : List LogEntry)
    (k₂ : w64) (ids₂ ps₂ : List w64) (ctxs₂ : List (List w8)) (boot₂ : List LogEntry)
    (k₃ : w64) (ids₃ ps₃ : List w64) (ctxs₃ : List (List w8)) (boot₃ : List LogEntry)
    (k₄ : w64) (ids₄ ps₄ : List w64) (ctxs₄ : List (List w8)) (boot₄ : List LogEntry)
    (lid₁ lid₂ lid₃ : w64) (psL : List w64) (ctxsL : List (List w8)) (bootL : List LogEntry)
    (k₅ : w64) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8)) (boot₅ : List LogEntry)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    (clients ops n₁ nw nops n₂ cnw cnops : w64)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  ids₁.length = uint.nat k₁ → etcd_txnlinfaultsN.BootFacts ids₁ ps₁ ctxs₁ boot₁ →
  etcd_partition.BootFacts pid₁ pid₂ pid₃ psP ctxsP bootP →
  etcd_compactwatch.BootFacts cwId ctxsCW bootCW →
  etcd_compacted.BootFacts cId ctxsC bootC →
  etcd_putget.BootFacts kvId ctxsK bootK →
  ids₂.length = uint.nat k₂ → etcd_putgetN.BootFacts ids₂ ps₂ ctxs₂ boot₂ →
  ids₃.length = uint.nat k₃ → etcd_putgetN.BootFacts ids₃ ps₃ ctxs₃ boot₃ →
  leaseIdsApart ids₃ →
  ids₄.length = uint.nat k₄ → etcd_putgetN.BootFacts ids₄ ps₄ ctxs₄ boot₄ →
  cluster3.BootFacts lid₁ lid₂ lid₃ psL ctxsL bootL →
  ids₅.length = uint.nat k₅ → etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅ →
  etcd_restart1.BootFacts rId ctxsR bootR →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk → lease.leasesNoExpiry →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all ∗
      (⌜paramsOk k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅⌝ -∗ startBundle k₁ k₂ k₃ k₄ k₅) ∗
      threadTok ∗
      etcd_txnlinfaultsN.premises (uint.nat k₁) N ids₁ ps₁ ctxs₁ boot₁ ∗
      etcd_partition.premises N pid₁ pid₂ pid₃ psP ctxsP bootP ∗
      etcd_compactwatch.premises N cwId ctxsCW bootCW ∗
      etcd_compacted.premises N cId ctxsC bootC ∗
      etcd_cache.premises N kvId ctxsK bootK ∗
      etcd_authN.premises (uint.nat k₂) N ids₂ ps₂ ctxs₂ boot₂ ∗
      etcd_authlease.premises (uint.nat k₃) N ids₃ ps₃ ctxs₃ boot₃ ∗
      etcd_leaseN.premises (uint.nat k₄) N ids₄ ps₄ ctxs₄ boot₄ ∗
      cluster3.premises etcd_leasecatchup.clusterCfg N lid₁ lid₂ lid₃ psL ctxsL bootL ∗
      etcd_restartN.premises (uint.nat k₅) N ids₅ ps₅ ctxs₅ boot₅ ∗
      etcd_restart1.premises N rId ctxsR bootR }}
    (App (App (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked))
      (Val #k₁)) (Val #clients)) (Val #ops)) (Val #n₁)) (Val #nw)) (Val #nops))
      (Val #n₂)) (Val #cnw)) (Val #cnops))
      (Val #k₂)) (Val #k₃)) (Val #k₄)) (Val #k₅))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
