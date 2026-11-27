/-
`MainChecked(k5)` (`examples/etcd/all/checked.go`; the pure-premises plan's P4, 2026-11-24): `Main` on
a parameter it checks first (`ParamsOk`; out of range it returns, running nothing). The closed
theorem's program since then: its statement has no premise on the member count.

**The triple:** `Main`'s (`Main.lean`), over the member count as the `uint64` the program passes
(`uint.nat k₅`), without its premise on the count's range; the clusters' start bundles are needed only
when the parameter is in range (`paramsOk`: the bundle is behind `⌜paramsOk k₅⌝ -∗`, since out of range
the program's addresses may not be distinct and no bundle exists).
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

/-- **The two clusters' start bundles** (`Main.spec`'s, at the member count `uint.nat k₅`). -/
def startBundle (k₅ : w64) : IProp GF :=
  iprop(
  ([∗list] m ∈ etcd_restartN.members (uint.nat k₅),
    etcdstart.memberStartRes (GF := GF) m.Name' ⟨some m.Peer', none⟩) ∗
  etcdstart.memberStartRes (GF := GF) etcd_restart1.name {})

/-- See the file header. -/
abbrev MainChecked.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (N : Nat)
    (k₅ : w64) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8)) (boot₅ : List LogEntry)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  ids₅.length = uint.nat k₅ → etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅ →
  etcd_restart1.BootFacts rId ctxsR bootR →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all ∗
      (⌜paramsOk k₅⌝ -∗ startBundle k₅) ∗
      threadTok ∗
      etcd_restartN.premises (uint.nat k₅) N ids₅ ps₅ ctxs₅ boot₅ ∗
      etcd_restart1.premises N rId ctxsR bootR }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked)) (Val #k₅))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
