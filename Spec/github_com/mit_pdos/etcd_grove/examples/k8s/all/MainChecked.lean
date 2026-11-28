/-
`MainChecked(k1, clients, ops, watchers, wops, n1, k2, n2)` (`examples/k8s/all/checked.go`; the
pure-premises plan's P5, 2026-11-24): `Main` on parameters it checks first (`ParamsOk`; out of range it
returns, running nothing), with fault schedules of `n1` and `n2` steps it draws itself
(`cluster3.RandomSchedule`). The closed theorem's program since then: its statement has no premise on
the member counts, the workload or the schedules.

**The triple:** `Main`'s (`Main.lean`), over the member counts as the `uint64`s the program passes
(`uint.nat k`), without its premises on the counts' ranges and the workload's bounds, and without the
schedules; the two clusters' start bundles are needed only when the parameters are in range
(`paramsOk`: behind `⌜paramsOk …⌝ -∗`, since out of range the program's addresses may collide and no
bundle exists).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.ParamsOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

/-- **The two clusters' start bundles** (`Main.spec`'s, at the member counts `uint.nat kᵢ`). -/
def startBundle (k₁ k₂ : w64) : IProp GF :=
  iprop(
  ([∗list] m ∈ k8s_etcd3N.startOf (k8s_etcd3N.members (uint.nat k₁)),
    etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
  ([∗list] b ∈ k8s_etcd3N.bridges (uint.nat k₁), netAddrFree (GF := GF) b) ∗
  ([∗list] m ∈ k8s_etcd3N.startOf (k8s_compactorN.members (uint.nat k₂)),
    etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
  ([∗list] b ∈ k8s_compactorN.bridges (uint.nat k₂), netAddrFree (GF := GF) b))

/-- See the file header. -/
abbrev MainChecked.spec : Prop :=
  ∀ [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.Assumptions] [k8s_io.apimachinery.pkg.runtime.schema.Assumptions]
    [k8s_io.apiserver.pkg.storage.Assumptions] [k8s_io.apiserver.pkg.storage.value.Assumptions]
    (k₁ : w64) (N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry)
    (k₂ : w64) (ids' : List w64) (ps' : List w64) (ctxs' : List (List w8)) (boot' : List LogEntry)
    (clients ops watchers wops n₁ n₂ : w64)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  ids.length = uint.nat k₁ → k8s_etcd3N.BootFacts ids ps ctxs boot →
  ids'.length = uint.nat k₂ → k8s_compactorN.BootFacts ids' ps' ctxs' boot' →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → k8s_etcd3.storageErrTyOk →
  k8s_etcd3.objTyOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.all ∗
      (⌜paramsOk k₁ clients ops watchers wops k₂⌝ -∗ startBundle k₁ k₂) ∗
      threadTok ∗
      k8s_etcd3N.premises (uint.nat k₁) N ids ps ctxs boot ∗
      k8s_compactorN.premises (uint.nat k₂) N ids' ps' ctxs' boot' ∗
      k8s.regAuth (∅ : GMap GoString GName) }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.MainChecked))
      (Val #k₁)) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)) (Val #n₁))
      (Val #k₂)) (Val #n₂))
  {{ RET #(); True }}

end spec

end k8s_all
end EtcdGrove
end Perennial
