/- Lean-first (no Rocq counterpart).

`x.shut(m)` (`examples/mvccfull/mvccfull.go`): member `m` closes its store, lessor and backend
(the chain's step 2, `Writer.lean`'s header), after its incarnation retired (`inc_retire`: the store's
state `σ`, nothing pending, owned by the writer) with every reader token back: `KV.Close`, the census
(`inc_census`), `lessor.Stop`, `backend.Close` (at `dbCloseOk`, the checks pass), the image
(`inc_stop_image`). Afterwards the file holds data `D`, the image of `σ`'s history (with an
unfinished compaction iff `u`), its lease bucket holding the live leases `L`'s records.
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
abbrev runner.shut.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames)
    (mp : Loc) (path : GoString) (bk : mvcc.KBReal) (lp : Loc) (kv : GoInterface) (γk : MvccName)
    (σ : MvccState) (L : List w64) (r : GMap GoString backend.BktData) (k : Nat),
  backend.dbCloseOk → σ.pending = none → leaseRecsOk r L →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ mF go!"kv" mp ↦ kv ∗ mF go!"le" mp ↦ lease.lessorIface lp ∗
      mF go!"be" mp ↦ (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #bk.be : GoInterface) ∗
      isMvcc kv γk ∗ mvccOpen γk ∗ mvccReaders γk mvccReaderN ∗
      mvccBackend γk 1 (etcdStorage bk) iprop(True) ∗ mvccState γk σ ∗ bkKeep bk path k ∗
      lease.lessorStopTok lp ∗ backend.rbPart bk.γB (· = leaseName) r }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"shut") (Val #mp))
  {{ RET #(); mF go!"kv" mp ↦ kv ∗ mF go!"le" mp ↦ lease.lessorIface lp ∗
      mF go!"be" mp ↦ (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #bk.be : GoInterface) ∗
      ∃ (D : backend.Data) (u : Bool), backend.fileHolds path D ∗ mvccImage D σ.log σ.crev u ∗
        ⌜leaseRecsOk (backend.rbData bk.P D) L⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
