/- Lean-first (no Rocq counterpart).

`x.openBackend(path)` (`examples/mvccfull/mvccfull.go`): `backend.New` on the file `path` (holding
the data `D`) with `DefaultBackendConfig`'s configuration and the run's batch settings (the limit
`limOf cfg`, the tester's parameters `mvccrand.rcP`): `backend.New.spec`'s post at `dbOpenOk` (its
panic excluded), for the opener's resources `W`, `Pk`, `K` (`newPostK`), its file recorded (`bFile`),
the thread token back.
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
abbrev runner.openBackend.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)] (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64)
    (h : Loc) (γh : HistNames) (path : GoString) (D : backend.Data)
    (W Pk K : backend.BNames → IProp GF),
  backend.dbOpenOk → sint.Z (limOf cfg) ≤ 2 ^ 57 →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ backend.fileHolds path D ∗ envVerifyOff ∗ threadTok ∗
      (∀ γ : backend.BNames, backend.hkOwn γ (backend.hkData (mvccrand.rcP (limOf cfg)) D) ∗
        backend.bFresh γ ={⊤}=∗ W γ ∗ Pk γ ∗ K γ) }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"openBackend") (Val #path))
  {{ (r : GoInterface), RET #r; threadTok ∗
      ∃ (b : Loc) (γB : backend.BNames),
        ⌜r = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b⌝ ∗
        backend.newPostK γB (mvccrand.rcP (limOf cfg)) W Pk K b D ∗ backend.bFile γB path }}

end spec

end mvccfull
end EtcdGrove
end Perennial
