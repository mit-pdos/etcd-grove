/- Shared initialization facts for the API version used by membership and lease. -/
module

public import GeneratedProof.go_etcd_io.etcd.api.v3.version
public import Proof.github_com.Masterminds.semver.v3.PkgInit

@[expose] public section
noncomputable section

namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

namespace go_etcd_io.etcd.api.v3.version

/-- `api/v3/version` (names-only): the package variables `Version` (the request path's unit 4c:
the server's `start` logs it; moved here from the server's `BaseApply.lean`, 2026-10-13) and
`V3_6` (the lessor's `shouldPersistCheckpoints` compares the cluster's version with it) hold
fixed read-only values; `Version` is `"3.8.0-alpha.0"` (2026-10-23, rafthttp stage 5e-2: the
stream handler's `X-Server-Version`); `MinClusterVersion` is `"3.0.0"` (stage 5e-3: the stream
reader's `X-Min-Cluster-Version`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version :=
  define_is_pkg_init iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
    (∃ v : github_com.Masterminds.semver.v3.Version,
      globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
    globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0")
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.api.v3.version

end Perennial
