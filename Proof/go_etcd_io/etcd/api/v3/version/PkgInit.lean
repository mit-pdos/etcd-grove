/-
The package-initialization instance of etcd's `api/v3/version`: its fact (moved from the lease's
`Base.lean`, prove-initleft 2026-11-21, so that `storage/schema`'s instance, in the server's
`Base.lean`, below the lease's, can name it: schema imports version since its `schemaChanges` is
translated). Its fact is an assumption about package initialization, proved from `initialize'` by
`InitLinked.lean` (`etc/gen-init.py`).
-/
module

public import Code.go_etcd_io.etcd.api.v3.version
public import GeneratedProof.go_etcd_io.etcd.api.v3.version
public import Proof.github_com.Masterminds.semver.v3.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.api.v3.version

/-- `api/v3/version` (names-only): the package variables `Version` (the request path's unit 4c:
the server's `start` logs it; moved here from the server's `BaseApply.lean`, 2026-10-13) and
`V3_6` (the lessor's `shouldPersistCheckpoints` compares the cluster's version with it) hold
fixed read-only values; `Version` is `"3.8.0-alpha.0"` (2026-10-23, rafthttp stage 5e-2: the
stream handler's `X-Server-Version`); `MinClusterVersion` is `"3.0.0"` (stage 5e-3: the stream
reader's `X-Min-Cluster-Version`); `V3_7` and `V3_8` hold read-only values too (prove-initleft,
2026-11-21: `storage/schema`'s initializer reads them, the keys of its `schemaChanges`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version :=
  define_is_pkg_init iprop(globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ go!"3.8.0-alpha.0" ∗
    (∃ v : github_com.Masterminds.semver.v3.Version,
      globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v) ∗
    globalAddr go_etcd_io.etcd.api.v3.version.MinClusterVersion ↦□ go!"3.0.0" ∗
    (∃ v7 v8 : github_com.Masterminds.semver.v3.Version,
      globalAddr go_etcd_io.etcd.api.v3.version.V3_7 ↦□ v7 ∗
      globalAddr go_etcd_io.etcd.api.v3.version.V3_8 ↦□ v8))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.api.v3.version

end init

end Perennial
