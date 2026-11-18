/-
Package initialization of `go_etcd_io.etcd.api.v3.version`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`server/v3/lease/Base.lean`): `Version` holds `"3.8.0-alpha.0"`, `V3_6` a fixed value and
`MinClusterVersion` `"3.0.0"`. Its
initializer runs its variables' untranslated initializers (`version.go`): string constants,
`semver` versions (`*semver.New(3, 6, 0, "", "")`), and `AllVersions`; the trust-boundary axioms
`Version_init`, `V3_6_init` and `MinClusterVersion_init` state the three the fact reads,
`opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.api.v3.version
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.version`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([APIVersion.init,
        GitSHA.init,
        V3_0.init,
        V3_1.init,
        V3_2.init,
        V3_3.init,
        V3_4.init,
        V3_5.init,
        V3_7.init,
        V3_8.init,
        V3_9.init,
        V4_0.init,
        AllVersions.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.version`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `Version = "3.8.0-alpha.0"` (`version.go`). -/
axiom Version_init :
    {{ (True : IProp GF) }} (App (Val Version.init) (Val #()))
    {{ RET #(); globalAddr Version ↦ go!"3.8.0-alpha.0" }}

/-- `V3_6 = *semver.New(3, 6, 0, "", "")` (`version.go`): a `semver.Version`. -/
axiom V3_6_init :
    {{ (True : IProp GF) }} (App (Val V3_6.init) (Val #()))
    {{ RET #(); ∃ v : github_com.Masterminds.semver.v3.Version, globalAddr V3_6 ↦ v }}

/-- `MinClusterVersion = "3.0.0"` (`version.go`). -/
axiom MinClusterVersion_init :
    {{ (True : IProp GF) }} (App (Val MinClusterVersion.init) (Val #()))
    {{ RET #(); globalAddr MinClusterVersion ↦ go!"3.0.0" }}

end go_etcd_io.etcd.api.v3.version
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.version.Assumptions]

namespace go_etcd_io.etcd.api.v3.version

end go_etcd_io.etcd.api.v3.version

end init

end Perennial
