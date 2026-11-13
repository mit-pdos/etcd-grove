/-
The package fact of `pkg/v3/ioutil` (the part's translation: the WAL's page writer, with its body):
`defaultBufferBytes` (`pagewriter.go`, a `var`) holds `128 * 1024`, read-only for good (only its
tests assign it). WAL W6, 2026-11-13.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.pkg.v3.ioutil
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.io

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace EtcdGrove

/-- `ioutil`'s fact: `defaultBufferBytes` holds `128 * 1024`, read-only. -/
abbrev ioutil.ioutilInit : IProp GF :=
  iprop(globalAddr go_etcd_io.etcd.pkg.v3.ioutil.defaultBufferBytes ↦□ (W64 131072))

end EtcdGrove

namespace go_etcd_io.etcd.pkg.v3.ioutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil :=
  define_is_pkg_init EtcdGrove.ioutil.ioutilInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.ioutil

end init

end Perennial
