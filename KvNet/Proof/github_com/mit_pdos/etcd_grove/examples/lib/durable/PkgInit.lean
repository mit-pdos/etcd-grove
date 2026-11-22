-- The copy for the part `KvNet/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/PkgInit.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The package fact of `examples/lib/durable` (the part's translation, with its bodies; W4c U2): its
mutex `mu` is a `sync.Mutex` guarding nothing (`True`). The calls are serialized in the proof by
the file's handle (`DurFs.durHandle`), not by the mutex, which the specs need only not to block
forever on a mutex nobody initialized.
-/
module

public import KvNet.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.durable
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base
public import Proof.os.PkgInit
public import Proof.path.filepath.PkgInit

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

/-- `durable`'s fact: `mu` is a mutex guarding nothing. -/
abbrev durable.durableInit : IProp GF :=
  iprop(sync.isMutex (globalAddr github_com.mit_pdos.etcd_grove.examples.lib.durable.mu) iprop(True))

end EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.durable

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable :=
  define_is_pkg_init EtcdGrove.durable.durableInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable :=
  build_get_is_pkg_init_wf

/-- `durable`'s fact read off its package's: `mu` is a mutex guarding nothing. -/
theorem mu_of_pkgInit :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable ⊢
      sync.isMutex (globalAddr github_com.mit_pdos.etcd_grove.examples.lib.durable.mu) iprop(True) :=
  isPkgInit_access (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable

end github_com.mit_pdos.etcd_grove.examples.lib.durable

end init

end Perennial
