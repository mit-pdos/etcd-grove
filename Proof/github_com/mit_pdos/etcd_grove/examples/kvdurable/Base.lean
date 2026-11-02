/-
Lean-first (no Rocq counterpart).

# The durable reconfiguring key-value store: package initialization (2026-10-31)

`examples/kvdurable` (kvreconf with durability through the `durable` package) has no
package-level variable (its constants are untyped or typed constants), so its package fact is
`True`; the packages it imports have theirs. Its pure model is in `Codec.lean` (the file and
snapshot codecs) and, as the port of kvreconf's goes on, in further files of this directory.
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.PbModel
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.kvdurable
public import Perennial.Proof.encoding.binary
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Proof.github_com.mit_pdos.gokv.trusted_proph.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.durable.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.sync.atomic.Base
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.kvdurable

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.kvdurable

end Perennial
