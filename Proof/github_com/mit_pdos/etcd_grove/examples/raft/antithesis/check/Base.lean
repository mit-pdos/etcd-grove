/-
Lean-first (no Rocq counterpart).

# The Go checker's package initialization (#33 S3b, 2026-11-23)

`examples/raft/antithesis/check` has no package-level variable (`GCBatch`, `MaxReads`, the kinds,
the roles and the field bits are constants), so its package fact is `True`; it imports nothing.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check

end Perennial
