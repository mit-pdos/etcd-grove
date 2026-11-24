/- Lean-first (no Rocq counterpart).

The package-initialization instance of `examples/osfs/walfs`: it has no package variable and no
`init()`, so its fact is `True`; its `isPkgInit` gives its imports' (`os`'s, which the
path specs of `os` take, 2026-11-24). Its `wp_initialize'` is generated (`Init.lean`,
`etc/gen-init.py`); until 2026-11-24 the top-level theorem assumed the initializer ran (`Hinit_wp`).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs
public import Proof.os.PkgInit
public import Proof.golang_org.x.sys.unix.PkgInit
public import Perennial.Proof.io

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.osfs.walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.walfs :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.walfs :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.osfs.walfs
end Perennial
