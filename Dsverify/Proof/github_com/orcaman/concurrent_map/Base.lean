/-
The package fact of `github_com.orcaman.concurrent_map` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `True`: `SHARD_COUNT` is the boot thread's, owned (`swift.mutGlobalsInit`; the lab's `cmap.pkgSt`). Its initializer is not generated: its first run hands the node's boot thread owned resources Perennial's `wp_initialize'` cannot return (notes/dsv-swiftpaxos.md, "Package initialization"); its proof is hand-written.
-/
module

public import Dsverify.GeneratedProof.github_com.orcaman.concurrent_map
public import Dsverify.Proof.encoding.json.Init
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.orcaman.concurrent_map

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.orcaman.concurrent_map :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.orcaman.concurrent_map :=
  build_get_is_pkg_init_wf

end def_

end github_com.orcaman.concurrent_map
end Perennial
