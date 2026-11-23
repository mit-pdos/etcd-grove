/-
The package fact of `github_com.emirpasic.gods.trees.redblacktree` (dsv-epaxos, notes/dsv-epaxos.md): `True` (no variables a proof reads).
-/
module

public import Dsverify.GeneratedProof.github_com.emirpasic.gods.trees.redblacktree
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.encoding.json.Init
public import Dsverify.Proof.github_com.emirpasic.gods.containers.Init
public import Dsverify.Proof.github_com.emirpasic.gods.trees.Init
public import Dsverify.Proof.github_com.emirpasic.gods.utils.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.emirpasic.gods.trees.redblacktree

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.emirpasic.gods.trees.redblacktree :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.emirpasic.gods.trees.redblacktree :=
  build_get_is_pkg_init_wf

end def_

end github_com.emirpasic.gods.trees.redblacktree
end Perennial
