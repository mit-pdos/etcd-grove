/- Lean-first (no Rocq counterpart).

The package-initialization instance of `examples/osfs/bboltfs` (minibolt). Its fact
(`bboltfsInit`): its three error variables, `errPageSize`, `errFailed` and `errMapTooLarge`, hold
non-nil errors for good (their initializers are translated `errors.New` calls); `envErrors`, the
fourth variable, is not in it (the client reads it through `envFacts`). Its `isPkgInit` gives its
imports' (`sync`'s, `io`'s `EOF`, `os`'s); `pkgFacts` (`DB.lean`), what the proofs take, follows
from it (`pkgFacts_of_isPkgInit`). Its `wp_initialize'` is generated (`Init.lean`,
`etc/gen-init.py`); until 2026-11-24 the top-level theorem assumed the initializer's spec with
`pkgFacts` as its post.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
public import Proof.os.PkgInit
public import Proof.golang_org.x.sys.unix.PkgInit
public import Perennial.Proof.io
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact (see the file header). -/
def bboltfsInit : IProp GF :=
  iprop(∃ (e1 e2 e3 : GoInterface),
    globalAddr errFailed ↦□ e1 ∗ globalAddr errPageSize ↦□ e2 ∗ globalAddr errMapTooLarge ↦□ e3 ∗
    ⌜e1 ≠ interface.nil ∧ e2 ≠ interface.nil ∧ e3 ≠ interface.nil⌝)

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs :=
  define_is_pkg_init bboltfsInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs :=
  build_get_is_pkg_init_wf

theorem bboltfsInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs ⊢
      bboltfsInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

end init

end github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
end Perennial
