/-
Package initialization of google/btree: the global `itemLess` (the less function of the
non-generic `BTree`, `func(a, b Item) bool { return a.Less(b) }`) is set.
-/
import GoogleBtree.GeneratedProof.github_com.google.btree
import Perennial.Proof.ProofPrelude
import Perennial.Proof.fmt
import Perennial.Proof.io
import Perennial.Proof.strings
import Perennial.Proof.sync
import Perennial.Proof.sort_proof.sort_init

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI github_com.google.btree

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

/-- `f a b` runs `a.Less(b)` (the method call on the interface value `a`). -/
def isItemLessFn (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (a b : GoInterface) (Φ : val → IProp GF),
    WP (App (App (Val (GoInstruction (MethodResolve Item.ty go!"Less"))) (Val #a)) (Val #b))
      {{ Φ }} -∗
    WP (App (App (Val #f) (Val #a)) (Val #b)) {{ Φ }})

instance isItemLessFn_persistent (f : GoFunc) : Persistent (isItemLessFn (GF := GF) f) := by
  unfold isItemLessFn; infer_instance

/-- What initialization establishes: `itemLess` holds a function that behaves as
`Item.Less`. -/
def isInit : IProp GF :=
  iprop(∃ f : GoFunc, typedPointsto (globalAddr itemLess) f DFrac.discard ∗ isItemLessFn f)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.google.btree :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.google.btree :=
  build_get_is_pkg_init_wf

end init

end Btree
end EtcdGrove
end Perennial
