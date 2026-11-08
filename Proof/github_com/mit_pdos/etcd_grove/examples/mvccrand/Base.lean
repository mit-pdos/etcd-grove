/-
The randomized tester of mvcc (`examples/mvccrand`, `notes/mvccrand.md`): its package fact.

`mvccrand` has two package variables, never written after its initializer: `keys`, the keys in
increasing order, and `extraEnds`, the range ends besides them. Its fact says each holds a read-only
slice of those strings. (Its initializer's proof, `Init.lean`, is `etc/gen-init.py`'s, which does not
list `mvccrand` yet: `notes/mvcc-migration/mvccrand.md`.) Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.mvccrand
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The tester's keys (`keys`), in increasing order. -/
def keyList : List GoString := [go!"a", go!"aa", go!"b", go!"ba", go!"c", go!"d"]

/-- The tester's extra range ends (`extraEnds`). -/
def extraEndList : List GoString := [go!"bb", go!"z"]

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact: its two variables hold read-only slices of `keyList` and `extraEndList`. -/
def mvccrandInit : IProp GF :=
  iprop((∃ ks : GoSlice, globalAddr keys ↦□ ks ∗ ks ↦*□ keyList) ∗
    (∃ es : GoSlice, globalAddr extraEnds ↦□ es ∗ es ↦*□ extraEndList))

instance mvccrandInit_persistent : Persistent (mvccrandInit (GF := GF)) := by
  unfold mvccrandInit; infer_instance

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand :=
  define_is_pkg_init mvccrandInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.mvccrand
end Perennial
