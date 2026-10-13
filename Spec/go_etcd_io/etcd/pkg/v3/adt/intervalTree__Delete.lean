/-
`intervalTree.Delete` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`,
`Defs.lean`, `TreeDelete.lean`. Proved in unit 4c (`intervalTree__Delete.lean`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `t.Delete(ivl)`: an entry with the interval removed, if any (and whether there was one).
With equal intervals (the tree allows them), the entry removed is one of them, not necessarily
the first in order (`find`'s). The whole tree (fraction `1`). -/
abbrev adt.intervalTree.Delete.spec : Prop :=
  ∀ (t : Loc) (L : List adt.Entry) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvt t L 1 }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Delete"))
      (Val #(adt.affIvl b e)))
  {{ RET #(decide ((b, e) ∈ L.map Prod.fst));
      ∃ L' : List adt.Entry,
        ⌜if (b, e) ∈ L.map Prod.fst then
            ∃ (i : Nat) (z : adt.Entry), L[i]? = some z ∧ z.1 = (b, e) ∧ L' = L.eraseIdx i
          else L' = L⌝ ∗
        adt.ownIvt t L' 1 }}

end spec

end EtcdGrove
end Perennial
