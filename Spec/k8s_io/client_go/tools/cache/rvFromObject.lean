/-
`rvFromObject(obj)` (`thread_safe_store.go:417`): the object's resource version, through
`meta.Accessor`. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `rvFromObject(o)` on an object meeting `OK`: `rvOf o` and no error, or `""` and an error if it
has none (the accessor's contract, `rvAcc`). -/
abbrev rvFromObject.spec : Prop :=
  ∀ (OK : GoInterface → IProp GF) (rvOf : GoInterface → Option GoString) (o : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ rvAcc OK rvOf ∗ □ OK o }}
    (App (Val (@! rvFromObject)) (Val #o))
  {{ (rv : GoString) (err : GoInterface), RET (PairV #rv #err);
      ⌜match rvOf o with
        | some r => rv = r ∧ err = interface.nil
        | none => rv = [] ∧ err ≠ interface.nil⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
