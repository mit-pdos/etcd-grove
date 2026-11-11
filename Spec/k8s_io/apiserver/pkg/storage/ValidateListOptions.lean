/-
`storage.ValidateListOptions(keyPrefix, versioner, opts)` (`k8s.io/apiserver/pkg/storage/interfaces.go:372-410`)
of options with no continue token, a resource version the versioner parses as `n`, and a match among
`""`, `NotOlderThan`, `Exact`: the revision the list reads (`listRevL`: `n` for `Exact`, and for the
legacy match when recursive with a limit and `n > 0`; else `0`, the latest), no continue key, no
error. (An empty resource version returns `0` without parsing; it parses as `0`, `parse_empty`, and
`listRevL` of `0` is `0`.) Proved from the translated body (stage 7e-2, `notes/k8s-7e-2-draft.md`
§4.1). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.ValidateListOptions.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (kp : GoString) (vi : GoInterfaceOk)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (n : w64),
  opts.Predicate'.Continue' = [] → S.parseRV opts.ResourceVersion' = some n →
  opts.ResourceVersionMatch' ∈ [[], go!"NotOlderThan", go!"Exact"] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ versionerOk S vi }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.ValidateListOptions)) (Val #kp))
      (Val #(GoInterface.ok vi))) (Val #opts))
  {{ RET (PairV (PairV #(listRevL opts.ResourceVersionMatch' opts.Recursive' opts.Predicate'.Limit' n)
      #([] : GoString)) #GoInterface.nil); True }}

end spec

end EtcdGrove
end Perennial
