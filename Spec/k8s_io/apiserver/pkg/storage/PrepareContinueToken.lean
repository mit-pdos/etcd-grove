/-
`storage.PrepareContinueToken(keyLastItem, keyPrefix, resourceVersion, itemsCount, hasMoreItems,
opts)` (`k8s.io/apiserver/pkg/storage/continue.go`), **for the k8s etcd3 driver's list options**
(`listOptsV x`, `examples/k8s/etcd3`'s `listOptions(in)`): with more items, the continue token
`encL` of `EncodeContinue(keyLastItem + "\x00"`'s caller-built key, the prefix and the revision
(an error iff `strings.TrimPrefix` leaves the key unchanged: `encOkL`; `json.Marshal` of the
token does not fail), and the remaining count `itemsCount - Limit` iff the predicate is empty
(`predEmptyL x`); with none, no token, no count and no error.

A hypothesis of the driver's `mlist` (k8s 7e-3b, Q7e-3b-2): not linked, no axiom; its statement
is 7e-2's Draft's to review (stated for the driver's options only; the general statement would
take the predicate's `Empty` spec). `encL` is opaque (Q7e-1). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open k8s_etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.PrepareContinueToken.spec : Prop :=
  ∀ (kl kp : GoString) (rv cnt : w64) (more : Bool)
    (x : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.PrepareContinueToken))
      (Val #kl)) (Val #kp)) (Val #rv)) (Val #cnt)) (Val #more)) (Val #(listOptsV x)))
  {{ (c : GoString) (rem : Loc) (err : GoInterface), RET (PairV (PairV #c #rem) #err);
      if more then
        (if encOkL (kl ++ [W8 0]) kp then
          ⌜err = GoInterface.nil ∧ c = encL (kl ++ [W8 0]) kp rv⌝ ∗
            (if predEmptyL x then rem ↦ (cnt - x.Limit') else ⌜rem = null⌝)
        else ⌜err ≠ GoInterface.nil⌝)
      else ⌜c = [] ∧ rem = null ∧ err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
