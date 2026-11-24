/-
`typedNilString(x)` (`examples/specreq/reflect/typednil.go`, the recover branch of zap's
`encodeStringer`: `v.Kind() == reflect.Pointer && v.IsNil()` of `v := reflect.ValueOf(x)`): of an
interface holding a pointer `p : *T`, `("<nil>", true)` if `p` is nil, else `("", false)`; of an `int`,
`("", false)` (its `Kind` is `Int`, so `IsNil` is not called). Lean-first (no Rocq counterpart);
reflect S0.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace specreq_reflect

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.specreq.reflect

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Assumptions]

/-- `typedNilString` of an interface holding the pointer `p : *T`. -/
abbrev typedNilString.spec : Prop :=
  ∀ (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.specreq.reflect }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.specreq.reflect.typedNilString)) (Val #(interface.mkOk (go.PointerType T) #p)))
  {{ RET (PairV #(if p = null then go!"<nil>" else go!"") #(decide (p = null))); True }}

/-- `typedNilString` of an `int`. -/
abbrev typedNilString.spec_int : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.specreq.reflect }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.specreq.reflect.typedNilString)) (Val #(interface.mkOk go.int #n)))
  {{ RET (PairV #(go!"") #false); True }}

end spec

end specreq_reflect
end EtcdGrove
end Perennial
