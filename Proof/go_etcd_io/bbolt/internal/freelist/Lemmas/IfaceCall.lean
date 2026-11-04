/-
The expression a call through the freelist interface steps to (U2, `notes/bbolt-proof-plan.md`).

**Spec defect (U0b's `Spec/go_etcd_io/bbolt/internal/freelist/Interface__*.lean`).** The frozen
specs are stated over `#(methods Interface.ty m #fli)`, the method `m` of the *interface type*
applied to the interface value. No program reaches that expression and it has no semantics: Go's
`fl.M(args)` on an interface `fl` is translated as `MethodResolve Interface.ty "M" fl`, which steps
(`go.InterfaceSemantics.method_interface_ok`) to a `match` on the interface value, `nil` panicking
and `ok i` giving `#(methods i.ty "M" i.v)` (the dynamic type's method), and `methods` of an
interface type has no `MethodUnfold`. So the frozen specs can neither be proved nor applied by
their callers. U2 proves each spec with the expression replaced by `ifaceCall fli m` (what a
caller's `wp_auto` leaves after loading the interface value), and the rest unchanged.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- `fli.m`, a method value of the freelist interface value `fli`: the dynamic type's method
(`nil` panics). -/
abbrev ifaceCall [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (fli : GoInterface)
    (m : GoString) : Expr :=
  match fli with
  | GoInterface.nil => Panic "nil interface"
  | GoInterface.ok i => Val #(methods i.ty m i.v)

end bbolt
end EtcdGrove
end Perennial
