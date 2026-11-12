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
caller's `wp_auto` leaves after loading the interface value), and the rest unchanged; since the
2026-11-04 fix the frozen specs are those.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode

-- `ifaceCall` is in `Inv/Freelist.lean` (shared: the interface specs are stated over it).

theorem ifaceCall_impl [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    {GF : BundledGFunctors} [HeapGS hlc GF] [go.Semantics]
    [go_etcd_io.bbolt.internal.freelist.Assumptions] (I : FLImpl (GF := GF)) (m : GoString) :
    ifaceCall I.iface m = Val #(methods I.ity m I.iv) :=
  rfl

theorem ifaceCall_array [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    {GF : BundledGFunctors} [HeapGS hlc GF] [go.Semantics]
    [go_etcd_io.bbolt.internal.freelist.Assumptions] (a : Loc) (m : GoString) :
    ifaceCall (FLImpl.iface (arrayImpl (GF := GF) a)) m =
      Val #(methods (go.GoType.PointerType go_etcd_io.bbolt.internal.freelist.array'.ty) m #a) :=
  rfl

theorem ifaceCall_hash [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    {GF : BundledGFunctors} [HeapGS hlc GF] [go.Semantics]
    [go_etcd_io.bbolt.internal.freelist.Assumptions] (a : Loc) (m : GoString) :
    ifaceCall (FLImpl.iface (hashImpl (GF := GF) a)) m =
      Val #(methods (go.GoType.PointerType go_etcd_io.bbolt.internal.freelist.hashMap.ty) m #a) :=
  rfl

/-- Step a call `ifaceCall I.iface m` of an implementation (`arrayImpl a`/`hashImpl a`) into the
promoted `shared` method: unfold the implementation's method, load its `shared` pointer (its
`hdl`, `Hhdl`), and resolve `(*shared).m`. -/
macro "iface_dispatch" : tactic => `(tactic| (
  first | rw [ifaceCall_array] | rw [ifaceCall_hash]
  wp_method_call
  wp_pure
  wp_pure
  wp_pure
  wp_load
  wp_pure))

end bbolt
end EtcdGrove
end Perennial
