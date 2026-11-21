/-
`crc32.New(tab)` of a Castagnoli table (`crc32.go:146-151`; the table read-only for good, as
`MakeTable`'s): a fresh digest `&digest{0, tab}`, as a `hash.Hash32`. The table is not `IEEETable`
(the package's fact, `crc32Init`: that one holds the IEEE table), so `ieeeInitOnce` is not called.
Lean-first (prove-etcdint3, 2026-11-21).
-/
module

public import Proof.hash.crc32.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

/-- See the file header. -/
abbrev hash.crc32.New.spec : Prop :=
  ∀ (tab : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.hash.crc32 ∗ tab ↦□ hash.crc32.castagnoliTableArr }}
    (App (Val (@! hash.crc32.New)) (Val #tab))
  {{ (d : Loc), RET #(interface.mkOk (go.GoType.PointerType _root_.Perennial.hash.crc32.digest.ty) #d);
      d ↦ _root_.Perennial.hash.crc32.digest.mk (W32 0) tab }}

end spec

end EtcdGrove
end Perennial
