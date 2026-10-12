/-
`idutil.Generator.Next()` (`id.go`): the next request id. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `g.Next()` (any goroutine), with one id credit, returns an id nobody holds (`idFresh`), of
the generator's shape: its prefix `pfx` and the 48 low bits of its initial suffix `s0` plus the
number `j` of ids issued so far, this one included. -/
abbrev idutil.Generator.Next.spec : Prop :=
  ∀ (γi : IdNames) (g : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idGen γi g ∗
      idCred γi 1 }}
    (App (Val (g @!! go.GoType.PointerType idutil.Generator.ty @!! go!"Next")) (Val #()))
  {{ (id : w64), RET #id; idFresh γi id ∗
      ∃ (pfx s0 : w64) (j : Nat),
        structFieldRef idutil.Generator go!"prefix" g ↦□ pfx ∗
        ⌜1 ≤ j ∧ j < 2 ^ 48 ∧ id = pfx ||| ((s0 + W64 (j : Int)) &&& W64 (2 ^ 48 - 1))⌝ }}

end spec

end EtcdGrove
end Perennial
