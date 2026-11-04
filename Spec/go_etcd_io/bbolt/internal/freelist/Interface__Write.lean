/-
`Interface.Write` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U10 (`commitFreelist`). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__Write.lean` (a `sorry` until U2).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Freelist
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.Write(p)`: the freelist page at `p` (its header, and the `R` zeroed bytes after it, at
least `EstimatedWritePageSize() - 16`): the header's flags the freelist's, its count the number
`n` of free and pending ids (`0xFFFF` from there on, the count then the first id after the
header), and the ids, sorted, after it (`flIds` reads them back).
Stated over `ifaceCall fli m`, what the call steps to (U2 fix, 2026-11-04: Go's `fl.M(args)`
resolves the interface value's dynamic method; `methods Interface.ty m` has no semantics). -/
abbrev Interface.Write.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (p : Loc) (hdr : Page) (R : Nat),
  8 * (fl.allIds.length + 1) ≤ R → 0 < p.addr → p.addr + 16 + R ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) (List.replicate R (W8 0)) }}
    (App (ifaceCall fli go!"Write") (Val #p))
  {{ RET #(); flPgOwn fli fl ∗
      let n := fl.allIds.length
      let body := (if n < 0xFFFF then [] else encode (W64 (n : Int))) ++
        (sortPgids fl.allIds).flatMap encode
      iprop(p ↦ (⟨hdr.id', W16 (freelistPageFlag : Int),
                     W16 ((if n < 0xFFFF then n else 0xFFFF : Nat) : Int), hdr.overflow'⟩ : Page) ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1) (body ++ List.replicate (R - body.length) (W8 0))) }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
