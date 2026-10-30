module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The `count` field of a freelist page of `n` ids (`0xFFFF`: the count is the first id's
cell). -/
def flCount (n : Nat) : w16 := if n = 0 then W16 0 else if n < 65535 then W16 (n : Int) else W16 65535

/-- The number of `Pgid` cells after a freelist page's header (`EstimatedWritePageSize`). -/
def flCells (n : Nat) : Nat := if 65535 ≤ n then n + 1 else n

/-- `t.Write(p)`: `p` becomes a freelist page of the free and pending ids, sorted (after the
count, if there are `0xFFFF` or more), over the `Pgid` cells after its header. -/
abbrev shared.Write.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) (p : Loc)
    (pv : go_etcd_io.bbolt.internal.common.Page) (old : List w64),
  I.FreeCountSpec → I.FreePageIdsSpec → p.locCar ≠ 0 → old.length = flCells σ.allIds.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShared s I.iface σ ∗ I.own s σ.free ∗ p ↦ pv ∗
      slice.mk (p +ₗ 16) (W64 (old.length : Int)) (W64 (old.length : Int)) ↦* old }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"Write")) (Val #p))
  {{ (out : List w64), RET #(); ⌜PgidsSorted out ∧ out.Perm σ.allIds⌝ ∗
      ownShared s I.iface σ ∗ I.own s σ.free ∗
      p ↦ ({ pv with flags' := W16 16, count' := flCount σ.allIds.length } :
        go_etcd_io.bbolt.internal.common.Page) ∗
      slice.mk (p +ₗ 16) (W64 (old.length : Int)) (W64 (old.length : Int)) ↦*
        (if 65535 ≤ σ.allIds.length then W64 (σ.allIds.length : Int) :: out else out) }}

end spec

end bbolt
end EtcdGrove
end Perennial
