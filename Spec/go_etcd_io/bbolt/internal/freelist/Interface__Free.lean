/-
`Interface.Free` (bbolt/internal/freelist, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U2; used by U7 (`Bucket.free`), U8 (`node.free`), U9 (`node.spill`), U10 (`Commit`'s old freelist page). Proof:
`Proof/go_etcd_io/bbolt/internal/freelist/Interface__Free.lean` (a `sorry` until U2).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Freelist
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.Free(txid, p)` through the freelist interface (the writer side's part `flPgOwn`): the page
`p` (its header at any fraction) and its overflow pages are pending for `txid`
(`FLPg.freePages`). It panics on page 0 or 1, a page already free or pending, or (`Verify`) a
page `txid` allocated: excluded by `FLPg.canFree`.
Stated over `ifaceCall fli m`, what the call steps to (U2 fix, 2026-11-04: Go's `fl.M(args)`
resolves the interface value's dynamic method; `methods Interface.ty m` has no semantics). -/
abbrev Interface.Free.spec : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (txid : w64) (p : Loc) (hdr : Page) (dq : DFrac),
  fl.canFree txid hdr.id' (1 + hdr.overflow'.toNat) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      flPgOwn fli fl ∗ p ↦{dq} hdr }}
    (App (App (ifaceCall fli go!"Free") (Val #txid)) (Val #p))
  {{ RET #(); flPgOwn fli (fl.freePages txid hdr.id' (1 + hdr.overflow'.toNat)) ∗ p ↦{dq} hdr }}

end spec

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
