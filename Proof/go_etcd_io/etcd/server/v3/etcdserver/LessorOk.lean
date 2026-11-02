/-
The server's lessor contract (`lessorOk`: `Promote`, `Demote`, `ExpiredLeasesC`) of the real
lessor (2026-10-13, unit 9 of the backend). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.

`lessorOk_of_lessorInv`: the lessor at `lp` (`lease.lessorInv`, its configuration and its
`expiredC` at the server's grant guard, `lease.lessorExpiredC`, D19n, the lease-grant plan's D1)
meets `lessorOk`,
from the specs of `Promote` and
`Demote` (trust-boundary axioms: float arithmetic, a float-to-integer conversion and `sort.Sort`;
the close of `demotec`) and the proof of `ExpiredLeasesC`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Promote
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Demote
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__ExpiredLeasesC

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section bag
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- (review M1, 2026-11-02; a local workaround: a fact of Perennial's `isChanBag`, which has no
such law yet, `notes/perennial-changes.md`) The bag invariant is monotone in its payload. -/
theorem chanBagInv_mono (γ : ChanNames) (P Q : V → IProp GF) (h : ∀ v, P v ⊢ Q v) :
    chanBagInv γ P ⊢ chanBagInv γ Q := by
  unfold chanBagInv
  refine exists_mono fun s => sep_mono_right ?_
  cases s <;> first
    | exact .rfl
    | exact h _
    | exact BigSepL.bigSepL_mono_of_forall (fun {_ _} => h _)

/-- (review M1; local, as `chanBagInv_mono`) **A bag's payload may be replaced by an equivalent
one**. -/
theorem isChanBag_iff (γ : ChanNames) (ch : Loc) (P Q : V → IProp GF) (h1 : ∀ v, P v ⊢ Q v)
    (h2 : ∀ v, Q v ⊢ P v) : isChanBag γ ch P ⊢ isChanBag γ ch Q := by
  rw [isChanBag_unseal]; unfold isChanBagDef
  iintro ⟨#Hch, #Hinv⟩
  isplitr
  · iexact Hch
  iapply inv_iff $$ Hinv
  inext; imodintro
  isplit
  · iintro H; iapply (chanBagInv_mono γ P Q h1) $$ H
  · iintro H; iapply (chanBagInv_mono γ Q P h2) $$ H

end bag

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's lessor contract, of the real lessor** at `lp`, (its grant guard the server's,
`srvGrantGuard lg on`: the lease-grant plan's D1; until then `False`, D45): the guard refutes the
expired slices' payload, so the bag is of `False` (`isChanBag_iff`, review M1). -/
theorem lessorOk_of_lessorInv
    (hPromote : lease.lessor.Promote.spec (GF := GF) (hG := hG))
    (hDemote : lease.lessor.Demote.spec (GF := GF) (hG := hG))
    (hExp : lease.lessor.ExpiredLeasesC.spec (GF := GF) (hG := hG))
    (lp : Loc) (γl : GName) (lg on : Bool) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γl ∗ lease.lessorCfg lp ∗ lease.lessorExpiredC lp (srvGrantGuard lg on) ⊢
      lessorOk (lease.lessorIface lp) := by
  iintro ⟨#Hpkg, #Hinv, #Hcfg, #Hexp⟩
  iunfold lessorOk
  iexists (interface.mk (go.GoType.PointerType lease.lessor.ty) #lp)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %d %Φ !> - HΦ
    iapply (hPromote lp γl d) $$ [] HΦ
    iframe #
  isplitr
  · iintro !> %Φ !> - HΦ
    iapply (hDemote lp γl) $$ [] HΦ
    iframe #
  · iintro !> %Φ !> - HΦ
    iapply (hExp lp (srvGrantGuard lg on)) $$ []
    · iframe #
    iintro %c !> ⟨%γc, #Hb⟩
    iapply HΦ
    iexists γc
    iapply (isChanBag_iff γc c _ _ (fun _ => srvGrantGuard_expired lg on)
      (fun _ => false_elim)) $$ Hb

end proof

end EtcdGrove
end Perennial
