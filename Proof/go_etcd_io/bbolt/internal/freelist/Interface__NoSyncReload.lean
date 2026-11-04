/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__NoSyncReload.lean` (U2, `notes/bbolt-proof-plan.md`): `wp_proof'`, of `spec'`, the spec over the call a caller reaches (`ifaceCall`, `Lemmas/IfaceCall.lean`: the frozen spec's expression is unreachable) with the premises it lacks; `wp_proof` stays `sorry` until the frozen spec is restated.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__NoSyncReload
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__NoSyncReload

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The spec over the call a caller reaches, with three more premises than the frozen spec,
which is false without them: the ids are pages (at least 2) and not too many with the pending
ones (else the result is not `FLPg.WF`, which `flPgOwn` requires), and some id is left or no id
was free (`hashMap.Init` of no ids returns before `reindex`, keeping the old cache: the old free
ids would stay cached). -/
abbrev Interface.NoSyncReload.spec' : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (s : GoSlice) (ids : List w64) (dq : DFrac),
  PgidsIncr ids → (∀ x ∈ ids, 2 ≤ x.toNat) → ids.length + fl.pendingIds.length < 2 ^ 63 →
  ((fl.noSyncReload ids).free ≠ [] ∨ fl.free = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      s ↦*{dq} ids }}
    (App (ifaceCall fli go!"NoSyncReload") (Val #s))
  {{ RET #(); flPgOwn fli (fl.noSyncReload ids) ∗ s ↦*{dq} ids }}

theorem Interface.NoSyncReload.wp_proof'
    (hI : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.InitSpec) :
    Interface.NoSyncReload.spec' (GF := GF) (hG := hG) := by
  intro fli fl sl ids dq Hinc Hge Hlen Hemp
  wp_start_folded as ⟨Hfl, Hs⟩
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hInit := hI I a HI
  have Hemp' : ids.filter (fun x => decide (x ∉ fl.pendingIds)) ≠ [] ∨
      ∀ x ∈ fl.free, x ∈ fl.pendingIds := by
    rcases Hemp with h | h
    · left; rw [← reload_free (fl := fl) Hinc]; exact h
    · right; simp [h]
  have hI' := HI
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.NoSyncReload.wp_proof _ hInit s fl sl ids dq (sl ↦*{dq} ids) Hinc Hge Hlen
      Hemp') $$ [Hsh Hown Hs] as ⟨Hsh, Hown, Hs⟩
    · iframe
      isplitl []
      · isimp only [arrayImpl, hashImpl]; iexact Hhdl
      isplitl [Hsh]
      · iapply ownSh_w $$ Hsh
      iintro Hs
      iframe
    iapply HΦ
    iframe Hs
    iapply flPgOwn_close _ a s _ _ hI' rfl
    isplitl []
    · isimp only [arrayImpl, hashImpl]; iexact Hhdl
    isplitl [Hown]
    · isimp only [arrayImpl, hashImpl, FLPg.noSyncReload, FLPg.reload]
      iExactEq Hown
      simp
    rw [show fl.noSyncReload ids = fl.reload ids from rfl]
    iexact Hsh)

theorem Interface.NoSyncReload.wp_proof : Interface.NoSyncReload.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
