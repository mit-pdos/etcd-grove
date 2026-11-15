/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__NoSyncReload.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
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

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem Interface.NoSyncReload.wp_proof
    (hI : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.InitSpec) :
    Interface.NoSyncReload.spec (GF := GF) (hG := hG) := by
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

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
