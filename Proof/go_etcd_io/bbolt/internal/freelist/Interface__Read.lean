/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Read.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Read
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Read

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

theorem Interface.Read.wp_proof
    (hI : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.InitSpec)
    (hIs : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.IsFreelistPage.spec
      (GF := GF) (hG := hG))
    (hIds : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.FreelistPageIds.spec
      (GF := GF) (hG := hG)) :
    Interface.Read.spec (GF := GF) (hG := hG) := by
  intro fli p pg dq Hfl Hsz Hcnt Hnd Hge Hp Hmax
  wp_start_folded as ⟨Hfl', Hpg⟩
  icases flPgOwn_open _ _ $$ Hfl' with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hInit := hI I a HI
  have Hinc : PgidsIncr (sortPgids (flIds pg)) := sortPgids_incr Hnd
  have Hperm := sortPgids_perm (flIds pg)
  have hofi : FLPg.ofInit (flIds pg) = { FLPg.empty with free := sortPgids (flIds pg) } := rfl
  have Hwf : ({ FLPg.empty with free := sortPgids (flIds pg) } : FLPg).WF := by
    have hp : ({ FLPg.empty with free := sortPgids (flIds pg) } : FLPg).pendingIds = [] := by
      simp [FLPg.pendingIds, FLPg.empty]
    refine ⟨?_, ?_, Hinc, ?_, ?_⟩
    · rw [FLPg.allIds, hp, List.append_nil]; exact Hinc.nodup
    · intro id hid
      rw [FLPg.allIds, hp, List.append_nil] at hid
      exact Hge id (Hperm.mem_iff.1 hid)
    · rw [FLPg.allIds, hp, List.append_nil]
      show (sortPgids (flIds pg)).length < _
      rw [Hperm.length_eq, flIds_length]; omega
    · intro t q h; simp [FLPg.empty] at h
  have hI' := HI
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.Read.wp_proof _ hInit hIs hIds s FLPg.empty p pg dq Hfl Hsz Hcnt Hp Hmax
      Hwf.wfw (Or.inr (by simp [FLPg.empty]))) $$ [Hsh Hown Hpg] as ⟨Hsh, Hown, Hpg⟩
    · iframe
      isplitl []
      · isimp only [arrayImpl, hashImpl]; iexact Hhdl
      iapply ownSh_w $$ Hsh
    iapply HΦ
    iframe Hpg
    rw [hofi]
    iapply flPgOwn_close _ a s _ _ hI' rfl
    isplitl []
    · isimp only [arrayImpl, hashImpl]; iexact Hhdl
    isplitl [Hown]
    · iExactEq Hown; first | rfl | simp [arrayImpl, hashImpl, FLPg.reload]
    iapply ownShW_wf _ _ _ Hwf
    iExactEq Hsh
    rfl)

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
