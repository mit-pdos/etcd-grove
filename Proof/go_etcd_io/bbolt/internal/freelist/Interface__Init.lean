/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Init.lean` (U2, `notes/bbolt-proof-plan.md`): `wp_proof'`, of `spec'`, the spec over the call a caller reaches (`ifaceCall`, `Lemmas/IfaceCall.lean`: the frozen spec's expression is unreachable); `wp_proof` stays `sorry` until the frozen spec is restated.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Init
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall

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

abbrev Interface.Init.spec' : Prop :=
  ∀ (fli : GoInterface) (s : GoSlice) (ids : List w64),
  PgidsIncr ids → (∀ x ∈ ids, 2 ≤ x.toNat) → ids.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      flPgOwn fli FLPg.empty ∗ s ↦* ids ∗ ownSliceCap w64 s (DFrac.own 1) }}
    (App (ifaceCall fli go!"Init") (Val #s))
  {{ RET #(); flPgOwn fli (FLPg.ofInit ids) }}

theorem Interface.Init.wp_proof'
    (hI : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.InitSpec) :
    Interface.Init.spec' (GF := GF) (hG := hG) := by
  intro fli sl ids Hinc Hge Hlen
  wp_start_folded as ⟨Hfl, Hs, Hcap⟩
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hofi : FLPg.ofInit ids = { FLPg.empty with free := ids } := by
    simp [FLPg.ofInit, sortPgids_of_incr Hinc]
  have hwf : ({ FLPg.empty with free := ids } : FLPg).WF := by
    refine ⟨?_, ?_, Hinc, ?_, ?_⟩ <;>
      simp [FLPg.allIds, FLPg.pendingIds, FLPg.empty, Hinc.nodup, Hlen] <;> first | exact Hge | skip
  rw [ifaceCall_impl]
  iapply (hI I a HI s FLPg.empty sl ids hwf.wfw (Or.inr (by simp [FLPg.empty])))
    $$ [Hown Hsh Hs Hcap]
  · iframe
    isplitl []
    · iPkgInit
    isplitl []
    · iexact Hhdl
    iapply ownSh_w $$ Hsh
  inext
  iintro ⟨Hsh, Hown⟩
  iapply HΦ
  rw [hofi]
  iapply flPgOwn_close _ a s _ _ HI rfl
  iframe
  isplitl []
  · iexact Hhdl
  iapply ownShW_wf _ _ _ hwf $$ Hsh

theorem Interface.Init.wp_proof : Interface.Init.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
