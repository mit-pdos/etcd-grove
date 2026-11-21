/- Prefixes retained by appendEntries are shared with previously delivered Ready batches. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The third index in `r[:n:n]` gives the writer a prefix with no writable slack.
The old Ready can continue reading every run, including the discarded suffix. -/
theorem replayTerms_prefix (r : GoSlice) (runs : List replayTermRun) (n : w64)
    (hn : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z r.len) :
    let out := slice.fullSlice r replayTermRun (W64 0) n n
    (r ↦*□ runs : IProp GF) ⊢ out ↦*□ runs.take (sint.nat n) ∗
      ownSliceCap replayTermRun out (DFrac.own 1) := by
  dsimp only
  iintro #Hr
  isplitr
  · icases (ownSlice_slice n n r DFrac.discard runs ⟨hn.1, Int.le_refl _, hn.2⟩).1 $$ Hr with ⟨Hpre, -, -⟩
    rw [ownSlice_unseal]; unfold ownSliceDef
    icases Hpre with (%Hnil | ⟨Harr, -⟩)
    · ileft; ipureintro
      obtain ⟨hp, hlen, _⟩ := (slice_mk_eq_nil ..).mp Hnil.1
      exact ⟨(slice_mk_eq_nil ..).mpr ⟨hp, hlen, hlen⟩, Hnil.2⟩
    · iright; isplitl [Harr]
      · iExactEq Harr; rfl
      · ipureintro; exact Int.le_refl _
  · iapply ownSliceCap_empty _ rfl (by dsimp [slice.fullSlice]; word)

/-- A Ready with no new entries returns exactly the existing slice, for any receiver. -/
theorem replayTerms.appendEntries_empty (r ents : GoSlice) (hempty : ents.len = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
      (App (Val (r @!! replayTerms.ty @!! go!"appendEntries")) (Val #ents))
    {{ RET #r; True }} := by
  wp_start
  (try wp_auto)
  simp only [hempty, decide_true]
  (try wp_auto)
  iapply HΦ; itrivial

end EtcdGrove
end Perennial
