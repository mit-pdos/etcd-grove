/-
Lean-first (no Rocq counterpart). kvreconf's `kvr_ccAu` (`kvreconf/ClientAu.lean`), ported.

# The update `node.ProposeConfChange` takes (2026-11-01)

`kd_ccAu`: for a change `o` of a defined transition (`ccTransOk`), the persistent atomic update of
the committed log that `Reconfigure`'s proposals hand raft, from the store's invariant (`rkvInv`)
alone: a conf entry carries no datum, so the history stays (`kvreconf.logHist_conf`), and the
committed requested conf entries stay shaped (`kvreconf.confShaped_proposed`). `kd_ccAu_dup` is the
same at `□?γ.dup`, the form the spec takes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClientAu

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open kvreconf (ccTransOk logHist odOf)

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [AllG GF]

/-- **The update `node.ProposeConfChange` takes** for a change `o` of a defined transition (see
the file header). -/
theorem kd_ccAu (γ : KdNames) (o : ConfChangeIM) : ccTransOk o →
    rkvInv (GF := GF) γ ⊢
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ.r.cluster ops }>
          @ ⊤ \ ↑kdRaftN, ∅
        <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
             ownCommittedOps γ.r.cluster
               (ops ++ opsOf [(⟨t, confChangeEntryType (some o), bs⟩ : LogEntry)]),
           COMM True }> := by
  intro Hto
  iintro #Hinv
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj : (↑kdRkvN : CoPset) ⊆ ⊤ \ ↑kdRaftN :=
    mask_ndot_ne' nroot "kvdurable_rkv" "kvdurable_raft" (by decide)
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kdRaftN) \ ↑kdRkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hv HU Hn HMi HRS HRMi HO
      ipureintro; exact ⟨Hok, Hodm, Hsh⟩
    imodintro
    iempintro
  · iintro %t %bs ⟨%Hbs, Hops⟩
    imod Hclose2 with -
    have Hocc := kvreconf.logHist_conf ops o t bs
    imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
    · inext
      iexists ops ++ opsOf [⟨t, confChangeEntryType (some o), bs⟩], n, Mi, RS, RMi, O, U
      rw [Hocc]
      iframe Hsl
      unfold kvCore
      rw [Hocc]
      iframe Hops Hv HU Hn HMi HRS HRMi HO
      ipureintro
      refine ⟨Hok, fun d' h => ?_, ?_⟩
      · rw [List.map_append] at h
        rcases List.mem_append.mp h with h | h
        · exact Hodm d' h
        · cases kvreconf.odOf_conf_none o t bs _ h
      · intro e he hc
        rcases List.mem_append.mp he with h | h
        · exact Hsh e h hc
        · exact kvreconf.confShaped_proposed o t bs Hbs Hto e h hc
    imodintro
    itrivial

/-- `kd_ccAu` in the form `node.ProposeConfChange` takes it. -/
theorem kd_ccAu_dup (γ : KdNames) (o : ConfChangeIM) : ccTransOk o →
    rkvInv (GF := GF) γ ⊢
      □?γ.r.cluster.dup AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ.r.cluster ops }>
          @ ⊤ \ ↑kdRaftN, ∅
        <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
             ownCommittedOps γ.r.cluster
               (ops ++ opsOf [(⟨t, confChangeEntryType (some o), bs⟩ : LogEntry)]),
           COMM True }> := by
  intro Hto
  iintro #Hinv
  iapply intuitionisticallyIf_of_intuitionistically
  iapply kd_ccAu γ o Hto $$ Hinv

end lemmas

end kvdurable
end EtcdGrove
end Perennial
