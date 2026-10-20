/-
Lean-first (no Rocq counterpart). (2026-10-20, witness support)

# The store's witness storage (`WitnessStore`, `witness.go`)

The in-process witness storage of a cluster with a witness (`StartClusterWitness`): the stored
state under a mutex. A stored state is never changed: an update stores the caller's new one, so
a read hands out the stored state and an update compares the one stored with the one read by
identity. What it implements is raft's storage contract (`isWitnessStorage`,
`Proof/go_etcd_io/raft/v3/InvWitnessStorage.lean`) for any ghost counterpart `P` of the stored
state: the lock invariant holds `P` of the state stored, read-only (`whsRO`), and a read's or
an update's view shift runs under the lock. Two read-only facts of one state agree
(`whsRO_agree`), which is what makes the comparison by identity a comparison of states.

`isWStore s P`: the store at `s`, its mutex's invariant, and the value of raft's
`ErrWitnessStateModified` (non-nil), which `Update` returns on a conflict. raft's package
initializer does not state that value yet (a fact of its own, as `ErrCompacted`'s, to come with
the proof of `witness.Process`), so it is a premise of the store's construction
(`NewWitnessStore`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs
public import Proof.go_etcd_io.raft.v3.InvWitnessStorage

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's witness storage struct and one read of it. -/
abbrev RWStore [FfiSyntax] := github_com.mit_pdos.etcd_grove.examples.kv.WitnessStore
abbrev RWRead [FfiSyntax] := github_com.mit_pdos.etcd_grove.examples.kv.witnessRead

abbrev rWStoreTy [FfiSyntax] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.WitnessStore.ty
abbrev rWReadTy [FfiSyntax] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.witnessRead.ty

section wstore
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Two read-only facts of one `*pb.HardState` agree. -/
theorem hsF_ro_agree (ps : Loc) (σ1 σ2 : WHS) :
    hsF (GF := GF) ps DFrac.discard σ1 ∗ hsF ps DFrac.discard σ2 ⊢
      ⌜σ1.term = σ2.term ∧ σ1.vote = σ2.vote ∧ σ1.commit = σ2.commit⌝ := by
  iintro ⟨H1, H2⟩
  iNamedSuffix H1 "1"
  iNamedSuffix H2 "2"
  icombine HT1 HT2 gives %HT
  icombine HV1 HV2 gives %HV
  icombine HC1 HC2 gives %HC
  subst HT HV HC
  ihave %Ht := cellRO_agree (GF := GF) pt σ1.term σ2.term $$ [cT1 cT2]
  · isplitl [] <;> iassumption
  ihave %Hv := cellRO_agree (GF := GF) pv σ1.vote σ2.vote $$ [cV1 cV2]
  · isplitl [] <;> iassumption
  ihave %Hc := cellRO_agree (GF := GF) pc σ1.commit σ2.commit $$ [cC1 cC2]
  · isplitl [] <;> iassumption
  ipureintro; exact ⟨Ht, Hv, Hc⟩

/-- Two read-only facts of one witness state agree: a stored state is one state for good. -/
theorem whsRO_agree (p : Loc) (σ1 σ2 : WHS) :
    whsRO (GF := GF) p σ1 ∗ whsRO p σ2 ⊢ ⌜σ1 = σ2⌝ := by
  iintro ⟨H1, H2⟩
  unfold whsRO whsF
  icases H1 with ⟨%ps1, HS1, Hhs1, Hr1⟩
  icases H2 with ⟨%ps2, HS2, Hhs2, Hr2⟩
  icombine HS1 HS2 gives %HS
  subst HS
  -- the hard state: both nil (zero) or both a read-only hard state
  ihave %Hh : ⌜σ1.term = σ2.term ∧ σ1.vote = σ2.vote ∧ σ1.commit = σ2.commit⌝ $$ [Hhs1 Hhs2]
  · unfold hsOptW
    icases Hhs1 with (%Hz1 | Hh1)
    · icases Hhs2 with (%Hz2 | Hh2)
      · ipureintro
        obtain ⟨-, a1, b1, c1⟩ := Hz1
        obtain ⟨-, a2, b2, c2⟩ := Hz2
        exact ⟨a1.trans a2.symm, b1.trans b2.symm, c1.trans c2.symm⟩
      · iNamed Hh2; exact absurd Hz1.1 Hsn
    · icases Hhs2 with (%Hz2 | Hh2)
      · iNamed Hh1; exact absurd Hz2.1 Hsn
      · iapply hsF_ro_agree $$ [Hh1 Hh2]
        iframe
  iunfold whsRest at Hr1
  iunfold whsRest at Hr2
  icases Hr1 with ⟨%pli, %plt, %pls, %pld, %srs, %sro, %uf1, Hr1⟩
  icases Hr2 with ⟨%pli2, %plt2, %pls2, %pld2, %srs2, %sro2, %uf2, Hr2⟩
  iNamedSuffix Hr1 "1"
  iNamedSuffix Hr2 "2"
  icombine HLi1 HLi2 gives %HLi
  icombine HLt1 HLt2 gives %HLt
  icombine HLs1 HLs2 gives %HLs
  icombine HLd1 HLd2 gives %HLd
  icombine HRs1 HRs2 gives %HRs
  icombine HRo1 HRo2 gives %HRo
  subst HLi HLt HLs HLd HRs HRo
  ihave %Hli := cellRO_agree (GF := GF) pli σ1.li σ2.li $$ [cLi1 cLi2]
  · isplitl [] <;> iassumption
  ihave %Hlt := cellRO_agree (GF := GF) plt σ1.lt σ2.lt $$ [cLt1 cLt2]
  · isplitl [] <;> iassumption
  ihave %Hls := cellRO_agree (GF := GF) pls σ1.ls σ2.ls $$ [cLs1 cLs2]
  · isplitl [] <;> iassumption
  ihave %Hld := cellRO_agree (GF := GF) pld σ1.lead σ2.lead $$ [cLd1 cLd2]
  · isplitl [] <;> iassumption
  ihave %Hrs := ownSlice_agree (GF := GF) srs DFrac.discard DFrac.discard σ1.rs σ2.rs $$ Hrs1 Hrs2
  ihave %Hro := ownSlice_agree (GF := GF) sro DFrac.discard DFrac.discard σ1.rsOut σ2.rsOut
    $$ Hro1 Hro2
  ipureintro
  obtain ⟨Ht, Hv, Hc⟩ := Hh
  cases σ1; cases σ2
  simp_all

variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- The store's lock invariant: the state stored, read-only, and its ghost counterpart. -/
def wStoreLock (s : Loc) (P : WHS → IProp GF) : IProp GF :=
  iprop(∃ (p : Loc) (σ : WHS), s.[RWStore, go!"state"] ↦ p ∗ whsRO p σ ∗ P σ)

/-- raft's `ErrWitnessStateModified` is a non-nil error. -/
def wErrOk : IProp GF :=
  iprop(∃ e : GoInterface, globalAddr ErrWitnessStateModified ↦□ e ∗ ⌜e ≠ interface.nil⌝)

instance wErrOk_persistent : Persistent (wErrOk (GF := GF)) := by
  unfold wErrOk; infer_instance

/-- raft's initialization gives `wErrOk` (its `#ErrWitnessStateModified`, 2026-10-20). -/
theorem wErrOk_of_init [go_etcd_io.raft.v3.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ⊢ wErrOk := by
  iintro #Hpkg
  ihave #Hi := isInitialized_access $$ Hpkg
  unfold isInitialized
  iNamed Hi
  icases ErrWitnessStateModified with ⟨%ew, #Hg, %Hne⟩
  unfold wErrOk
  iexists ew
  iframe Hg
  ipureintro; exact Hne.1

/-- The store at `s`, the ghost counterpart of its state `P`. -/
def isWStore (s : Loc) (P : WHS → IProp GF) : IProp GF :=
  iprop(sync.isMutex (s.[RWStore, go!"mu"]) (wStoreLock s P) ∗ wErrOk)

instance isWStore_persistent (s : Loc) (P : WHS → IProp GF) :
    Persistent (isWStore (GF := GF) s P) := by
  unfold isWStore; infer_instance

/-- One read `r` of the store `s`: the state `p` it saw, which held `σ`. -/
def isWRead (r s : Loc) (P : WHS → IProp GF) (p : Loc) (σ : WHS) : IProp GF :=
  iprop(r.[RWRead, go!"s"] ↦□ s ∗ r.[RWRead, go!"state"] ↦□ p ∗ whsRO p σ ∗ isWStore s P)

instance isWRead_persistent (r s : Loc) (P : WHS → IProp GF) (p : Loc) (σ : WHS) :
    Persistent (isWRead (GF := GF) r s P p σ) := by
  unfold isWRead; infer_instance

end wstore

end EtcdGrove
end Perennial
