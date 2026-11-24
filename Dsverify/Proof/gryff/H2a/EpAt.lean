/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/EpAt.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: `epaxosOwn` at fixed witnesses (`epaxosOwnAt`)

A handler that loads an instance pointer, calls a helper that only reads the EPaxos state, and then
writes through the pointer needs the pointer map `M` to be the same before and after the call:
the helpers' internal specs take `epaxosOwnAt` (the body of `epaxosOwn` at given witnesses) and
give it back unchanged.
-/
module

public import Dsverify.Proof.gryff.H2.EpState

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- The witnesses of `epaxosOwn`. -/
structure EpW where
  ispS : GoSlice
  crtS : GoSlice
  c1S : GoSlice
  isp : List GoSlice
  msR : Loc
  pvtR : Loc
  cfs : List Loc
  M : GMap replica.Node Loc
  cu : GoArray w32 5
  pm : GMap w64 src.gryffproto.ValTag

/-- `epaxosOwn`'s body at the witnesses `W`. -/
def epaxosOwnAt (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) (W : EpW) : IProp GF :=
  iprop(h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
      h.[src.gryff.EPaxosRMWHandler, go!"noConflicts"] ↦□ false ∗
      h.[src.gryff.EPaxosRMWHandler, go!"InstanceSpace"] ↦□ W.ispS ∗ W.ispS ↦*□ W.isp ∗
      h.[src.gryff.EPaxosRMWHandler, go!"crtInstance"] ↦□ W.crtS ∗
      h.[src.gryff.EPaxosRMWHandler, go!"conflicts1"] ↦□ W.c1S ∗ W.c1S ↦*□ W.cfs ∗
      h.[src.gryff.EPaxosRMWHandler, go!"maxSeqPerKey1"] ↦□ W.msR ∗
      h.[src.gryff.EPaxosRMWHandler, go!"PrevValTag"] ↦□ W.pvtR ∗
      h.[src.gryff.EPaxosRMWHandler, go!"CommittedUpTo"] ↦ W.cu ∗
      W.crtS ↦* s.crtInstance ∗
      ghostMapAuth ρ.ptrs 1 W.M ∗
      ([∗map] n ↦ p ∈ W.M, ghostMapElem ρ.ptrs n
        (if committedOrExecuted s n then DFrac.discard else DFrac.own 1) p) ∗
      ([∗list] q ↦ sq ∈ W.isp, rowOwn W.M q sq) ∗
      instsRep ρ xs s W.M ∗
      ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (ρ.crt q) 1 (sint.Z (s.crt (rid32 q))).toNat) ∗
      ([∗list] q ↦ cr ∈ W.cfs, confRep cr (s.confAt q)) ∗ confRep W.msR s.maxSeqK0 ∗
      W.pvtR ↦$ W.pm ∗ epaxosRest h ∗
      ⌜epFacts xs s W.isp W.cfs W.M W.cu W.pm⌝)

theorem epaxosOwn_at (ρ : Repl2Names) (h r : Loc) (xs : XS) (s : RState) :
    epaxosOwn (GF := GF) ρ h r xs s ⊣⊢ ∃ W : EpW, epaxosOwnAt ρ h r xs s W := by
  constructor
  · iintro H
    icases (epaxosOwn_open ..).1 $$ H with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu, %pm, H⟩
    iexists ⟨ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm⟩
    unfold epaxosOwnAt; iexact H
  · iintro ⟨%W, H⟩
    iapply (epaxosOwn_open ..).2
    iexists W.ispS, W.crtS, W.c1S, W.isp, W.msR, W.pvtR, W.cfs, W.M, W.cu, W.pm
    unfold epaxosOwnAt; iexact H

end

end Perennial.gryff.replica2
