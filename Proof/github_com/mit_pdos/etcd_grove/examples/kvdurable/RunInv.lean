/-
Lean-first (no Rocq counterpart).

# kvdurable `run`'s loop invariant (2026-11-01, stage II (j))

kvreconf's (`kvreconf/RunInv.lean`) with the durable part: the loop's driver at the delivered log
`D`, the hard state `hd` (the Go variable `hs` points to it) and the durable state `S`; `run`'s half
of `nodeRunning`, its claim on the pending batch at `(none, S)` (no batch pending between `Ready`s)
and its half of the image's hard state at `hd` (G12), whose term and vote are `S`'s. The replicated
state `ap` may be ahead of `D` after a restart below the snapshot (then `snapIndex` is at least
`len ap`); the applier's view is at `D` when `ap` is as long, else the node's configuration stays at
`len ap` (G22: the covered entries leave it alone). `lead` is set only at role leader. The
delivered log is frozen above the known compaction point `c` and at most the image's frozen bound.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.RunLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- **`run`'s loop invariant** (see the file header); `pp`, `lp`, `sp`, `hp`, `rp` its `pending`,
`lead`, `snapIndex`, `hs` and `rafted`. -/
def runInv (γ : KdNames) (r n st : Loc) (ρ : KdRepNames) (pp lp sp hp rp : Loc) : IProp GF :=
  iprop(∃ (D : List LogEntry) (hd : HardStateM) (S : RaftState) (role : StateType)
      (ap : List LogEntry) (csp mA : Loc) (m : Membership) (A : GMap (List w8) (List w8))
      (snapIndex rafted : w64) (c : Nat) (pv : GoSlice) (ps : List ReadState) (lead : Bool) (hsp : Loc),
    "Hdrv" ∷ nodeDriver n γ.r.cluster kdRaftN
      { storage := kdStorIface st, delivered := D, hardState := hd, handling := none,
        key := ρ.key, durable := S, role := role } ∗
    "Hrun" ∷ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
    "Hclaim" ∷ ghostVar ρ.ph.ph (1 : Qp).half ((none : Option GName), S) ∗
    "Hcmh" ∷ ghostVar ρ.ph.cm (1 : Qp).half hd ∗
    "%Htie" ∷ ⌜S.term = hd.Term' ∧ S.vote = hd.Vote'⌝ ∗
    "Hprod" ∷ handoffProducer ρ.rd false ∗
    "Hown" ∷ repOwn γ r ap (W64 ap.length) csp m mA A ∗
    -- (G22) the applier's view: at `D` once the replicated state is `D`'s length, or, while it is
    -- ahead (after a restart below the snapshot), the node's configuration at `len ap` itself
    "Hview" ∷ ((⌜D.length = ap.length⌝ ∗ appNode γ n D D.length m) ∨
      (⌜D.length < ap.length⌝ ∗ nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩ ∗
        deliveredLogLb n γ.r.cluster kdRaftN D)) ∗
    "snapIndex" ∷ sp ↦ snapIndex ∗
    "rafted" ∷ rp ↦ rafted ∗
    "hs" ∷ hp ↦ hsp ∗
    "#HhsO" ∷ hsOpt hsp hd ∗
    "lead" ∷ lp ↦ lead ∗
    "#Hcp" ∷ memCompacted ρ.γs c ∗
    "#Hfz" ∷ kvreconf.frozenTo ρ.γs c D ∗
    "#Hicl" ∷ monoNatLbOwn ρ.ph.ic D.length ∗
    "%Hsi" ∷ ⌜(lead = true → role = StateLeader) ∧ c ≤ uint.nat snapIndex ∧ c ≤ D.length ∧
      uint.nat rafted = D.length ∧ (ap.length ≤ uint.nat snapIndex ∨ ap.length ≤ D.length)⌝ ∗
    "pending" ∷ pp ↦ pv ∗
    "Hpv" ∷ pv ↦* ps ∗
    "Hpcap" ∷ ownSliceCap ReadState pv (DFrac.own 1) ∗
    "#Hps" ∷ [∗list] v ∈ ps, rsOk γ.r.cluster v)

/-- `skippedIn` over a shorter range. -/
theorem skippedIn_shrink (γc : Cluster) (l : List LogEntry) (a b b' : Nat) (h : b' ≤ b) :
    skippedIn (GF := GF) γc l a b ⊢ skippedIn γc l a b' := by
  unfold skippedIn
  iintro #H
  have hr : List.range' a (b - a) = List.range' a (b' - a) ++ List.range' (a + (b' - a)) (b - a - (b' - a)) := by
    rw [show a + (b' - a) = a + 1 * (b' - a) by omega, List.range'_append]; congr 1; omega
  rw [hr]
  ihave ⟨#H1, -⟩ := (BigSepL.bigSepL_append (Φ := fun _ j => iprop(∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ →
    confDecided (GF := GF) γc j ConfDecision.skip))).1 $$ H
  iexact H1

/-- The invariant at the start (`runStart`: the node as `RestartNode` left it, `pending` nil, `lead`
false). -/
theorem runInv_init (γ : KdNames) (id : w64) (r n st : Loc) (ρ : KdRepNames) (l ap : List LogEntry)
    (hs : HardStateM) (S : RaftState) (m : Membership) (pp lp sp hp rp hsp : Loc)
    (snapIndex rafted : w64) (Hraf : uint.nat rafted = l.length)
    (Hsi : ap.length ≤ uint.nat snapIndex ∨ snapIndex = W64 ap.length) :
    runStart (GF := GF) γ id r n st ρ l hs S ap m ∗ pp ↦ slice.nil ∗ lp ↦ false ∗ sp ↦ snapIndex ∗
      hp ↦ hsp ∗ hsOpt hsp hs ∗ rp ↦ rafted ⊢
      runInv γ r n st ρ pp lp sp hp rp := by
  iintro ⟨Hs, Hpp, Hlp, Hsp, Hhp, #HhsO, Hrp⟩
  iunfold runStart at Hs
  icases Hs with ⟨%csp, %mA, %A, Hdrv, Hcfg, Hrun, Hown, Hprod, Hclaim, Hcmh, %Htie, %Hla,
    ⟨%c, #Hcp, #Hfz, %Hc⟩, #Hicl⟩
  ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
  ihave %Hap61 : ⌜(ap.length : Int) < 2 ^ 61⌝ $$ [Hown]
  · iunfold repOwn at Hown; iNamed Hown; ipureintro; exact Hlen
  unfold runInv
  iexists l, hs, S, StateFollower, ap, csp, mA, m, A, snapIndex, rafted, c, slice.nil, [], false, hsp
  iframe Hdrv Hrun Hclaim Hcmh Hprod Hown Hsp Hrp Hhp HhsO Hlp Hcp Hfz Hicl Hpp
  isplitr
  · ipureintro; exact Htie
  isplitl [Hcfg]
  · rcases Nat.lt_or_eq_of_le Hla with hlt | heq
    · iright
      iframe Hcfg Hdl
      ipureintro; exact hlt
    · ileft
      isplitr
      · ipureintro; exact heq
      iapply appNode_snap γ n l ap.length m heq $$ [$Hcfg $Hdl]
  isplitl []
  · ipureintro
    have Hsi' : ap.length ≤ uint.nat snapIndex := by
      rcases Hsi with h | h
      · exact h
      · rw [h]; word
    exact ⟨fun h => absurd h (by decide), by omega, Hc, Hraf, Or.inl Hsi'⟩
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  iapply BigSepL.bigSepL_nil.2
  itrivial

end inv

end kvdurable
end EtcdGrove
end Perennial
