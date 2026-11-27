/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__reads.lean`: each read state is
reported (`read`), the first after the pending cause (`reportCause`), which is then cleared.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RangeRo
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

attribute [-instance] pure_wp_slice_for_range

/-- The reports still due before the `i`-th read state, with the cause `o'` still pending. -/
def readsLeft (γr : GName) (nm : AntCheck.Str) (rss : List ReadStateM) (i : Nat)
    (o' : Option AntCheck.Event) (Q : IProp GF) : IProp GF :=
  reports γr ((if rss = [] then [] else o'.toList).map (atNode nm)) (readsAfter γr nm (rss.drop i) Q)

theorem readsLeft_step (γr : GName) (nm : AntCheck.Str) (rss : List ReadStateM) (i : Nat)
    (o' : Option AntCheck.Event) (Q : IProp GF) (r : ReadStateM) (hr : rss[i]? = some r) :
    readsLeft γr nm rss i o' Q =
      reports γr (o'.toList.map (atNode nm))
        (iprop(⧗ 2 -∗ reports γr [atNode nm (readEvM r)] (readsLeft γr nm rss (i + 1) none Q))) := by
  have hi : i < rss.length := (List.getElem?_eq_some_iff.1 hr).1
  have hne : rss ≠ [] := by intro h; simp [h] at hi
  have hr' : rss[i] = r := (List.getElem?_eq_some_iff.1 hr).2
  unfold readsLeft
  rw [if_neg hne, if_neg hne, List.drop_eq_getElem_cons hi, hr']
  rfl

theorem node.reads.wp_proof (wp_reportCause : node.reportCause.spec (GF := GF) (hG := hG))
    (wp_emit : node.emit.spec (GF := GF) (hG := hG)) :
    node.reads.spec (GF := GF) (hG := hG) := by
  intro c γ n j rd rss cl o Q
  wp_start as ⟨#Hc, #Hn, Hok, #Hrs, Hcl, Hpc, Hrep⟩
  ihave #Hrs' := Hrs
  iunfold readStatesPts at Hrs'
  icases Hrs' with ⟨%vs, #Hvs, #Hb⟩
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  wp_auto
  wp_apply (wp_slice_range_ro (V := ReadState) _ rd.ReadStates' vs DFrac.discard _
    (fun i => iprop(∃ (cl' : Loc) (o' : Option AntCheck.Event) (v : ReadState),
      n_ptr ↦ n ∗ rs_ptr ↦ v ∗ emitOk n ∗ n.[H.node, go!"cause"] ↦ cl' ∗ pendingCause cl' o' ∗
      readsLeft γ.strm (AntSim.nameOf (AntSim.nodeId j)) rss i o' Q ∗
      ⌜(i = 0 → cl' = cl ∧ o' = o) ∧ (0 < i → cl' = null ∧ o' = none)⌝))) $$ Hvs [n rs Hok Hcl Hpc Hrep]
  · iexists cl, o, _
    rw [show readsLeft (GF := GF) γ.strm (AntSim.nameOf (AntSim.nodeId j)) rss 0 o Q =
      reports γ.strm ((if rss = [] then [] else o.toList).map (atNode (AntSim.nameOf (AntSim.nodeId j))))
        (readsAfter γ.strm (AntSim.nameOf (AntSim.nodeId j)) rss Q) by unfold readsLeft; rw [List.drop_zero]]
    iframe
    ipureintro; exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (Nat.lt_irrefl 0)⟩
  · imodintro
    iintro %i %x %hx ⟨%cl', %o', %v, n, rs, Hok, Hcl, Hpc, Hrep, %Hi⟩ Hvs
    have hi : i < rss.length := by have := (List.getElem?_eq_some_iff.1 hx).1; omega
    obtain ⟨r, hr⟩ : ∃ r, rss[i]? = some r := ⟨_, List.getElem?_eq_getElem hi⟩
    ihave ⟨%Hidx, #Hctx⟩ := BigSepL2.bigSepL2_lookup
      (Φ := fun _ v st => iprop(⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx')) hx hr $$ Hb
    rw [readsLeft_step _ _ rss i o' Q r hr]
    wp_take_receipt as Hr1
    wp_apply +noauto wp_reportCause c γ n j cl' o' _ $$ [$Hpkg $Hc $Hn $Hok $Hcl $Hpc $Hrep] as ⟨Hok, Hcl, Hrep⟩
    try wp_auto
    wp_apply +noauto wp_bytes_to_string x.RequestCtx' r.RequestCtx' DFrac.discard $$ [$Hctx] as -
    wp_take_receipt as Hr2
    ihave Hrep := Hrep $$ [Hr1 Hr2]
    · iapply (receipt_add (GF := GF) 1 1).2
      iframe Hr1 Hr2
    wp_apply wp_emit c γ n j _ (readEvM r) _ $$ [$Hpkg $Hc $Hn $Hok Hrep «$a0»] as ⟨Hok, Hrep⟩
    · iframe Hrep
      iunfold eventOwn
      iexists _
      iframe
      simp only [readEvM, AntCheck.fieldRO, AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.fieldRel]
      isplitr
      · ipureintro
        refine ⟨trivial, trivial, trivial, ?_⟩
        simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
          AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
          AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx, Hidx]
        decide
      simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
        AntCheck.fCause]
      ipureintro; decide
    try wp_auto
    isplitr
    · ipureintro; rfl
    iframe
    isplitr
    · iunfold pendingCause; ileft; ipureintro; exact ⟨rfl, rfl⟩
    ipureintro; exact ⟨fun h => absurd h (Nat.succ_ne_zero i), fun _ => ⟨rfl, rfl⟩⟩
  iintro ⟨%cl', %o', %v, n, rs, Hok, Hcl, Hpc, Hrep, %Hi⟩ Hvs
  try wp_auto
  iapply HΦ
  iframe Hok Hrs
  have hdrop : rss.drop vs.length = [] := by rw [Hl]; simp
  by_cases hr : rss = []
  · subst hr
    have hv : vs = [] := List.length_eq_zero_iff.1 (by simpa using Hl)
    subst hv
    obtain ⟨rfl, rfl⟩ := Hi.1 rfl
    rw [if_pos rfl]
    iframe Hcl Hpc
    rw [show readsLeft (GF := GF) γ.strm (AntSim.nameOf (AntSim.nodeId j)) [] [].length o' Q = Q by
      unfold readsLeft; simp [readsAfter, reports]]
    iexact Hrep
  · have hpos : 0 < vs.length := by
      rw [Hl]; exact List.length_pos_iff.2 hr
    obtain ⟨rfl, rfl⟩ := Hi.2 hpos
    rw [if_neg hr]
    iframe Hcl
    have : readsLeft (GF := GF) γ.strm (AntSim.nameOf (AntSim.nodeId j)) rss vs.length none Q = Q := by
      unfold readsLeft; rw [hdrop]; split <;> rfl
    rw [this]
    iexact Hrep

end proof

end AntHarness
end EtcdGrove
end Perennial
