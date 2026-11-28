/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__applyCommitted.lean`: committed
entries are reported (`apply`) after the pending cause (`reportCause`), each switches the
configuration (a normal entry: nothing), and the applied index is the last one's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RangeRo
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__applyCommitted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__switchConf
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
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

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

attribute [-instance] pure_wp_slice_for_range

theorem last_idx (len : w64) (k : Nat) (h1 : k + 1 = sint.nat len) (h2 : 0 ≤ sint.Z len) :
    (sint.Z (len - W64 1)).toNat = k ∧ sint.Z (len - W64 1) < sint.Z len ∧ 0 ≤ sint.Z (len - W64 1) := by
  word

theorem node.applyCommitted.wp_proof (wp_reportCause : node.reportCause.spec (GF := GF) (hG := hG))
    (wp_emit : node.emit.spec (GF := GF) (hG := hG)) (wp_entries : node.entries.spec (GF := GF) (hG := hG))
    (wp_switchConf : node.switchConf.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    node.applyCommitted.spec (GF := GF) (hG := hG) := by
  intro c γ n j by_ sl dq els es a cl o Q hn
  wp_start as ⟨#Hc, #Hn, Hok, Hsl, #Hents, Ha, Hcl, Hpc, Hrep⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hents
  ihave %Hsll := ownSlice_len $$ Hsl
  wp_auto
  cases es with
  | nil =>
    have H0 : sl.len = W64 0 := by
      have h1 := Hsll.1; simp only [List.length_nil] at Hl; rw [Hl] at h1; word
    rw [decide_eq_true H0]
    wp_auto
    iapply HΦ
    repeat rw [if_pos rfl]
    iframe
    iframe Hents
    iapply (show reports (GF := GF) γ.strm (List.map (atNode (AntSim.nameOf (AntSim.nodeId j))) []) Q ⊢ Q
      from .rfl)
    iexact Hrep
  | cons e r =>
    obtain ⟨l, ls, rfl⟩ : ∃ l ls, els = l :: ls := by
      cases els with
      | nil => simp at Hl
      | cons l ls => exact ⟨l, ls, rfl⟩
    have H0 : sl.len ≠ W64 0 := by
      have h1 : sint.nat sl.len ≠ 0 := by rw [← Hsll.1]; simp
      intro h; apply h1; rw [h]; rfl
    rw [decide_eq_false H0]
    simp only [List.cons_ne_nil, ↓reduceIte]
    wp_auto
    wp_apply wp_reportCause c γ n j cl o _ $$ [$Hpkg $Hc $Hn $Hok $Hcl $Hpc $Hrep] as ⟨Hok, Hcl, Hrep⟩
    try wp_auto
    ihave ⟨#He, #Hr⟩ := BigSepL2.bigSepL2_cons $$ Hents
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
      have h1 := Hsll.1; simp only [List.length_cons] at h1; constructor <;> word
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply +noauto wp_load_slice_index sl (sint.Z (W64 0)) (l :: ls) dq l (by decide) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rfl
    wp_take_receipt as Hr1
    wp_apply +noauto wp_GetIndex.1 l DFrac.discard e $$ [$Hpb $He] as -
    wp_take_receipt as Hr2
    ihave #Hc' := Hc
    iunfold antCluster at Hc'
    icases Hc' with ⟨%cfg, %rr, %ns, %stop, -, -, -, -, -, #Hro, -⟩
    iunfold clusterRO at Hro
    icases Hro with ⟨%nsl, %ivl, -, -, -, #Hmd, -⟩
    ihave #Hn' := Hn
    iunfold nodeRO at Hn'
    icases Hn' with ⟨%ch, %d, #Hnc, -⟩
    wp_apply +noauto wp_entries c n γ.mode sl dq (l :: ls) (e :: r) hn $$ [$Hpkg $Hnc $Hmd $Hsl $Hents]
      as %out ⟨Hsl, -, #Hlog, Hr3⟩
    ihave Hrep := Hrep $$ [Hr1 Hr2 Hr3]
    · iapply (receipt_add (GF := GF) ((e :: r).length + 1) 1).2
      iframe Hr2
      iapply (receipt_add (GF := GF) (e :: r).length 1).2
      iframe Hr3 Hr1
    try wp_auto
    wp_apply wp_emit c γ n j _ (applyEvM by_ (e :: r)) _ $$ [$Hpkg $Hc $Hn $Hok Hrep «$a0»] as ⟨Hok, Hrep⟩
    · iframe Hrep
      iunfold eventOwn
      iexists _
      iframe
      simp only [applyEvM, firstIdx, List.head?_cons, Option.map_some, Option.getD_some, AntCheck.fieldRO,
        AntCheck.fieldIs, AntCheck.fieldZ, AntCheck.fieldRel]
      isplitr
      · ipureintro
        refine ⟨trivial, trivial, trivial, ?_⟩
        simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
          AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
          AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
        decide
      simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
        AntCheck.fCause]
      iframe Hlog
      ipureintro; decide
    try wp_auto
    wp_apply (wp_slice_range_ro (V := Loc) _ sl (l :: ls) dq _
      (fun _ => iprop(n_ptr ↦ n ∗ ∃ v : Loc, e_ptr ↦ v))) $$ Hsl [n e]
    · iframe
    · imodintro
      iintro %i %x %hx ⟨n, %v, e⟩ Hsl
      have hi : i < (e :: r).length := by
        have := (List.getElem?_eq_some_iff.1 hx).1; simp only [List.length_cons] at this Hl ⊢; omega
      obtain ⟨ei, hei⟩ : ∃ ei, (e :: r)[i]? = some ei := ⟨_, List.getElem?_eq_getElem hi⟩
      ihave #Hx := BigSepL2.bigSepL2_lookup (Φ := fun _ p e => entRO (GF := GF) p e) hx hei $$ Hents
      try wp_auto
      wp_apply wp_switchConf n x DFrac.discard ei (hn ei (List.mem_of_getElem? hei)) $$ [$Hpkg $Hx] as -
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe
    iintro ⟨n, %v, e⟩ Hsl
    try wp_auto
    obtain ⟨Hz1, Hz2, Hz3⟩ := last_idx sl.len ls.length (by simpa using Hsll.1) Hsll.2
    have Hb' : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := ⟨Hz3, Hz2⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    have hrl : r.length = ls.length := by simpa using Hl.symm
    obtain ⟨lx, hlx⟩ : ∃ lx, (l :: ls)[ls.length]? = some lx :=
      ⟨_, List.getElem?_eq_getElem (by simp)⟩
    obtain ⟨ex, hex⟩ : ∃ ex, (e :: r)[ls.length]? = some ex :=
      ⟨_, List.getElem?_eq_getElem (by simp [hrl])⟩
    ihave #Hx := BigSepL2.bigSepL2_lookup (Φ := fun _ p e => entRO (GF := GF) p e) hlx hex $$ Hents
    wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) (l :: ls) dq lx Hz3 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rw [Hz1]; simpa using hlx
    wp_apply wp_GetIndex.1 lx DFrac.discard ex $$ [$Hpb $Hx] as -
    try wp_auto
    iapply HΦ
    have hlast : (e :: r).getLast? = some ex := by
      rw [List.getLast?_eq_getElem?]; simpa [hrl] using hex
    rw [hlast]
    iframe
    iexact Hents
end proof

end AntHarness
end EtcdGrove
end Perennial
