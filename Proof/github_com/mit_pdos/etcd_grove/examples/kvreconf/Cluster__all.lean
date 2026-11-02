/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__all.lean`. Lean-first
(no Rocq counterpart).

Under `c.mu`, the range over `c.replicas` appends each replica (its `isRep` from the lock, and with
the stopper's token its stop token, `bigSepM_keys`). With the stopper's token, the lock's half of
`γr.stp` agrees (`false`: the tokens are in the lock) and both halves are set (`true`). The map is
not empty: its keys are `1 … nextID-1`, `nextID` above the voters (one at least, `OptsOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__all
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.LifeLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClusterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.all.wp_proof : Cluster.all.spec (GF := GF) (hG := hG) := by
  intro γr vs c own
  wp_start as ⟨Hc, Hown⟩
  iunfold isClusterC at Hc
  iNamed Hc
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold clusterLockInv at HL
  iNamed HL
  ihave #Hreps' := Hreps
  -- the stop tokens, as `own` says
  ihave Htk : iprop(|==> ((if own then iprop(ghostVar γr.stp (1 : Qp).half true) else iprop(True)) ∗
      ghostVar γr.stp (1 : Qp).half (b || own) ∗
      (if b || own then iprop(True) else [∗map] _id ↦ r ∈ R, repStop γr vs r) ∗
      [∗map] _id ↦ r ∈ R, (if own then repStop γr vs r else iprop(True)))) $$ [Hown Hstp Htoks]
  · cases own with
    | false =>
      simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      imodintro
      iframe Hstp Htoks
      iapply (BigSepM.bigSepM_mono (Φ := fun id r => isRep (GF := GF) γr vs id r)
        (Ψ := fun _ _ => iprop(True)) (m := R) (fun _ => true_intro)) $$ Hreps'
    | true =>
      simp only [Bool.or_true, ↓reduceIte]
      iunfold stopper at Hown
      ihave %Hb := ghostVar_agree _ _ _ _ _ $$ Hown Hstp
      subst Hb
      imod ghostVar_update_halves true _ _ _ $$ Hown Hstp with ⟨Hown, Hstp⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      imodintro
      iframe Hown Hstp Htoks
  imod Htk with ⟨Hown, Hstp, Htoks, Hmine⟩
  try wp_auto
  obtain ⟨HdomR, HdomU, Hvn, Hn10⟩ := Hdom
  have Hv1 : 1 ≤ vs.length := by
    rw [Ho.2, bootVoters_length]; have := Ho.1.1; word
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc)
    (fun (keys : List w64) (i : Int) => iprop(∃ (sl : GoSlice) (rs : List Loc) (rv : Loc),
      "rs" ∷ rs_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* rs ∗ "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "r" ∷ r_ptr ↦ rv ∗
      "%Hlen" ∷ ⌜(rs.length : Int) = i ∧ 0 ≤ i⌝ ∗
      "#Hgot" ∷ ([∗list] r ∈ rs, ∃ id, isRep γr vs id r) ∗
      "Hgtk" ∷ ([∗list] r ∈ rs, (if own then repStop γr vs r else iprop(True))) ∗
      "Hrest" ∷ ([∗list] k ∈ keys.drop i.toNat, ∃ x, ⌜R !! k = some x⌝ ∗
        (if own then repStop γr vs x else iprop(True)))))
    _ _ _ mR R _ $$ HR
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  isplitl [rs r Hmine]
  · ihave Hl := bigSepM_keys (fun _ x => iprop(if own then repStop γr vs x else iprop(True)))
      keys R Hknd Hkset $$ Hmine
    iexists slice.nil, [], _
    iframe rs r
    simp only [Int.toNat_zero, List.drop_zero]
    iframe Hl
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; simp
    isplitr
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
    iNamed HP
    try wp_auto
    rw [life_drop_cons _ _ _ Hki]
    icases Hrest with ⟨⟨%x, %Hx, Hx⟩, Hrest⟩
    rw [Hmv] at Hx
    cases Hx
    ihave #Hrv := BigSepM.bigSepM_lookup (Φ := fun id r => isRep γr vs id r) Hmv $$ Hreps'
    wp_apply wp_slice_literal (V := Loc) [v]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl', rs ++ [v], v
    iframe rs r Hsl Hcap
    have Hi : (i + 1).toNat = i.toNat + 1 := by omega
    rw [Hi]
    iframe Hrest
    isplitr
    · ipureintro; simp only [List.length_append, List.length_singleton]; omega
    isplitr
    · iapply BigSepL.bigSepL_snoc.2
      iframe Hgot
      iexists key; iexact Hrv
    iapply BigSepL.bigSepL_snoc.2
    iframe Hgtk Hx
  iintro HP HR
  iNamed HP
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hrseq Hstp
    Htoks]
  · inext
    unfold clusterLockInv
    iexists mR, R, nid, nop, U, b || own
    iframe
    iframe Hreps'
    ipureintro
    exact ⟨HdomR, HdomU, Hvn, Hn10⟩
  try wp_auto
  iapply HΦ
  iexists rs
  iframe Hsl Hgot
  isplitr
  · ipureintro
    intro hnil
    subst hnil
    have h1 : (R !! (W64 1)).isSome := (HdomR (W64 1)).2 ⟨by word, by word⟩
    have hk : (W64 1) ∈ keys := (Hkset _).2 h1
    have hpos : 0 < keys.length := List.length_pos_of_mem hk
    simp at Hlen
    omega
  cases own with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  | true =>
    simp only [↓reduceIte]
    iframe Hown Hgtk

end proof

end kvreconf
end EtcdGrove
end Perennial
