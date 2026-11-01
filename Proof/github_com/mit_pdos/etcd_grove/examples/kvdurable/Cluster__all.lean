/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__all.lean`. Lean-first
(no Rocq counterpart). kvreconf's, without the stopper's mode.

Under `c.mu`, the range over `c.replicas` appends each replica (its `isRep` from the lock; its id
known, below `nextID`, from the lock's `γ.r.nid` authority). The map is not empty: its keys are
`1 … nextID-1`, `nextID` above the voters (one at least, `kdOptsOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__all
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClusterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.all.wp_proof : Cluster.all.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c
  wp_start as Hc
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
  ihave #Hlb := monoNatLbOwn_get _ _ _ $$ HnidA
  try wp_auto
  obtain ⟨HdomR, HdomU, Hvn, Hn10⟩ := Hdom
  have Hv1 : 1 ≤ vs.length := by
    rw [Ho.2, kvreconf.bootVoters_length]; have := Ho.1.1; word
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc)
    (fun (keys : List w64) (i : Int) => iprop(∃ (sl : GoSlice) (rs : List Loc) (rv : Loc),
      "rs" ∷ rs_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* rs ∗ "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "r" ∷ r_ptr ↦ rv ∗
      "%Hlen" ∷ ⌜(rs.length : Int) = i ∧ 0 ≤ i⌝ ∗
      "#Hgot" ∷ ([∗list] r ∈ rs, ∃ id, isRep γ vs dir id r ∗ repKnown γ id)))
    _ _ _ mR R _ $$ HR
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  isplitl [rs r]
  · iexists slice.nil, [], _
    iframe rs r
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; simp
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
    iNamed HP
    try wp_auto
    ihave #Hrv := BigSepM.bigSepM_lookup (Φ := fun id r => isRep γ vs dir id r) Hmv $$ Hreps'
    have Hkr := (HdomR key).1 (by simp [Hmv])
    ihave #Hkn : repKnown γ key $$ []
    · unfold repKnown
      isplitr
      · ipureintro; intro h; subst h; simp at Hkr
      iapply monoNatLbOwn_le (uint.nat key + 1) (by omega) $$ Hlb
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
    isplitr
    · ipureintro; simp only [List.length_append, List.length_singleton]; omega
    iapply BigSepL.bigSepL_snoc.2
    iframe Hgot
    iexists key
    iframe Hrv Hkn
  iintro HP HR
  iNamed HP
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hcur Hstops
    Hfiles]
  · inext
    unfold clusterLockInv
    iexists mR, R, nid, nop, U
    iframe
    iframe Hreps'
    ipureintro
    exact ⟨HdomR, HdomU, Hvn, Hn10⟩
  try wp_auto
  iapply HΦ
  iexists rs
  iframe Hsl Hgot
  ipureintro
  intro hnil
  subst hnil
  have h1 : (R !! (W64 1)).isSome := (HdomR (W64 1)).2 ⟨by word, by word⟩
  have hk : (W64 1) ∈ keys := (Hkset _).2 h1
  have hpos : 0 < keys.length := List.length_pos_of_mem hk
  simp at Hlen
  omega

end proof

end kvdurable
end EtcdGrove
end Perennial
