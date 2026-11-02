/-
kvreconf's proof (the same Go text), ported. Proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__do.lean`. Lean-first (no Rocq
counterpart); kv's `KV.do` (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/KV__do.lean`) with the
cluster's operation ids.

Under the cluster's lock the next operation id (`c.nextOp`, with the cluster lock's half of
`γ.r.opn`) mints the operation's datum and its slot, holding the client's atomic update
(`kvr_mint`). Each attempt proposes the same datum at a random member (`Replica.propose`); an
answer (`waitP`) collects the client's result from the slot (`kvr_collect`). With every id used, the
cluster spins (it does not happen: `2^64 - 1` operations).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__do
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__randomMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__propose
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.encode
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ClientLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (encodeOp kvNext)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.do.wp_proof
    (wp_encode : encode.spec (GF := GF) (hG := hG))
    (wp_randomMember : Cluster.randomMember.spec (GF := GF) (hG := hG))
    (wp_propose : Replica.propose.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Cluster.do.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c kind key val Ψ Hkey Hval
  wp_start as ⟨#Hcc, Hau⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iNamed HL
  wp_auto_lc 3
  wp_if_destruct
  · -- every operation id used: the cluster spins
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hreps Hcur
      Hstops Hfiles]
    · inext
      unfold clusterLockInv
      iexists mR, R, nid, _, U
      iframe
      ipureintro; exact Hdom
    try wp_auto
    ihave Hspin : iprop(True) $$ []
    · itrivial
    wp_for Hspin
    wp_for_post
    iframe
  have Hn : uint.Z nop + 1 < 2 ^ 64 := by
    have : nop ≠ W64 18446744073709551615 := by assumption
    word
  have Hk64 : (key.length : Int) < 2 ^ 64 := by omega
  try wp_auto
  -- the operation's datum, minted at the fresh id, with its slot holding the client's update
  ihave Hau : opAu γ (kvNext kind key val) key Ψ $$ [Hau]
  · unfold opAu; iexact Hau
  imod kd_mint γ nop kind key val Ψ ⊤ CoPset.subseteq_top Hn Hk64 $$ Hinv Hopn Hlc1 Hau
    with ⟨Hopn, %γo, #Hop, #Hsp, Htok⟩
  wp_apply wp_encode (nop + W64 1) kind key val Hkey Hval $$ [$Hpkg] as %b' ⟨Hb, -⟩
  imod ownSlice_persist b' _ _ $$ Hb with #Hb
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hreps Hcur
    Hstops Hfiles]
  · inext
    unfold clusterLockInv
    iexists mR, R, nid, nop + W64 1, U
    iframe
    ipureintro; exact Hdom
  try wp_auto
  ihave HI : iprop(£ 1 ∗ £ 1) $$ [Hlc2 Hlc3]
  · iframe Hlc2 Hlc3
  wp_for HI
  wp_apply wp_randomMember γ vs dir c $$ [$Hcc] as %r ⟨%rid, #Hr⟩
  wp_apply wp_propose γ vs dir rid r (encodeOp (nop + W64 1) kind key val) γo b' (W64 100000000)
    $$ [$Hr $Hop $Hb] as %v %ok Hres
  try wp_auto
  cases ok
  · -- no answer: another attempt
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    ihave #Hctr := isStats_field (c.[KCluster, go!"Stats"]) go!"Retries" (by decide) $$ Hstats
    wp_apply wp_add _ _ $$ [$Hpkg $Hctr]
    wp_for_post
    iframe
  · -- the answer: the client's result, from the operation's slot
    simp only [↓reduceIte]
    imod kd_collect γ _ γo Ψ v ⊤ CoPset.subseteq_top $$ Hinv Hop Hsp Htok Hres with HQ
    icases HI with ⟨Hlc1, Hlc2⟩
    imod lc_fupd_elim_later $$ Hlc1 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    try wp_auto
    wp_for_post
    iapply HΦ $$ HQ

end proof

end kvdurable
end EtcdGrove
end Perennial
