/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__send.lean`. Lean-first
(no Rocq counterpart).

The sender is a started replica (`repKnown`), so `c.replica(from)` is it (`isRep`). Each message,
read-only at `readyDq` in the slice, is copied (`copyMsg`: owned, without responses, with its
`Entries` capacity) and the copy handed to `deliver` with the message's `sentMsg` and credits.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__send
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__replica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.copyMsg

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

theorem Cluster.send.wp_proof
    (wp_replica : Cluster.replica.spec (GF := GF) (hG := hG))
    (wp_copyMsg : copyMsg.spec (GF := GF) (hG := hG))
    (wp_deliver : Cluster.deliver.spec (GF := GF) (hG := hG)) :
    Cluster.send.spec (GF := GF) (hG := hG) := by
  intro γr vs c src msl ms
  wp_start as ⟨#Hcc, #Hkn, Hms, Hmsok⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  try wp_auto
  wp_apply wp_replica γr vs c src true $$ [$Hcc] as %r Hr
  · simp only [↓reduceIte]; iexact Hkn
  icases Hr with (%Hf | #Hr)
  · exact Hf.elim
  try wp_auto
  ihave %Hmslen := ownSlice_len $$ Hms
  simp only [List.length_map] at Hmslen
  ihave IH : iprop(∃ (k : w64) (mv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗ "Hms" ∷ msl ↦* ms.map QMsg.loc ∗
      "Hmsok" ∷ ([∗list] q ∈ ms.drop (sint.nat k),
        msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γr.cluster kvrRaftN src q.st ∗
          msgCredits γr.cluster kvrRaftN q.st) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ms.length : Int)⌝) $$ [i m Hms Hmsok]
  · iexists W64 0, _
    iframe i m Hms
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe Hmsok
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ms.length := by word
    obtain ⟨q, Hq⟩ : ∃ q, ms[sint.nat k]? = some q := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hql : (ms.map QMsg.loc)[sint.nat k]? = some q.loc := by
      rw [List.getElem?_map, Hq]; rfl
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z msl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index msl (sint.Z k) _ (DFrac.own 1) q.loc Hk.1 $$ [Hms] as Hms
    · iframe Hms; ipureintro; exact Hql
    have Hdrop : ms.drop (sint.nat k) = q :: ms.drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]
      rw [List.getElem?_eq_getElem Hlt] at Hq
      rw [Option.some.inj Hq]
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [Hdrop]
    icases Hmsok with ⟨⟨Hmq, #Hsent, Hcred⟩, Hmsok⟩
    try wp_auto
    wp_apply wp_copyMsg q.loc (readyDq q.st) DFrac.discard false q.st $$ [$Hpkg $Hmq] as %l' ⟨-, Hl'⟩
    wp_apply wp_deliver γr vs c src r l' q.st $$ [$Hcc $Hr $Hl' $Hsent $Hcred]
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, q.loc
    rw [Hk1]
    iframe
    ipureintro; constructor <;> word
  · try wp_auto
    iapply HΦ
    itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
