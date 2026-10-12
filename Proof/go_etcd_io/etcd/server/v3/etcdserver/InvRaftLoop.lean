/-
The raft wrapper's `applyc` stream (`InvRaftNode.lean`), its two ends: the loop's step before a
send (`cum` extended with the batch) and the apply side's receive (the batch extends what it
got). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The loop, at the delivered log `L` after `n` payloads, appends the batch `ce` to `cum`: the
`n`th payload's two elements. -/
theorem cum_extend (γc : GName) (cums : List (List EntryModel)) (L ce : List EntryModel)
    (n : Nat) (hlen : cums.length = n + 1) (hlast : cums.getLast? = some L) :
    ⊢ monoListAuthOwn (GF := GF) γc 1 cums ==∗
      monoListAuthOwn γc 1 (cums ++ [L ++ ce]) ∗ monoListIdxOwn γc n L ∗
      monoListIdxOwn γc (n + 1) (L ++ ce) := by
  iintro Hauth
  imod monoListAuthOwn_update_app [L ++ ce] $$ Hauth with ⟨Hauth, #Hlb⟩
  have hn : (cums ++ [L ++ ce])[n]? = some L := by
    rw [List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at hlast
    rw [hlen] at hlast
    simpa using hlast
  have hn1 : (cums ++ [L ++ ce])[n + 1]? = some (L ++ ce) := by
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  ihave #H1 := monoListIdxOwn_get n L hn $$ Hlb
  ihave #H2 := monoListIdxOwn_get (n + 1) (L ++ ce) hn1 $$ Hlb
  imodintro
  iframe Hauth H1 H2

/-- **The apply side's receive** of the payload at its position: the batch extends exactly the
log `A` it got so far, and its token moves to `A ++ ce`. -/
theorem rnApplyTok_recv (E : RNEnv GF) (γ : RNNames) (rcv : List toApply) (A : List EntryModel)
    (ap : toApply) :
    ⊢ spscConsumer γ.ap (rcv ++ [ap]) -∗ monoListIdxOwn γ.cum rcv.length A -∗
      rnApP E γ (rcv.length : Int) ap -∗
      ∃ (ce : List EntryModel) (ceL : List Loc),
        rnApplyTok γ (A ++ ce) ∗ ap.entries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (A ++ ce) ∗
        ⌜ap.snapshot' = null⌝ ∗ isUnitBag ap.notifyc' ∗ isUnitBag ap.raftAdvancedC' := by
  iintro Hcons #HA HP
  iunfold rnApP at HP
  icases HP with ⟨%F, %ce, %ceL, #HF, #HFce, #Hsl, #Hents, #HC, %Hsnap, #Hn, #Hrac⟩
  simp only [Int.toNat_natCast] at *
  ihave %Heq := mono_list_idx_agree γ.cum rcv.length F A $$ HF HA
  subst Heq
  iexists ce, ceL
  iframe Hsl Hents HC Hn Hrac
  isplitl [Hcons]
  · iunfold rnApplyTok
    iexists rcv ++ [ap]
    iframe Hcons
    simp only [List.length_append, List.length_singleton]
    iexact HFce
  ipureintro; exact Hsnap

end lemmas

end EtcdGrove
end Perennial
