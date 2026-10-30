/-
Lean-first (no Rocq counterpart).

# Applying a `Ready`'s committed entries (2026-10-30, kvreconf's `run`)

What `run`'s apply loop and its `Advance` use, beside the methods' specs:
- the `Ready`'s read states, each `rsOk` (`kvr_readStatesPts_rsOk`, kv's `readStatesPts_rsOk`);
- the applier's view of its node (`appNode`) carried to the longer delivered log
  (`appNode_extend`: `skippedIn` only reads the entries below the applied index), and opened for
  `Advance` (`appNode_open`);
- the bound `applyEntry` needs (`frozenTo_len`): a delivered log with an entry frozen above the
  compaction point is shorter than `2^61` (`memLog_bound`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunAppend

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

theorem run_lt (k len : w64) (n m : Nat) (h : sint.Z k < sint.Z len) (h1 : m = sint.nat len)
    (h2 : m = n) (h0 : 0 ≤ sint.Z k) : sint.nat k < n := by
  subst h1 h2; word

theorem run_eq (k len : w64) (n m : Nat) (h : ¬ sint.Z k < sint.Z len) (h1 : m = sint.nat len)
    (h2 : m = n) (hk : sint.Z k ≤ (n : Int)) : sint.nat k = n := by
  subst h1 h2; word

/-- The applied log's length fits a `uint64`: either an entry is frozen above the compaction point,
or it is at most the compaction point, at most the stored snapshot's index. -/
theorem run_len64 (c L : Nat) (si : w64) (h1 : c < L → L < 2 ^ 61) (h2 : c ≤ uint.nat si) :
    L < 2 ^ 64 := by
  by_cases h : c < L
  · have := h1 h; omega
  · have : uint.nat si < 2 ^ 64 := by word
    omega

section apply
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- The `ReadState` values of a `Ready`'s read states, each `rsOk`. -/
theorem kvr_rsOk_of_readStates (γ : Cluster) :
    ∀ (vs : List ReadState) (sts : List ReadStateM),
    ([∗list] v;st ∈ vs;sts, ⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx') ∗
      ([∗list] st ∈ sts, readStateOk (GF := GF) γ kvrRaftN st.RequestCtx' st.Index') ⊢
      [∗list] v ∈ vs, rsOk γ v
  | [], _ => by
    iintro ⟨-, -⟩
    iapply (BigSepL.bigSepL_nil (Φ := fun _ v => rsOk (GF := GF) γ v)).2; iempintro
  | v :: vs, [] => by
    iintro ⟨Hb, -⟩
    ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
    simp at Hl
  | v :: vs, st :: sts => by
    iintro ⟨Hb, #Hok⟩
    icases (BigSepL2.bigSepL2_cons).1 $$ Hb with ⟨⟨%Hi, #Hc⟩, #Hb'⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hok with ⟨#Hok1, #Hok'⟩
    iapply (BigSepL.bigSepL_cons (Φ := fun _ v => rsOk (GF := GF) γ v)).2
    isplitl []
    · unfold rsOk
      iexists st.RequestCtx'
      iframe Hc
      rw [Hi]
      iexact Hok1
    · ihave H := kvr_rsOk_of_readStates γ vs sts $$ [Hb' Hok']
      · iframe Hb' Hok'
      iexact H

/-- The `ReadState` values a `Ready` hands out, each `rsOk`. -/
theorem kvr_readStatesPts_rsOk (γ : Cluster) (rs : GoSlice) (sts : List ReadStateM) :
    readStatesPts (GF := GF) rs sts ∗
      ([∗list] st ∈ sts, readStateOk γ kvrRaftN st.RequestCtx' st.Index') ⊢
      ∃ vs : List ReadState, rs ↦*□ vs ∗ [∗list] v ∈ vs, rsOk γ v := by
  iintro ⟨H, #Hok⟩
  iunfold readStatesPts at H
  icases H with ⟨%vs, #Hs, #Hb⟩
  iexists vs
  iframe Hs
  ihave H := kvr_rsOk_of_readStates γ vs sts $$ [Hb Hok]
  · iframe Hb Hok
  iexact H

/-- `skippedIn` reads the entries below its end only: it carries to a longer log. -/
theorem skippedIn_prefix (γ : Cluster) (l l' : List LogEntry) (a b : Nat) (hp : l <+: l')
    (hb : b ≤ l.length) :
    skippedIn (GF := GF) γ l a b ⊢ skippedIn γ l' a b := by
  unfold skippedIn
  apply BigSepL.bigSepL_mono
  intro k j hj
  have hm := List.mem_range'_1.1 (List.mem_of_getElem? hj)
  have hjl : j < l.length := by omega
  obtain ⟨t, rfl⟩ := hp
  have hget : (l ++ t)[j]? = l[j]? := List.getElem?_append_left hjl
  iintro #H %e %he
  iapply H
  ipureintro
  rw [← hget]; exact he

/-- The applier's view carried to a longer delivered log. -/
theorem appNode_extend (γr : RNames) (n : Loc) (l l' : List LogEntry) (k : Nat) (m : Membership)
    (hp : l <+: l') (hk : k ≤ l.length) :
    appNode (GF := GF) γr n l k m ∗ deliveredLogLb n γr.cluster kvrRaftN l' ⊢ appNode γr n l' k m := by
  unfold appNode
  iintro ⟨⟨%v, Hc, -, #Hs, %Hv⟩, #Hd⟩
  iexists v
  iframe Hc Hd
  isplitl []
  · iapply skippedIn_prefix _ l l' _ _ hp hk $$ Hs
  ipureintro; exact Hv

/-- The applier's view opened for `Advance`: the node's configuration view, every conf entry
from its index skipped. -/
theorem appNode_open (γr : RNames) (n : Loc) (l : List LogEntry) (k : Nat) (m : Membership) :
    appNode (GF := GF) γr n l k m ⊢ ∃ v : ConfigView, nodeConfig n γr.cluster kvrRaftN v ∗
      skippedIn γr.cluster l v.applied k ∗
      (nodeConfig n γr.cluster kvrRaftN v -∗ appNode γr n l k m) := by
  unfold appNode
  iintro ⟨%v, Hc, #Hd, #Hs, %Hv⟩
  iexists v
  iframe Hc Hs
  iintro Hc
  iexists v
  iframe Hc Hd Hs
  ipureintro; exact Hv

/-- A delivered log with an entry frozen above the compaction point is shorter than `2^61`. -/
theorem frozenTo_len (γs : MemStorNames) (c : Nat) (D : List LogEntry) :
    frozenTo (GF := GF) γs c D ⊢ ⌜c < D.length → D.length < 2 ^ 61⌝ := by
  unfold frozenTo
  iintro #H
  ihave %Hb := memLog_bound _ _ _ _ $$ H
  ipureintro
  intro hc
  rw [List.length_drop, kvr_toEntries_length] at Hb
  rcases Hb with h | h
  · have := congrArg List.length h
    rw [List.length_drop, kvr_toEntries_length] at this
    simp at this; omega
  · omega

end apply

end kvreconf
end EtcdGrove
end Perennial
