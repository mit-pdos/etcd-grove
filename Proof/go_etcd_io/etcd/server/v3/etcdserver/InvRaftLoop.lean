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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
      (∃ (ce : List EntryModel) (ceL : List Loc),
        rnApplyTok γ (A ++ ce) ∗ ap.entries' ↦*□ ceL ∗ entriesAt ceL ce ∗ □ E.C (A ++ ce) ∗
        ⌜ap.snapshot' = null⌝ ∗
        (∃ γnc : NotifyNames, isNotify γnc ap.notifyc' (rnApR γ A ce) ∗ notifyRcv γnc) ∗
        rnApGive γ A ce ∗
        rnAdvChan ap.raftAdvancedC'
          (letI := srvStor (GF := GF) γ.node
           nodeAppliedLb γ.node.cl γ.id (γ.pre ++ A ++ ce).length) ∗
        committedLast E.γr ce) ∨
      -- (2026-10-30, the repair: snapshots allowed) a snapshot payload: the log jumps to `A'`
      (∃ (A' : List EntryModel) (sv : SnapshotM),
        rnApplyTok γ A' ∗
        ⌜A.length < A'.length ∧ (γ.pre ++ A').length = uint.nat sv.Metadata'.Index'⌝ ∗
        ownSnapM ap.snapshot' DFrac.discard sv ∗
        (letI := srvStor (GF := GF) γ.node
         snapshotCert γ.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists)) ∗
        □ E.C A' ∗ (∃ γnc : NotifyNames, isNotify γnc ap.notifyc' iprop(True) ∗ notifyRcv γnc) ∗
        rnAdvChan ap.raftAdvancedC'
          (letI := srvStor (GF := GF) γ.node
           nodeAppliedLb γ.node.cl γ.id (γ.pre ++ A').length) ∗
        committedAtLeast E.γr sv.Metadata'.Index') := by
  iintro Hcons #HA HP
  iunfold rnApP at HP
  icases HP with (HP | HP)
  rotate_left
  · -- SNAPSHOT-SORRY: the snapshot payload's components, `cum`'s agreement at `rcv.length`
    -- (`A` is `F`) and the consumer's token at `A'`
    sorry
  ileft
  iunfold rnApN at HP
  icases HP with ⟨%F, %ce, %ceL, #HF, #HFce, #Hsl, #Hents, #HC, %Hsnap, Hn, HG, #Hrac, #Hcl, -⟩
  simp only [Int.toNat_natCast] at *
  ihave %Heq := mono_list_idx_agree γ.cum rcv.length F A $$ HF HA
  subst Heq
  iexists ce, ceL
  iframe Hsl Hents HC Hn HG Hrac Hcl
  isplitl [Hcons]
  · iunfold rnApplyTok
    iexists rcv ++ [ap]
    iframe Hcons
    simp only [List.length_append, List.length_singleton]
    iexact HFce
  ipureintro; exact Hsnap


/-- (D43 M3) A normal entry keeps the view. -/
theorem rnCfgAt_normal1 (γ : RNNames) (L : List EntryModel) (m : EntryModel)
    (hm : m.typ = W32 0) :
    rnCfgAt (GF := GF) γ L ⊢ rnCfgAt γ (L ++ [m]) := by
  sorry
/- REPAIR-OLD
  unfold rnCfgAt
  split
  · have := dvView_normal (GF := GF) γ.srv (some γ.nl) L m hm
    unfold dvView at this
    exact this
  · exact .rfl
-/

/-- (D43 M3) A batch of normal entries keeps the view. -/
theorem rnCfgAt_normal (γ : RNNames) (ce : List EntryModel)
    (h : ∀ m, m ∈ ce → m.typ = W32 0) : ∀ L, rnCfgAt (GF := GF) γ L ⊢ rnCfgAt γ (L ++ ce) := by
  induction ce with
  | nil => intro L; rw [List.append_nil]
  | cons m ce IH =>
    intro L
    refine (rnCfgAt_normal1 γ L m (h m List.mem_cons_self)).trans ?_
    rw [show L ++ m :: ce = (L ++ [m]) ++ ce by simp]
    exact IH (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) _

/-- (D43 M3) A batch with no `ConfChange` entry (Go's scan) of the server's committed log
(`srvIdxOkW`: normal entries and `ConfChange`s) is all normal entries. -/
theorem ccIn_false_normal (ai₀ : w64) (L ce : List EntryModel) (hidx : srvIdxOkW ai₀ (L ++ ce))
    (hc : ccIn ce = false) : ∀ m, m ∈ ce → m.typ = W32 0 := by
  intro m hm
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
  have h1 := (hidx (L.length + n) m (by rw [List.getElem?_append_right (by omega)]; simpa using hn)).2
  rcases h1 with h1 | ⟨h1, -⟩
  · exact h1
  · exfalso
    unfold ccIn at hc
    have := List.any_eq_false.1 hc m hm
    simp [h1] at this

/-- (D43 M3) **The view after a batch with no `ConfChange` entry**: the loop kept it (`rnHands`
is false), and the batch, of the server's committed log, is normal entries. -/
theorem rnCfgAt_back_false (γ : RNNames) (ai₀ : w64) (L ce : List EntryModel)
    (hidx : srvIdxOkW ai₀ (L ++ ce)) (hcc : ccIn ce = false) :
    (if rnHands γ ce then iprop(True) else rnCfgAt (GF := GF) γ L) ⊢ rnCfgAt γ (L ++ ce) := by
  have hh : rnHands γ ce = false := by unfold rnHands; simp [hcc]
  rw [ite_eq_right (by rw [hh]; decide)]
  exact rnCfgAt_normal γ ce (ccIn_false_normal ai₀ L ce hidx hcc) L

/-- (D43 M3) **The view after a batch with a `ConfChange` entry**: the second `notifyc` send's
(`rnApR`; 2026-10-30, the repair: one mode, until then in the static mode the one the loop kept). -/
theorem rnCfgAt_back_true (γ : RNNames) (L ce : List EntryModel) (hcc : ccIn ce = true) :
    (if rnHands γ ce then iprop(True) else rnCfgAt (GF := GF) γ L) ∗ rnApR γ L ce ⊢
      rnCfgAt γ (L ++ ce) := by
  sorry
/- REPAIR-OLD
  unfold rnApR
  cases hd : γ.node.dyn
  · have hh : rnHands γ ce = false := by unfold rnHands; simp [hd]
    rw [ite_eq_right (by rw [hh]; decide), ite_eq_right (by rw [hh]; decide)]
    iintro ⟨H, -⟩
    iapply rnCfgAt_static γ L (L ++ ce) hd $$ H
  · have hh : rnHands γ ce = true := by unfold rnHands; simp [hd, hcc]
    rw [ite_eq_left hh, ite_eq_left hh]
    iintro ⟨-, H⟩
    iexact H
-/

/-- (D43 M3) The batch's view option at the apply side: the node's names when the view goes along
(`rnHands`). -/
def rnDv (γ : RNNames) (ce : List EntryModel) : Option Loc :=
  if rnHands γ ce then some γ.nl else none

/-- (D43 M3) What the apply thread's receive deposits, as the apply side states it. -/
theorem rnApR_dv (γ : RNNames) (γs : ServerRaftNames) (hpre : γ.pre = γs.pre)
    (hraft : γs.raft = γ.node) (A ce : List EntryModel) :
    rnApR (GF := GF) γ A ce = dvView γs (rnDv γ ce) (A ++ ce) := by
  sorry
/- REPAIR-OLD
  unfold rnApR rnDv dvView
  by_cases h : rnHands γ ce
  · have hd : γ.node.dyn = true := by
      unfold rnHands at h; simp only [Bool.and_eq_true] at h; exact h.1
    rw [ite_eq_left h, ite_eq_left h]
    unfold rnCfgAt srvCfgView
    rw [ite_eq_left hd, hpre, hraft]
  · rw [ite_eq_right h, ite_eq_right h]
-/

/-- (D43 M3) What goes along with the batch, as the apply side states it, with the node's
conf-change contract (`isRaftNodeIfc`'s). -/
theorem rnApGive_dv (s : Loc) (γ : RNNames) (γs : ServerRaftNames) (hpre : γ.pre = γs.pre)
    (hraft : γs.raft = γ.node) (A ce : List EntryModel) :
    srvRaftNodeCC (GF := GF) s γ.srv γ.nl ∗ rnApGive γ A ce ⊢
      dvView γs (rnDv γ ce) A ∗ dvRes s γs (rnDv γ ce) (A ++ ce) := by
  sorry
/- REPAIR-OLD
  unfold rnApGive rnDv dvView dvRes
  by_cases h : rnHands γ ce
  · have hd : γ.node.dyn = true := by
      unfold rnHands at h; simp only [Bool.and_eq_true] at h; exact h.1
    rw [ite_eq_left h, ite_eq_left h]
    simp only
    unfold rnCfgAt srvCfgView
    rw [ite_eq_left hd, srvRaftNodeDyn_congr s γs γ.srv γ.nl hraft]
    iintro ⟨(%Hf | #Hn), Hv, #Hd⟩
    · rw [hd] at Hf; cases Hf
    have hγs : γs = ⟨γ.node, γ.pre, γs.ai0⟩ := by cases γs; simp_all
    rw [hγs]
    iframe Hv Hn
    unfold srvLE at *
    iexact Hd
  · rw [ite_eq_right h, ite_eq_right h]
    simp only
    iintro -
    isplit <;> itrivial
-/

/-- (D43 M3) The server's node meets the conf-change contract: the wrapper's node contract's
(`isRaftNodeIfc`). (2026-10-30, the repair: in every cluster; until then `srvRaftNodeDyn`, in the
dynamic mode.) -/
theorem srvRaftNodeCC_of_isRaftNode (E : RNEnv GF) (γ : RNNames) (s : Loc) :
    isRaftNode E γ (srvRAddr s) ⊢ srvRaftNodeCC s γ.srv γ.nl := by
  sorry
/- REPAIR-OLD
  iintro #H
  iunfold isRaftNode at H
  iNamed H
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hn, (%Hd | #Hd), -⟩
  · ileft; ipureintro; exact Hd
  · iright
    iunfold srvRaftNodeDyn
    iexists n
    iframe Hn Hd
-/

end lemmas

end EtcdGrove
end Perennial
