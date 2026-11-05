/-
**The example's client operations' atomic updates, from its invariant** (K4 of
`notes/k8s-compactor-plan.md`, its second part). Lean-first.

Each opens `cinv` at the operation's commit, at a member's KV names `γk'` with the invariant's
`γk`'s state (`kvSame`), and keeps it: the state's revision counter moves with the state
(`kvOpStep_rev`), and `compact_rev_key`'s protocol holds of the new state.
- `readAu_check`: `apiserver`'s latest `Get` of the key: the read state's revision is at least a
  lower bound of the counter, and the key is absent or holds `FormatInt c` for a `c` that is `0` or
  reached.
- `putAu_other`: the writer's put of another key.
- `casAu`, `casOk_of_cinv`: the compactors' contract (`k8s.casOk`, K2) at `Seen := seenOk γ` and
  `recorded := True`. A winning round puts `FormatInt rev` (`casTxn_win_value`; the flag set); a
  losing one changes nothing (`casTxn_lose_same`) and finds the key present: absent, its version
  is `0`, so a round at `ev = 0` wins (`casWins_of_absent`), and one at `Seen` contradicts the unset
  flag.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Inv
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.CasModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver k8s

section aus
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `etcdKV` reads only the state's ghost name (as `etcdKV_congr`, without the server's
assumptions). -/
theorem etcdKV_same (γk γk' : KVNames) (hs : kvSame γk' γk) (σ : KVState) :
    etcdKV (GF := GF) γk σ = etcdKV γk' σ := by
  unfold etcdKV; rw [hs.1]

/-- What `apiserver`'s `Get` of `compact_rev_key` tells it about the state `σ` it read (pure but for
`revOk`; persistent): its revision is at least `r`, and the key is absent or holds `FormatInt c` for a
`c` that is `0` or reached. -/
def checkQ (γk : KVNames) (r : Nat) (σ : KVState) : IProp GF :=
  iprop(⌜r ≤ σ.rev⌝ ∗ (⌜keyValue σ compactRevKey = none⌝ ∨
    ∃ c : w64, ⌜keyValue σ compactRevKey = some (fmtInt c (W64 10))⌝ ∗ k8s.revOk γk c))

instance checkQ_persistent (γk : KVNames) (r : Nat) (σ : KVState) :
    Persistent (checkQ (GF := GF) γk r σ) := by
  unfold checkQ; infer_instance

/-- `keyOk` gives `checkQ`'s key part. -/
theorem keyOk_check (γk : KVNames) (γ : CNames) (σ : KVState) (r : Nat) (hr : r ≤ σ.rev) :
    keyOk (GF := GF) γk γ σ ⊢ keyOk γk γ σ ∗ checkQ γk r σ := by
  iintro Hk
  iunfold keyOk at Hk
  icases Hk with (⟨%Hn, Hf⟩ | ⟨#Hs, %c, %Hc, #Hrc⟩)
  · isplitl [Hf]
    · iunfold keyOk; ileft; iframe Hf; ipureintro; exact Hn
    · iunfold checkQ; isplitr
      · ipureintro; exact hr
      · ileft; ipureintro; exact Hn
  · isplitl []
    · iunfold keyOk; iright; iframe Hs; iexists c; iframe Hrc; ipureintro; exact Hc
    · iunfold checkQ; isplitr
      · ipureintro; exact hr
      · iright; iexists c; iframe Hrc; ipureintro; exact Hc

/-- **`apiserver`'s read update** (persistent; see the file header): at a member's names `γk'`, the
read state meets `checkQ` at a lower bound `r` of the counter. -/
theorem readAu_check (γk γk' : KVNames) (hs : kvSame γk' γk) (γ : CNames) (r : Nat) :
    cinv (GF := GF) γk γ ∗ monoNatLbOwn γ.rv r ⊢ kvReadAu γk' (checkQ γk r) := by
  have Hm := cinvN_mask
  iintro ⟨#Hinv, #Hlb⟩
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold cinv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hrv, Hk, #Hh⟩
  ihave %Hv := monoNatLbOwn_valid γ.rv 1 σ.rev r $$ Hrv Hlb
  rw [etcdKV_same γk γk' hs]
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hrv Hk] with -
    · inext; iexists σ; rw [etcdKV_same γk γk' hs]; iframe; iexact Hh
    imodintro
    itrivial
  · iintro ⟨Hσ, -⟩
    imod Hmask with -
    ihave ⟨Hk, #HQ⟩ := keyOk_check γk γ σ r Hv.2 $$ Hk
    imod Hclose $$ [Hσ Hrv Hk] with -
    · inext; iexists σ; rw [etcdKV_same γk γk' hs]; iframe; iexact Hh
    imodintro
    iintro !>
    iexact HQ

/-- The invariant's contents at a new state `σ'` after `σ` (`σ.rev ≤ σ'.rev`): the counter moves. -/
theorem cinv_step (γk : KVNames) (γ : CNames) (σ σ' : KVState) (h : σ.rev ≤ σ'.rev) :
    monoNatAuthOwn (GF := GF) γ.rv 1 σ.rev ⊢ |==> monoNatAuthOwn γ.rv 1 σ'.rev := by
  iintro Hrv
  imod (mono_nat_own_update (GF := GF) (γ := γ.rv) σ'.rev h) $$ Hrv with ⟨Hrv, -⟩
  imodintro; iexact Hrv

/-- The writer's put of another key keeps the key's history. -/
theorem histOk_put_other (γk : KVNames) (σ : KVState) (k v : GoString) (hk : k ≠ compactRevKey) :
    histOk (GF := GF) γk σ ⊢ histOk γk (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) := by
  iintro #H
  iunfold histOk at H
  unfold histOk
  icases H with ⟨%C, %HC, #Hc⟩
  iexists C
  iframe Hc
  ipureintro
  exact ⟨KeyHist_put_other k v hk HC.1, OneChange_put k v HC.2.1,
    Nat.le_trans HC.2.2 (client.kvOpStep_rev _ σ)⟩

/-- A compactor's round keeps the key's history, its revision added. -/
theorem histOk_cas (γk : KVNames) (σ : KVState) (ev rev : w64) :
    histOk (GF := GF) γk σ ∗ k8s.revOk γk rev ⊢
      histOk γk (kvOpStep (.txn (casTxn ev rev)) σ) := by
  iintro ⟨#H, #Hr⟩
  iunfold histOk at H
  unfold histOk
  icases H with ⟨%C, %HC, #Hc⟩
  iexists rev :: C
  isplitr
  · ipureintro
    exact ⟨KeyHist_cas ev rev HC.1, OneChange_cas ev rev HC.2.1,
      Nat.le_trans HC.2.2 (client.kvOpStep_rev _ σ)⟩
  iapply BigSepL.bigSepL_cons.2
  iframe #

/-- **The writer's put of another key** (persistent; see the file header). -/
theorem putAu_other (γk : KVNames) (γ : CNames) (k v : GoString) (hk : k ≠ compactRevKey) :
    cinv (GF := GF) γk γ ⊢
      □ AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γk (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) ∗ ⌜kvRoom σ⌝,
          COMM iprop(True) }> := by
  have Hm := cinvN_mask
  iintro #Hinv
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold cinv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hrv, Hk, #Hh⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hrv Hk] with -
    · inext; iexists σ; iframe; iexact Hh
    imodintro
    itrivial
  · iintro ⟨Hσ, -⟩
    imod Hmask with -
    imod (cinv_step γk γ σ (kvOpStep (.put (putWireOf (opPutModel k v []))) σ)
      (client.kvOpStep_rev _ σ)) $$ Hrv with Hrv
    ihave #Hh' := histOk_put_other γk σ k v hk $$ Hh
    imod Hclose $$ [Hσ Hrv Hk] with -
    · inext
      iexists (kvOpStep (.put (putWireOf (opPutModel k v []))) σ)
      iframe Hσ Hrv Hh'
      have hko : keyOk (GF := GF) γk γ (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) =
          keyOk γk γ σ := by
        unfold keyOk; rw [keyValue_put_other k v σ hk]
      rw [hko]
      iexact Hk
    imodintro
    itrivial

/-- **One member's update for a compactor's round** (see the file header). -/
theorem casAu (γk γk' : KVNames) (hs : kvSame γk' γk) (γ : CNames) (ev rev : w64) :
    cinv (GF := GF) γk γ ∗ (⌜ev = W64 0⌝ ∨ seenOk γ) ∗ k8s.revOk γk rev ⊢
      kvOpAu1 γk' (.txn (casTxn ev rev))
        (casPost γk (seenOk γ) (fun _ => iprop(True)) ev rev) := by
  have Hm := cinvN_mask
  iintro ⟨#Hinv, #Hev, #Hrev⟩
  iunfold kvOpAu1
  iunfold kvAu1
  iauintro
  unfold atomic_acc
  iunfold cinv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hrv, Hk, #Hh⟩
  rw [etcdKV_same γk γk' hs]
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hrv Hk] with -
    · inext; iexists σ; rw [etcdKV_same γk γk' hs]; iframe; iexact Hh
    imodintro
    itrivial
  · iintro ⟨Hσ, -⟩
    imod Hmask with -
    imod (cinv_step γk γ σ (kvOpStep (.txn (casTxn ev rev)) σ) (client.kvOpStep_rev _ σ)) $$ Hrv with Hrv
    cases hw : casWins ev rev σ
    · -- lost: nothing changes, and the key is present
      rw [casTxn_lose_same ev rev σ hw]
      iunfold keyOk at Hk
      icases Hk with (⟨%Hn, Hf⟩ | ⟨#Hs, %c, %Hc, #Hrc⟩)
      · -- absent: impossible
        iexfalso
        icases Hev with (%Hev0 | #Hs)
        · subst Hev0
          rw [casWins_of_absent rev σ Hn] at hw
          cases hw
        · iunfold seenOk at Hs
          ihave %Hag := dghostVar_agree _ _ _ _ _ $$ Hf Hs
          cases Hag
      · imod Hclose $$ [Hσ Hrv] with -
        · inext; iexists σ; rw [etcdKV_same γk γk' hs]; iframe Hσ Hrv Hh
          iunfold keyOk; iright; iframe Hs; iexists c; iframe Hrc; ipureintro; exact Hc
        imodintro
        iunfold casPost
        iframe Hs
        rw [hw]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexists c
        iframe Hrc
        ipureintro; exact Hc
    · -- won: the key holds `FormatInt rev`, the flag set
      ihave Hseen : iprop(|==> seenOk (GF := GF) γ) $$ [Hk]
      · iunfold keyOk at Hk
        icases Hk with (⟨%Hn, Hf⟩ | ⟨#Hs, -⟩)
        · imod (dghostVar_update true γ.seen false) $$ Hf with Hf
          imod (dghostVar_persist γ.seen 1 true) $$ Hf with #Hf
          imodintro; iunfold seenOk; iexact Hf
        · imodintro; iexact Hs
      imod Hseen with #Hs
      ihave #Hh' := histOk_cas γk σ ev rev $$ [Hh Hrev]
      · iframe #
      imod Hclose $$ [Hσ Hrv] with -
      · inext; iexists (kvOpStep (.txn (casTxn ev rev)) σ)
        rw [etcdKV_same γk γk' hs]; iframe Hσ Hrv Hh'
        iunfold keyOk; iright; iframe Hs; iexists rev; iframe Hrev
        ipureintro; exact casTxn_win_value ev rev σ hw
      imodintro
      iunfold casPost
      iframe Hs
      rw [hw]
      simp only [↓reduceIte]
      itrivial

/-- **What the key's history gives a read** (Q1 (b)): the watch loop's read result. -/
theorem histOk_keyHist (γk : KVNames) (σ : KVState) :
    histOk (GF := GF) γk σ ⊢ k8s.keyHistOk γk (fun _ => iprop(True)) σ := by
  iintro #H
  iunfold histOk at H
  icases H with ⟨%C, ⟨%HK, -, %H1⟩, #Hc⟩
  unfold k8s.keyHistOk
  isplitr
  · ipureintro; exact H1
  isplitr
  · iintro !> %v %hv
    obtain ⟨c, hc, rfl⟩ := HK.1 v hv
    unfold k8s.keyValOk
    iexists c
    isplitr
    · ipureintro; rfl
    isplitr
    · itrivial
    iapply (BigSepL.bigSepL_mem (Φ := fun c => k8s.revOk (GF := GF) γk c) hc) $$ Hc
  · iintro !> %r %ev ⟨%hr, %hm, %hk⟩
    obtain ⟨c, hc, hv⟩ := HK.2 r ev hr hm hk
    unfold k8s.keyValOk
    iexists c
    isplitr
    · ipureintro; exact hv
    isplitr
    · itrivial
    iapply (BigSepL.bigSepL_mem (Φ := fun c => k8s.revOk (GF := GF) γk c) hc) $$ Hc

/-- **A read update whose result is the invariant's state's** `Q` (persistent): from a fact `Q` of
the invariant's contents at every state. -/
theorem readAu_of_cinv (γk : KVNames) (γ : CNames) (Q : KVState → IProp GF)
    (hQ : ∀ σ, histOk (GF := GF) γk σ ⊢ □ Q σ) :
    cinv (GF := GF) γk γ ⊢ kvReadAu γk Q := by
  have Hm := cinvN_mask
  iintro #Hinv
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold cinv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hrv, Hk, #Hh⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hrv Hk] with -
    · inext; iexists σ; iframe; iexact Hh
    imodintro
    itrivial
  · iintro ⟨Hσ, -⟩
    imod Hmask with -
    imod Hclose $$ [Hσ Hrv Hk] with -
    · inext; iexists σ; iframe; iexact Hh
    imodintro
    iapply (hQ σ) $$ Hh

/-- **The watch loop's contract, from the invariant** (Q1 (b); see the file header). -/
theorem keyReadOk_of_cinv (γk : KVNames) (γ : CNames) :
    cinv (GF := GF) γk γ ⊢ k8s.keyReadOk γk (fun _ => iprop(True)) := by
  iintro #Hinv
  unfold k8s.keyReadOk
  iapply (readAu_of_cinv γk γ _ (fun σ => by
    iintro #H
    imodintro
    iapply histOk_keyHist $$ H)) $$ Hinv

/-- **No revision writes a key twice, as a read update** (the watch server's `noDupKeys`). -/
theorem oneChangeAu (γk : KVNames) (γ : CNames) :
    cinv (GF := GF) γk γ ⊢ kvReadAu γk (fun σ => iprop(⌜OneChange σ⌝)) := by
  iintro #Hinv
  iapply (readAu_of_cinv γk γ _ (fun σ => by
    iintro #H
    iunfold histOk at H
    icases H with ⟨%C, ⟨-, %HO, -⟩, -⟩
    imodintro
    ipureintro; exact HO)) $$ Hinv

/-- **The compactors' contract, from the invariant** (see the file header), for members at the
invariant's KV names. -/
theorem casOk_of_cinv (ms : List (client.SrvAt GF)) (γk : KVNames)
    (hs : ∀ x ∈ ms, kvSame x.γr.kv γk) (γ : CNames) :
    cinv (GF := GF) γk γ ⊢ casOk ms γk (seenOk γ) (fun _ => iprop(True)) := by
  iintro #Hinv
  iunfold casOk
  iintro !> %ev %rev #Hev #Hrev
  iapply (BigAndL.bigAndL_intro (P := iprop(cinv (GF := GF) γk γ ∗ (⌜ev = W64 0⌝ ∨ seenOk γ) ∗
      k8s.revOk γk rev))
    (fun _ x hx => casAu γk x.γr.kv (hs x (List.mem_of_getElem? hx)) γ ev rev))
  iframe #

end aus

end k8s_compactor
end EtcdGrove
end Perennial
