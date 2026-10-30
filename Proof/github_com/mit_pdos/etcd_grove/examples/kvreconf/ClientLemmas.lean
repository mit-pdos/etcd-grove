/-
Lean-first (no Rocq counterpart).

# The client's ghost lemmas (2026-10-29, kvreconf-final)

kv's (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/Lemmas.lean`, `kv_mint` to `kv_collect`)
on kvreconf's invariant (`rkvInv`, `Defs.lean`), where they differ:

- `kvr_mint`: the cluster's next operation id (`ghostVar γr.opn`, the other half in the cluster's
  lock) mints the operation's datum (`MintOk`) and its slot, holding the client's atomic update.
- `kvr_mint_read`: a replica's next read sequence number (`γr.rseq`, its element in the replica's
  lock) mints a read's context at `(replica, seq)` and commits it, once, with the update
  `kvr_readAu` (`readCtx_commit_after`: the read sees at least the committed log `l0` the reader
  knew). There is no read credit.
- `kvr_readAns_ok`: what the applier answers such a read with is the key's value in a history
  extending the reader's.
- `kvr_collect`: the client's result, from its slot, with its ticket, given the waiter's answer
  (`waitP`).
- `recvAu_nonblocking`: a receive's atomic update is also a non-blocking receive's (for the
  `select` with a `default` of `propose` and `read`, on a handoff channel).

The atomic updates raft's `Propose` and `ProposeConfChange` take are in `ClientAu.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.PureLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ReadLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Minting, pure -/

section pure
variable [GooseExts]

theorem rkvN_kvrRaftN : (↑rkvN : CoPset) ⊆ ⊤ \ ↑kvrRaftN :=
  mask_ndot_ne' nroot "kvreconf_rkv" "kvreconf_raft" (by decide)

theorem kvrMask_sub : kvrMask ⊆ (⊤ \ ↑kvrRaftN) \ ↑rkvN :=
  Std.LawfulSet.subset_trans Std.LawfulSet.diff_subset_left Std.LawfulSet.diff_subset_left

theorem opId_encodeOp (id : w64) (kind : w8) (key val : List w8) (hk : (key.length : Int) < 2 ^ 64) :
    opId (encodeOp id kind key val) = some id := by
  simp [opId, decodeOp_encodeOp _ _ _ _ hk]

/-- A minted datum is not empty (it decodes). -/
theorem mintedOp_ne_nil (Mi : GMap w64 (List w8)) (d : List w8) (h : MintedOp Mi d) : d ≠ [] := by
  obtain ⟨i, hi, -⟩ := h
  unfold opId at hi
  cases hd : decodeOp d with
  | none => rw [hd] at hi; cases hi
  | some x => exact decodeOp_ne_nil d x hd

theorem mintedOp_insert (Mi : GMap w64 (List w8)) (i : w64) (d x : List w8)
    (H0 : Mi !! i = none) (Hx : MintedOp Mi x) : MintedOp (Mi.insert i d) x := by
  obtain ⟨i', Hi', HMi⟩ := Hx
  have Hne : i ≠ i' := by intro h; subst h; rw [H0] at HMi; cases HMi
  exact ⟨i', Hi', by rw [GMap.lookup_insert_ne _ _ Hne]; exact HMi⟩

theorem mintedRead_insert (RMi : GMap (w64 × w64) (List w8)) (k : w64 × w64) (c x : List w8)
    (H0 : RMi !! k = none) (Hx : MintedRead RMi x) : MintedRead (RMi.insert k c) x := by
  obtain ⟨k', HMi⟩ := Hx
  have Hne : k ≠ k' := by intro h; subst h; rw [H0] at HMi; cases HMi
  exact ⟨k', by rw [GMap.lookup_insert_ne _ _ Hne]; exact HMi⟩

/-- **A fresh operation id** (`n + 1`, the cluster's next): nothing was minted there, so the datum
`d` of that id was not minted, has no slot, and minting it with the slot `γp` keeps the
discipline. -/
theorem mintOk_op (n : w64) (Mi : GMap w64 (List w8)) (RS : GMap w64 w64)
    (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8))
    (d : List w8) (γp : GName × GName) (Hok : MintOk n Mi RS RMi O U)
    (Hn : uint.Z n + 1 < 2 ^ 64) (Hd : opId d = some (n + W64 1)) :
    Mi !! (n + W64 1) = none ∧ ¬ MintedOp Mi d ∧ O !! d = none ∧
      MintOk (n + W64 1) (Mi.insert (n + W64 1) d) RS RMi (O.insert d γp) U := by
  have Hn1 : uint.Z (n + W64 1) = uint.Z n + 1 := by word
  have HMi0 : Mi !! (n + W64 1) = none := by
    cases h : Mi !! (n + W64 1) with
    | none => rfl
    | some d' => have := (Hok.1 _ _ h).1; omega
  have HnM : ¬ MintedOp Mi d := by
    rintro ⟨i, Hi, HMi⟩
    rw [Hd] at Hi; cases Hi
    rw [HMi0] at HMi; cases HMi
  have HO0 : O !! d = none := by
    cases h : O !! d with
    | none => rfl
    | some γ' => exact absurd (Hok.2.2.1 d γ' h) HnM
  refine ⟨HMi0, HnM, HO0, ?_, Hok.2.1, ?_, fun c hc => Hok.2.2.2 c hc⟩
  · intro i d' Hi
    by_cases Heq : i = n + W64 1
    · subst Heq
      rw [GMap.lookup_insert_eq] at Hi; cases Hi
      exact ⟨Int.le_refl _, Hd⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hi
      have := Hok.1 _ _ Hi
      exact ⟨by omega, this.2⟩
  · intro d' γ' Hd'
    by_cases Heq : d' = d
    · subst Heq; exact ⟨n + W64 1, Hd, GMap.lookup_insert_eq _ _ _⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hd'
      exact mintedOp_insert _ _ _ _ HMi0 (Hok.2.2.1 d' γ' Hd')

/-- **A fresh read sequence number** (`ns + 1`, replica `id`'s next): nothing was minted at
`(id, ns + 1)`, so the read's context there was not used, and minting it keeps the discipline. -/
theorem mintOk_read (n : w64) (Mi : GMap w64 (List w8)) (RS : GMap w64 w64)
    (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8))
    (id ns : w64) (key : List w8) (Hok : MintOk n Mi RS RMi O U) (HS : RS !! id = some ns)
    (Hns : uint.Z ns + 1 < 2 ^ 64) (Hk : (key.length : Int) < 2 ^ 64) :
    RMi !! (id, ns + W64 1) = none ∧ readCtxB id (ns + W64 1) key ∉ U ∧
      MintOk n Mi (RS.insert id (ns + W64 1))
        (RMi.insert (id, ns + W64 1) (readCtxB id (ns + W64 1) key)) O
        (insert (readCtxB id (ns + W64 1) key) U) := by
  have Hns1 : uint.Z (ns + W64 1) = uint.Z ns + 1 := by word
  have HRM0 : RMi !! (id, ns + W64 1) = none := by
    cases h : RMi !! (id, ns + W64 1) with
    | none => rfl
    | some c =>
      obtain ⟨ns', Hns', Hle, -⟩ := Hok.2.1 _ _ _ h
      rw [HS] at Hns'; cases Hns'
      omega
  have HU0 : readCtxB id (ns + W64 1) key ∉ U := by
    intro hU
    obtain ⟨⟨r', s'⟩, Hk'⟩ := Hok.2.2.2 _ hU
    obtain ⟨-, -, -, key', Hkl', Hc⟩ := Hok.2.1 r' s' _ Hk'
    have h1 := decodeReadCtxB_readCtxB id (ns + W64 1) key Hk
    rw [Hc, decodeReadCtxB_readCtxB _ _ _ Hkl'] at h1
    cases h1
    rw [HRM0] at Hk'; cases Hk'
  refine ⟨HRM0, HU0, Hok.1, ?_, Hok.2.2.1, ?_⟩
  · intro r s c Hc
    by_cases Heq : (r, s) = (id, ns + W64 1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
      rw [GMap.lookup_insert_eq] at Hc; cases Hc
      exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, Int.le_refl _, key, Hk, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hc
      obtain ⟨ns', Hns', Hle, Hkey⟩ := Hok.2.1 _ _ _ Hc
      by_cases Hr : r = id
      · subst Hr
        rw [HS] at Hns'; cases Hns'
        exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, by omega, Hkey⟩
      · exact ⟨ns', by rw [GMap.lookup_insert_ne _ _ (Ne.symm Hr)]; exact Hns', Hle, Hkey⟩
  · intro c Hc
    by_cases Heq : c = readCtxB id (ns + W64 1) key
    · subst Heq; exact ⟨(id, ns + W64 1), GMap.lookup_insert_eq _ _ _⟩
    · rcases (GMap.elem_of_insert_set c _ U).1 Hc with h | h
      · exact absurd h Heq
      · exact mintedRead_insert _ _ _ _ HRM0 (Hok.2.2.2 c h)

end pure

/-! ## The ghost lemmas -/

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- The client's half of the history's ghost variable agrees with the invariant's. -/
theorem rkvVal_agree (γr : RNames) (H : List (List w8)) (x : KVMap) :
    ⊢ ghostVar (GF := GF) γr.val (1 : Qp).half H -∗ rkvVal γr x -∗ ⌜kvFold H = x⌝ := by
  iintro Hv Hx
  unfold rkvVal
  icases Hx with ⟨%H', Hx, %Hf⟩
  ihave %Heq := ghostVar_agree γr.val H (1 : Qp).half H' (1 : Qp).half $$ Hv Hx
  ipureintro; rw [Heq]; exact Hf

/-- Both halves move to the history `H'`; the client's at its fold. -/
theorem rkvVal_update (γr : RNames) (H : List (List w8)) (x : KVMap) (H' : List (List w8)) :
    ⊢ ghostVar (GF := GF) γr.val (1 : Qp).half H -∗ rkvVal γr x ==∗
      ghostVar γr.val (1 : Qp).half H' ∗ rkvVal γr (kvFold H') := by
  iintro Hv Hx
  unfold rkvVal
  icases Hx with ⟨%H0, Hx, -⟩
  imod ghostVar_update_halves H' γr.val H H0 $$ Hv Hx with ⟨Hv, Hx⟩
  imodintro
  iframe Hv
  iexists H'
  iframe Hx
  ipureintro; rfl

/-- **A fresh operation id mints the operation's datum**, with its slot holding the client's atomic
update and a later credit (see the file header). -/
theorem kvr_mint (γr : RNames) (nop : w64) (kind : w8) (key val : List w8)
    (Ψ : List w8 → IProp GF) (E : CoPset) (HE : ↑rkvN ⊆ E) (Hn : uint.Z nop + 1 < 2 ^ 64)
    (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γr -∗ ghostVar γr.opn (1 : Qp).half nop -∗ £ 1 -∗
      opAu γr (kvNext kind key val) key Ψ ={E}=∗
      ghostVar γr.opn (1 : Qp).half (nop + W64 1) ∗
      ∃ γp : GName × GName, encodeOp (nop + W64 1) kind key val ↪[γr.ops]□ γp ∗
        savedPredOwn γp.1 DFrac.discard Ψ ∗ token γp.2 := by
  iintro #Hinv Hopn Hlc Hau
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn', HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  ihave %Heq := ghostVar_agree γr.opn nop (1 : Qp).half n (1 : Qp).half $$ Hopn Hn'
  subst Heq
  have Hf : (fun x => kvApply x (encodeOp (nop + W64 1) kind key val)) = kvNext kind key val :=
    funext fun x => kvApply_encodeOp x (nop + W64 1) kind key val Hk
  have Hdk : dkey (encodeOp (nop + W64 1) kind key val) = key := dkey_encodeOp _ _ _ _ Hk
  have Hid := opId_encodeOp (nop + W64 1) kind key val Hk
  generalize Hd : encodeOp (nop + W64 1) kind key val = d at Hf Hdk Hid ⊢
  imod saved_pred_alloc Ψ DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod token_alloc (GF := GF) with ⟨%γk, Htok⟩
  obtain ⟨HMi0, HnM, HO0, Hok'⟩ := mintOk_op nop Mi RS RMi O U d (γq, γk) Hok Hn Hid
  have Hdn : d ∉ logHist ops := fun h => HnM (Hodm d ((mem_histOf _ d).mp h))
  imod ghostVar_update_halves (nop + W64 1) γr.opn nop nop $$ Hopn Hn' with ⟨Hopn, Hn'⟩
  imod ghost_map_insert_persist (nop + W64 1) d HMi0 $$ HMi with ⟨HMi, -⟩
  imod ghost_map_insert_persist d ((γq, γk) : GName × GName) HO0 $$ HO with ⟨HO, #Hop⟩
  imod Hclose $$ [Hops Hv HU Hn' HMi HRS HRMi HO Hsl Hlc Hau] with -
  · inext
    iexists ops, nop + W64 1, Mi.insert (nop + W64 1) d, RS, RMi, O.insert d (γq, γk), U
    isplitl [Hops Hv HU Hn' HMi HRS HRMi HO]
    · unfold kvCore
      iframe Hops Hv HU Hn' HMi HRS HRMi HO
      ipureintro
      exact ⟨Hok', fun d' Hd' => mintedOp_insert _ _ _ _ HMi0 (Hodm d' Hd'), Hsh⟩
    iapply (BigSepM.bigSepM_insert (Φ := fun d γp => opSlot (GF := GF) γr d γp (logHist ops))
      HO0).2
    iframe Hsl
    unfold opSlot
    iexists Ψ
    iframe Hsp
    ileft
    iframe Hlc
    isplitr
    · ipureintro; exact Hdn
    rw [Hf, Hdk]; iexact Hau
  imodintro
  iframe Hopn
  iexists (γq, γk)
  iframe Hop Hsp Htok

/-- **A read's update**: the committed requested entries lent and returned, nothing moved (a read
needs nothing of them: `readCtxAfter` gives it the committed log it must see). -/
theorem kvr_readAu (γr : RNames) :
    ⊢ rkvInv (GF := GF) γr -∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvrRaftN, ∅
        <{ ownCommittedOps γr.cluster ops,
           COMM □ (fun _ => iprop(True) : List LogEntry → IProp GF) ops }> := by
  iintro #Hinv
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_kvrRaftN
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hc⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kvrRaftN) \ ↑rkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hc Hsl] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hc
    imodintro
    iempintro
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hc Hsl] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hc
    imodintro
    imodintro
    itrivial

/-- **A fresh read sequence number mints a read's context** at `(id, ns + 1)` and commits it, once,
to the read seeing at least the committed log `l0` the reader knows (`readCtx_commit_after`). -/
theorem kvr_mint_read (γr : RNames) (id ns : w64) (key : List w8) (l0 : List LogEntry)
    (E : CoPset) (HE : ↑rkvN ⊆ E) (Hns : uint.Z ns + 1 < 2 ^ 64) (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γr -∗ id ↪[γr.rseq] ns -∗ isCommittedLogLb γr.cluster l0 ={E}=∗
      id ↪[γr.rseq] (ns + W64 1) ∗
      (id, ns + W64 1) ↪[γr.rmint]□ readCtxB id (ns + W64 1) key ∗
      isReadCtx γr.cluster kvrRaftN (readCtxB id (ns + W64 1) key)
        (fun _ => iprop(True)) ∗
      readCtxAfter γr.cluster kvrRaftN (readCtxB id (ns + W64 1) key) l0 := by
  iintro #Hinv Hseq #Hl0
  ihave #Hau := kvr_readAu γr $$ Hinv
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  icases ghost_map_lookup $$ HRS Hseq with %HSi
  obtain ⟨HRM0, HU0, Hok'⟩ := mintOk_read n Mi RS RMi O U id ns key Hok HSi Hns Hk
  generalize Hd : readCtxB id (ns + W64 1) key = c at HRM0 HU0 Hok' ⊢
  imod ghost_map_update (ns + W64 1) $$ HRS Hseq with ⟨HRS, Hseq⟩
  imod ghost_map_insert_persist (id, ns + W64 1) c HRM0 $$ HRMi with ⟨HRMi, #Hmint⟩
  ihave Hcm := readCtx_commit_after γr.cluster kvrRaftN U c (fun _ => iprop(True)) l0 HU0
    $$ [HU Hau Hl0]
  · iframe HU Hau Hl0
  imod Hcm with ⟨HU, #Hrc, #Hra⟩
  imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
  · inext
    iexists ops, n, Mi, RS.insert id (ns + W64 1), RMi.insert (id, ns + W64 1) c, O, insert c U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU Hn HMi HRS HRMi HO
    ipureintro; exact ⟨Hok', Hodm, Hsh⟩
  imodintro
  iframe Hseq Hmint Hrc Hra

/-- **What the applier answers a read with** (`readAns`, of the context minted at `(id, s)`): the
key's value in a history that extends the reader's (`l0`'s, which the read state's index covers:
`readStateOk_after`). -/
theorem kvr_readAns_ok (γr : RNames) (id s : w64) (key : List w8) (l0 : List LogEntry)
    (v : List w8) (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ readCtxAfter (GF := GF) γr.cluster kvrRaftN (readCtxB id s key) l0 -∗
      isCommittedLogLb γr.cluster l0 -∗ readAns γr (readCtxB id s key) v -∗
      ∃ L, kvLb γr L ∗ ⌜logHist l0 <+: L ∧ v = kvFold L key⌝ := by
  iintro #Hra #Hl0 Hans
  iunfold readAns at Hans
  icases Hans with ⟨%i, %ap, %key', #Hok, #Hap, %Hfacts⟩
  obtain ⟨Hle, ⟨rp, s', Hdec⟩, Hv⟩ := Hfacts
  rw [decodeReadCtxB_readCtxB _ _ _ Hk] at Hdec
  cases Hdec
  ihave %Hl0i := readStateOk_after γr.cluster kvrRaftN _ i l0 $$ [Hok Hra]
  · iframe Hok Hra
  ihave %Hagr := isCommittedLogLb_agree γr.cluster l0 ap $$ [Hl0 Hap]
  · iframe Hl0 Hap
  have Hpre : l0 <+: ap := by
    rcases Hagr with h | h
    · exact h
    · have h1 := h.length_le
      have hl : l0.length = ap.length := by word
      rw [List.prefix_iff_eq_take] at h
      rw [h, List.take_of_length_le (by omega)]; exact List.prefix_refl _
  iexists logHist ap
  isplitl
  · unfold kvLb
    iexists ap
    iframe Hap
    ipureintro; rfl
  ipureintro
  exact ⟨logHist_prefix _ _ Hpre, Hv⟩

/-- **Collecting an operation's result**: given the waiter's answer `v` (`waitP`: `d`'s answer in a
committed log's history), the ticket buys the client's result at `v`, under two laters (the
invariant it was stored in; the saved predicate naming it). -/
theorem kvr_collect (γr : RNames) (d : List w8) (γp : GName × GName) (Ψ : List w8 → IProp GF)
    (v : List w8) (E : CoPset) (HE1 : ↑rkvN ⊆ E) :
    ⊢ rkvInv (GF := GF) γr -∗ d ↪[γr.ops]□ γp -∗
      savedPredOwn γp.1 DFrac.discard Ψ -∗ token γp.2 -∗ waitP γr d v ={E}=∗ ▷ ▷ Ψ v := by
  iintro #Hinv #Hop #Hsp Htok #Hw
  iunfold waitP at Hw
  icases Hw with ⟨%l, #Hl, %Hans⟩
  obtain ⟨H1, HH1, Hd1, Hv⟩ := Hans
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv', HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γr.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  icases ghost_map_lookup $$ HO Hop with %HOd
  have Hocc : H1 ++ [d] <+: logHist ops := HH1.trans (logHist_le_ops l ops Hpre)
  have HdL : d ∈ logHist ops :=
    Hocc.subset (List.mem_append_right _ (List.mem_singleton_self d))
  ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
  icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
    iprop(▷ opSlot (GF := GF) γr d γp (logHist ops))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
  iunfold opSlot at Hsd
  icases Hsd with ⟨%Φ', #Hsp', Hst⟩
  icases Hst with (⟨>%Hn', -, -⟩ | ⟨%H0, >%HH0, HQ⟩)
  · exact absurd HdL Hn'
  have HH0eq : H0 = H1 :=
    hist_prefix_before_unique _ _ _ d (histOf_nodup _) HH0.1 Hocc
  subst HH0eq
  subst Hv
  icases HQ with (HQ | >Htok')
  · ihave #Heq : ▷ ▷ (Φ' (kvFold (H0 ++ [d]) (dkey d)) ≡ Ψ (kvFold (H0 ++ [d]) (dkey d))) $$ []
    · inext
      iapply saved_pred_agree γp.1 DFrac.discard DFrac.discard Φ' Ψ _ $$ Hsp' Hsp
    imod Hclose $$ [Hops Hv' HU Hn HMi HRS HRMi HO Hsl Htok] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      isplitl [Hops Hv' HU Hn HMi HRS HRMi HO]
      · unfold kvCore
        iframe Hops Hv' HU Hn HMi HRS HRMi HO
        ipureintro; exact ⟨Hok, Hodm, Hsh⟩
      iapply (BigSepM.bigSepM_delete (Φ := fun d γp =>
        opSlot (GF := GF) γr d γp (logHist ops)) HOd).2
      iframe Hsl
      unfold opSlot
      iexists Φ'
      iframe Hsp'
      iright
      iexists H0
      iframe Htok
      ipureintro; exact HH0
    imodintro
    inext
    inext
    ihave Hiff := internalEq_iff _ _ $$ Heq
    icases Hiff with ⟨Hiff, -⟩
    iapply Hiff $$ HQ
  · iexfalso
    iapply token_exclusive $$ Htok Htok'

/-- A waiter dropped from the replica's waiters (`propose`, after its timeout). -/
theorem waiters_drop (γr : RNames) (W : GMap (List w8) Loc) (d : List w8) :
    ([∗map] k ↦ c ∈ W, waiterOk (GF := GF) γr k c) ⊢
      [∗map] k ↦ c ∈ GMap.delete d W, waiterOk γr k c := by
  cases h : W !! d with
  | none =>
    rw [GMap.delete_notin W d h]
  | some x =>
    iintro H
    icases (BigSepM.bigSepM_delete (Φ := fun k c => waiterOk (GF := GF) γr k c) h).1 $$ H
      with ⟨-, H⟩
    iexact H

/-- A read dropped from the replica's waiting reads (`read`, after its timeout). -/
theorem reads_drop (γr : RNames) (id : w64) (Rd : GMap w64 Loc) (s : w64) :
    ([∗map] k ↦ c ∈ Rd, readWaiterOk (GF := GF) γr id k c) ⊢
      [∗map] k ↦ c ∈ GMap.delete s Rd, readWaiterOk γr id k c := by
  cases h : Rd !! s with
  | none =>
    rw [GMap.delete_notin Rd s h]
  | some x =>
    iintro H
    icases (BigSepM.bigSepM_delete (Φ := fun k c => readWaiterOk (GF := GF) γr id k c) h).1 $$ H
      with ⟨-, H⟩
    iexact H

/-- **A receive's atomic update is a non-blocking receive's** (whose not-ready case, an empty
buffer or a waiting receiver, asks nothing). -/
theorem recvAu_nonblocking {V : Type} [Pos.Countable V] [ZeroVal V] (γ : ChanNames) (Φ : V → Bool → IProp GF) :
    ⊢ recvAu γ V Φ -∗ nonblockingRecvAuInner γ V Φ := by
  unfold recvAu nonblockingRecvAuInner
  iintro Hau
  imod Hau with Hau
  imodintro
  inext
  icases Hau with ⟨%s, Hoc, Hcont⟩
  iexists s
  iframe Hoc
  rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals first
    | iexact Hcont
    | itrivial

end lemmas

end kvreconf
end EtcdGrove
end Perennial
