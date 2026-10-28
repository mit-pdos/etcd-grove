/-
Lean-first (no Rocq counterpart).

# The key-value store's ghost lemmas (2026-10-10; 2026-10-27: over raft's draft API)

- `kvStor_register`: a new storage joins the registry (`kvStorInv`, `Defs.lean`).
- `kv_mint`: a new sequence number mints the operation's datum (`MintOk`) and the operation's
  slot, holding the client's atomic update (`opSlot`).
- `kv_mint_read`: a new sequence number mints a read's context and commits it, once, to the read
  seeing what the reader knew to be committed (`readCtx_commit`, with the update `kv_readAu`).
- `kvLb_current`: the history now is a lower bound (`kvLb`), at the client's state.
- `kv_propAu`: the atomic update over the committed requested entries (`ownCommittedOps`)
  that `Node.Propose` takes for an operation's datum, fired at most once: the history moves by the
  datum, and at its first occurrence the client's update runs from the operation's slot (the
  linearization point); `kv_ccAu`, `RemoveMember`'s conf change's (no datum).
- `kv_collect`: the client's result, from its slot, with its ticket.
- `rkvVal_agree`, `rkvVal_update`: the client's half of the history's ghost variable against the
  invariant's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The applier's table, pure -/

theorem histStep_mem (L : List (List w8)) (d : List w8) (h : d ∈ L) : histStep L (some d) = L := by
  show (if d ∈ L then _ else _) = _; rw [ite_eq_left h]

theorem histStep_nmem (L : List (List w8)) (d : List w8) (h : d ∉ L) :
    histStep L (some d) = L ++ [d] := by
  show (if d ∈ L then _ else _) = _; rw [ite_eq_right h]

theorem appliedOk_skip (A : GMap (List w8) (List w8)) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hd : decodeOp d = none ∨ d ∈ L) : AppliedOk A (histStep L (some d)) := by
  by_cases Hm : d ∈ L
  · rw [histStep_mem L d Hm]; exact HA
  · have Hd' : decodeOp d = none := by rcases Hd with h | h; exact h; exact absurd h Hm
    rw [histStep_nmem L d Hm]
    refine ⟨fun d' => ?_, fun d' v h => ansOk_mono _ _ _ _ (List.prefix_append _ _) (HA.2 d' v h)⟩
    rw [HA.1 d']
    by_cases Heq : d' = d
    · subst Heq; simp [Hd', Hm]
    · simp [List.mem_append, Heq]

/-- (2026-10-22) The first occurrence of `d` applied: the table records its answer, the key's
value after it. -/
theorem appliedOk_insert (A : GMap (List w8) (List w8)) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hm : d ∉ L) (Hd : (decodeOp d).isSome) :
    AppliedOk (A.insert d (kvFold (L ++ [d]) (dkey d))) (L ++ [d]) := by
  refine ⟨fun d' => ?_, fun d' v h => ?_⟩
  · show (A.insert d (kvFold (L ++ [d]) (dkey d)) !! d').isSome ↔ _
    by_cases Heq : d' = d
    · subst Heq; rw [GMap.lookup_insert_eq]; simp [Hd]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq), HA.1 d']
      simp [List.mem_append, Heq]
  · by_cases Heq : d' = d
    · subst Heq
      have h' : A.insert d' (kvFold (L ++ [d']) (dkey d')) !! d' = some v := h
      rw [GMap.lookup_insert_eq] at h'
      cases h'
      exact ansOk_last L d' Hm
    · have h' : A.insert d (kvFold (L ++ [d]) (dkey d)) !! d' = some v := h
      rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at h'
      exact ansOk_mono _ _ _ _ (List.prefix_append _ _) (HA.2 d' v h')

theorem appliedOk_lookup (A : GMap (List w8) (List w8)) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hd : (decodeOp d).isSome) : (A !! d).isSome = decide (d ∈ L) := by
  have h := HA.1 d
  by_cases Hm : d ∈ L
  · simp only [Hm, Hd, and_self, iff_true] at h; simp [Hm, h]
  · simp only [Hm, false_and, iff_false] at h; simp [Hm, h]

/-- A datum's first occurrence in `ods`: at `m`, not in the history before it. -/
theorem histOf_first (ods : List (Option (List w8))) (d : List w8) (h : some d ∈ ods) :
    ∃ m, ods[m]? = some (some d) ∧ d ∉ histOf (ods.take m) := by
  suffices H : ∃ m, ods[m]? = some (some d) ∧ some d ∉ ods.take m by
    obtain ⟨m, h1, h2⟩ := H
    exact ⟨m, h1, fun h' => h2 ((mem_histOf _ d).1 h')⟩
  induction ods with
  | nil => cases h
  | cons x ods ih =>
    by_cases hx : x = some d
    · subst hx; exact ⟨0, rfl, by simp⟩
    · have hin : some d ∈ ods := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨m, hm, hm2⟩ := ih hin
      refine ⟨m + 1, by simpa using hm, ?_⟩
      simp only [List.take_succ_cons, List.mem_cons, not_or]
      exact ⟨fun h' => hx h'.symm, hm2⟩

/-- (2026-10-22) Where the answer of an operation of the history `histOf ods` comes from: the
entry of its first occurrence in `ods`, at `m`, after which the key's value is the answer (what
`waitP` says of an answer). -/
theorem ansOk_histOf (ods : List (Option (List w8))) (d v : List w8)
    (h : AnsOk (histOf ods) d v) :
    ∃ m, ods[m]? = some (some d) ∧ d ∉ histOf (ods.take m) ∧
      v = kvFold (histOf (ods.take m) ++ [d]) (dkey d) := by
  obtain ⟨H0, Hpre, -, Hv⟩ := h
  obtain ⟨m, hm, hm2⟩ :=
    histOf_first ods d ((mem_histOf ods d).1 (Hpre.subset (by simp)))
  have Hsplit : ods.take (m + 1) = ods.take m ++ [some d] := by
    rw [List.take_add_one, hm]; rfl
  have Hp1 : histOf (ods.take m) ++ [d] <+: histOf ods := by
    have h1 : histOf (ods.take (m + 1)) = histOf (ods.take m) ++ [d] := by
      rw [Hsplit, histOf_snoc, histStep_nmem _ _ hm2]
    rw [← h1]
    have h2 := histOf_append_prefix (ods.take (m + 1)) (ods.drop (m + 1))
    rwa [List.take_append_drop] at h2
  have HH0 := hist_prefix_before_unique (histOf ods) H0 (histOf (ods.take m)) d
    (histOf_nodup ods) Hpre Hp1
  subst HH0
  exact ⟨m, hm, hm2, Hv⟩

theorem histOf_prefix_of_prefix (a b : List (Option (List w8))) (h : a <+: b) :
    histOf a <+: histOf b := by
  obtain ⟨t, rfl⟩ := h
  exact histOf_append_prefix a t

/-- The history of a log's prefix `l` is a prefix of the history of committed requested entries
`ops` extending its requested entries. -/
theorem logHist_le_ops [GooseExts] (l ops : List LogEntry) (h : opsOf l <+: ops) :
    logHist l <+: logHist ops := by
  rw [← logHist_opsOf l]; exact logHist_prefix _ _ h

/-! ## Minting, pure -/

/-- Minting is kept by a new key. -/
theorem minted_insert [GooseExts] (Mi : GMap (w64 × w64) (List w8)) (k : w64 × w64) (d x : List w8)
    (H0 : Mi !! k = none) (Hx : Minted Mi x) : Minted (Mi.insert k d) x := by
  obtain ⟨k', Hk', HMi⟩ := Hx
  have Hne : k ≠ k' := by intro h; subst h; rw [H0] at HMi; cases HMi
  exact ⟨k', Hk', by rw [GMap.lookup_insert_ne _ _ Hne]; exact HMi⟩

theorem minted_new [GooseExts] (Mi : GMap (w64 × w64) (List w8)) (k : w64 × w64) (d : List w8)
    (Hk : opKey d = some k) : Minted (Mi.insert k d) d :=
  ⟨k, Hk, GMap.lookup_insert_eq _ _ _⟩

/-- A new sequence number's key is fresh: no datum minted there, so the datum is not minted, has no
slot and is no used read context. -/
theorem mintOk_fresh [GooseExts] (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8))
    (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)) (id ns : w64)
    (d : List w8) (Hok : MintOk S Mi O U) (HS : S !! id = some ns)
    (Hkey : opKey d = some (id, ns + W64 1)) (Hns : uint.Z ns + 1 < 2 ^ 64) :
    Mi !! (id, ns + W64 1) = none ∧ ¬ Minted Mi d ∧ O !! d = none ∧ d ∉ U := by
  have HMi0 : Mi !! (id, ns + W64 1) = none := by
    cases h : Mi !! (id, ns + W64 1) with
    | none => rfl
    | some d' =>
      obtain ⟨n, Hn, Hle⟩ := Hok.1 _ _ _ h
      rw [HS] at Hn; cases Hn
      have : uint.Z (ns + W64 1) = uint.Z ns + 1 := by word
      omega
  have HnM : ¬ Minted Mi d := by
    rintro ⟨k, Hk, Hk'⟩
    rw [Hkey] at Hk; cases Hk
    rw [HMi0] at Hk'; cases Hk'
  refine ⟨HMi0, HnM, ?_, fun h => HnM (Hok.2.2 d h)⟩
  cases h : O !! d with
  | none => rfl
  | some γp => exact absurd (Hok.2.1 d γp h) HnM

/-- Minting `d` at a new sequence number. -/
theorem mintOk_step [GooseExts] (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8))
    (O O' : GMap (List w8) (GName × GName)) (U U' : GSet (List w8)) (id ns : w64) (d : List w8)
    (Hok : MintOk S Mi O U) (HS : S !! id = some ns) (Hkey : opKey d = some (id, ns + W64 1))
    (Hns : uint.Z ns + 1 < 2 ^ 64)
    (HO' : ∀ d' γp, O' !! d' = some γp → O !! d' = some γp ∨ d' = d)
    (HU' : ∀ c, c ∈ U' → c ∈ U ∨ c = d) :
    MintOk (S.insert id (ns + W64 1)) (Mi.insert (id, ns + W64 1) d) O' U' := by
  obtain ⟨HMi0, -, -, -⟩ := mintOk_fresh S Mi O U id ns d Hok HS Hkey Hns
  refine ⟨?_, ?_, ?_⟩
  · intro i s d' Hs
    by_cases Hk : (i, s) = (id, ns + W64 1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hk
      exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, Int.le_refl _⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hk)] at Hs
      obtain ⟨n, Hn, Hle⟩ := Hok.1 _ _ _ Hs
      by_cases Hi : i = id
      · subst Hi
        rw [HS] at Hn; cases Hn
        exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, by word⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hi)]
        exact ⟨n, Hn, Hle⟩
  · intro d' γp Hd'
    rcases HO' d' γp Hd' with h | rfl
    · exact minted_insert _ _ _ _ HMi0 (Hok.2.1 d' γp h)
    · exact minted_new _ _ _ Hkey
  · intro c Hc
    rcases HU' c Hc with h | rfl
    · exact minted_insert _ _ _ _ HMi0 (Hok.2.2 c h)
    · exact minted_new _ _ _ Hkey

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The client's half of the history's ghost variable agrees with the invariant's: its state
is the history's fold. -/
theorem rkvVal_agree (γr : RKVNames) (H : List (List w8)) (x : KVMap) :
    ⊢ ghostVar (GF := GF) γr.val (1 : Qp).half H -∗ rkvVal γr x -∗ ⌜kvFold H = x⌝ := by
  iintro Hv Hx
  unfold rkvVal
  icases Hx with ⟨%H', Hx, %Hf⟩
  ihave %Heq := ghostVar_agree γr.val H (1 : Qp).half H' (1 : Qp).half $$ Hv Hx
  ipureintro; rw [Heq]; exact Hf

/-- Both halves move to the history `H'`; the client's at its fold. -/
theorem rkvVal_update (γr : RKVNames) (H : List (List w8)) (x : KVMap) (H' : List (List w8)) :
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

/-- A pointer-valued location wholly owned has no other fraction. -/
theorem loc_pointsto_excl (l : Loc) (v1 v2 : Loc) (q : Qp) :
    ⊢ (l ↦ v1 : IProp GF) -∗ l ↦{DFrac.own q} v2 -∗ False := by
  iintro H1 H2
  ihave H1 := typedPointsto_split _ _ _ $$ H1
  ihave H2 := typedPointsto_split _ _ _ $$ H2
  have h : ∀ (v : Loc) (dq : DFrac),
      typedPointstoDef (GF := GF) l v dq = heapPointsto l dq #v := fun _ _ => rfl
  rw [h, h]
  icombine H1 H2 gives %H
  exfalso
  have := DFrac.valid_own_op H.1
  have h1 : (1 : Qp).val = 1 := rfl
  have h2 : 0 < q.val := q.property
  grind

/-- A new storage joins the registry. -/
theorem kvStor_register (s ms : Loc) (γs : MemStorNames) (E : CoPset) (HE : ↑kvStorN ⊆ E) :
    ⊢ kvStorInv (GF := GF) -∗ s.[RStorage, go!"MemoryStorage"] ↦ ms ={E}=∗
      kvStorRec s ms γs := by
  iintro #Hinv Hf
  unfold kvStorInv
  iinv Hinv with >Hi Hclose
  unfold kvStorInvBody
  icases Hi with ⟨%M, Ha, Hm⟩
  cases HM : M !! s with
  | some x =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (s : Loc) (x : MemStorRec) =>
      iprop(s.[RStorage, go!"MemoryStorage"] ↦{DFrac.own (1 : Qp).half} x.1)) HM).1 $$ Hm
      with ⟨Hx, -⟩
    iexfalso
    iapply loc_pointsto_excl $$ Hf Hx
  | none =>
    imod ghost_map_insert_persist s (memStorRec ms γs) HM $$ Ha with ⟨Ha, #Hfrag⟩
    icases (typedPointsto_dfractional (GF := GF) (s.[RStorage, go!"MemoryStorage"]) ms).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [Hf] with ⟨Hf1, Hf2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hf
    imod (typedPointsto_dfractional (GF := GF) _ ms).dfractional_persist _ $$ Hf2 with #Hf2
    imod Hclose $$ [Ha Hm Hf1] with -
    · inext
      iexists M.insert s (memStorRec ms γs)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (s : Loc) (x : MemStorRec) =>
        iprop(s.[RStorage, go!"MemoryStorage"] ↦{DFrac.own (1 : Qp).half} x.1)) HM).2
      iframe Hm
      unfold memStorRec
      iexact Hf1
    imodintro
    unfold kvStorRec
    iframe Hf2 Hfrag

/-- A new sequence number mints the operation's datum and records it; the operation's slot, with
the client's atomic update and a later credit. -/
theorem kv_mint (γr : RKVNames) (id ns : w64) (kind : w8) (key val : List w8)
    (Ψ : List w8 → IProp GF) (E : CoPset) (HE : ↑rkvN ⊆ E) (Hns : uint.Z ns + 1 < 2 ^ 64)
    (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γr -∗ id ↪[γr.seq] ns -∗ £ 1 -∗ opAu γr (kvNext kind key val) key Ψ ={E}=∗
      id ↪[γr.seq] (ns + W64 1) ∗
      (id, ns + W64 1) ↪[γr.mint]□ encodeOp id (ns + W64 1) kind key val ∗
      ∃ γp : GName × GName, encodeOp id (ns + W64 1) kind key val ↪[γr.ops]□ γp ∗
        savedPredOwn γp.1 DFrac.discard Ψ ∗ token γp.2 := by
  iintro #Hinv Hseq Hlc Hau
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  icases ghost_map_lookup $$ HS Hseq with %HSi
  have Hf : (fun x => kvApply x (encodeOp id (ns + W64 1) kind key val)) = kvNext kind key val :=
    funext fun x => kvApply_encodeOp x id (ns + W64 1) kind key val Hk
  have Hdk : dkey (encodeOp id (ns + W64 1) kind key val) = key := dkey_encodeOp _ _ _ _ _ Hk
  generalize Hd : encodeOp id (ns + W64 1) kind key val = d at Hf Hdk ⊢
  have Hkey : opKey d = some (id, ns + W64 1) := by rw [← Hd]; exact opKey_encodeOp _ _ _ _ _ Hk
  obtain ⟨HMi0, HnM, HO0, -⟩ := mintOk_fresh S Mi O U id ns d Hok HSi Hkey Hns
  have Hdn : d ∉ logHist ops := fun h => HnM (Hodm d ((mem_histOf _ d).mp h))
  imod ghost_map_update (ns + W64 1) $$ HS Hseq with ⟨HS, Hseq⟩
  imod ghost_map_insert_persist (id, ns + W64 1) d HMi0 $$ HMi with ⟨HMi, #Hmint⟩
  imod saved_pred_alloc Ψ DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod token_alloc (GF := GF) with ⟨%γk, Htok⟩
  imod ghost_map_insert_persist d ((γq, γk) : GName × GName) HO0 $$ HO with ⟨HO, #Hop⟩
  imod Hclose $$ [Hops Hv HU HS HMi HO Hsl Hlc Hau] with -
  · inext
    iexists ops, S.insert id (ns + W64 1), Mi.insert (id, ns + W64 1) d, O.insert d (γq, γk), U
    isplitl [Hops Hv HU HS HMi HO]
    · unfold kvCore
      iframe Hops Hv HU HS HMi HO
      ipureintro
      refine ⟨mintOk_step S Mi O _ U U id ns d Hok HSi Hkey Hns ?_ (fun c h => .inl h), ?_, ?_⟩
      · intro d' γp' Hd'
        by_cases Heq : d' = d
        · exact .inr Heq
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hd'; exact .inl Hd'
      · intro d' Hd'
        exact minted_insert _ _ _ _ HMi0 (Hodm d' Hd')
      · exact Hrm
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
  iframe Hseq Hmint
  iexists (γq, γk)
  iframe Hop Hsp Htok

/-- A read's update: the committed requested entries lent and returned, nothing moved; it gives
that they extend the requested entries of `l0`, a committed log the reader knew. -/
theorem kv_readAu (γr : RKVNames) (l0 : List LogEntry) :
    ⊢ rkvInv (GF := GF) γr -∗ isCommittedLogLb γr.cluster l0 -∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvRaftN, ∅
        <{ ownCommittedOps γr.cluster ops,
           COMM □ (fun ops => iprop(⌜opsOf l0 <+: ops⌝) : List LogEntry → IProp GF) ops }> := by
  iintro #Hinv #Hl0
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_raftN
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γr.cluster ops l0 $$ [Hops Hl0]
  · iframe Hops Hl0
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kvRaftN) \ ↑rkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
    · inext
      iexists ops, S, Mi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hv HU HS HMi HO
      ipureintro; exact ⟨Hok, Hodm, Hrm⟩
    imodintro
    iempintro
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
    · inext
      iexists ops, S, Mi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hv HU HS HMi HO
      ipureintro; exact ⟨Hok, Hodm, Hrm⟩
    imodintro
    imodintro
    ipureintro; exact Hpre

/-- A new sequence number mints a read's context and commits it, once, to the read seeing the
requested entries of `l0`, a committed log the reader knows (`readCtx_commit`). -/
theorem kv_mint_read (γr : RKVNames) (id ns : w64) (key : List w8) (l0 : List LogEntry)
    (E : CoPset) (HE : ↑rkvN ⊆ E) (Hns : uint.Z ns + 1 < 2 ^ 64) (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γr -∗ id ↪[γr.seq] ns -∗ isCommittedLogLb γr.cluster l0 ={E}=∗
      id ↪[γr.seq] (ns + W64 1) ∗
      (id, ns + W64 1) ↪[γr.mint]□ encodeOp id (ns + W64 1) opReadB key [] ∗
      isReadCtx γr.cluster kvRaftN (encodeOp id (ns + W64 1) opReadB key [])
        (fun ops => iprop(⌜opsOf l0 <+: ops⌝)) := by
  iintro #Hinv Hseq #Hl0
  ihave #Hau := kv_readAu γr l0 $$ Hinv Hl0
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  icases ghost_map_lookup $$ HS Hseq with %HSi
  generalize Hd : encodeOp id (ns + W64 1) opReadB key [] = d
  have Hkey : opKey d = some (id, ns + W64 1) := by rw [← Hd]; exact opKey_encodeOp _ _ _ _ _ Hk
  obtain ⟨HMi0, -, -, HU0⟩ := mintOk_fresh S Mi O U id ns d Hok HSi Hkey Hns
  imod ghost_map_update (ns + W64 1) $$ HS Hseq with ⟨HS, Hseq⟩
  imod ghost_map_insert_persist (id, ns + W64 1) d HMi0 $$ HMi with ⟨HMi, #Hmint⟩
  ihave Hcm := readCtx_commit γr.cluster kvRaftN U d
      (fun ops => iprop(⌜opsOf l0 <+: ops⌝)) HU0 $$ [HU Hau]
  · iframe HU Hau
  imod Hcm with ⟨HU, #Hrc⟩
  imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
  · inext
    iexists ops, S.insert id (ns + W64 1), Mi.insert (id, ns + W64 1) d, O, insert d U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU HS HMi HO
    ipureintro
    refine ⟨mintOk_step S Mi O O U _ id ns d Hok HSi Hkey Hns (fun d' γp h => .inl h) ?_, ?_, ?_⟩
    · intro c Hc
      by_cases Heq : c = d
      · exact .inr Heq
      · left
        rcases (GMap.elem_of_insert_set c d U).1 Hc with h | h
        · exact absurd h Heq
        · exact h
    · intro d' Hd'
      exact minted_insert _ _ _ _ HMi0 (Hodm d' Hd')
    · exact Hrm
  imodintro
  iframe Hseq Hmint Hrc

/-- A read state's context with a minted key is the one minted there: it was committed
(`readStateOk_used`), so minted. -/
theorem kv_read_minted (γr : RKVNames) (c c0 : List w8) (i : w64) (k : w64 × w64) (E : CoPset)
    (HE : ↑rkvN ⊆ E) (Hk : opKey c = some k) :
    ⊢ rkvInv (GF := GF) γr -∗ readStateOk γr.cluster kvRaftN c i -∗
      k ↪[γr.mint]□ c0 ={E}=∗ ⌜c0 = c⌝ := by
  iintro #Hinv #Hok #Hmint
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  ihave %HcU := readStateOk_used γr.cluster kvRaftN c i U $$ [Hok HU]
  · iframe Hok HU
  obtain ⟨k', Hk', HMik⟩ := Hok.2.2 c HcU
  rw [Hk] at Hk'; cases Hk'
  icases ghost_map_lookup $$ HMi Hmint with %HMi0
  rw [HMik] at HMi0
  cases HMi0
  imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
  · inext
    iexists ops, S, Mi, O, U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU HS HMi HO
    ipureintro; exact ⟨Hok, Hodm, Hrm⟩
  imodintro
  ipureintro; rfl

/-- A datum of a committed entry is a datum of its requested entries (a filler has none). -/
theorem odOf_mem_opsOf [GooseExts] (l : List LogEntry) (d : List w8)
    (h : some d ∈ l.map odOf) : some d ∈ (opsOf l).map odOf := by
  obtain ⟨e, he, hd⟩ := List.mem_map.1 h
  refine List.mem_map.2 ⟨e, ?_, hd⟩
  unfold opsOf
  refine List.mem_filter.2 ⟨he, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  intro hf; rw [odOf_filler e hf] at hd; cases hd

/-- A datum of a committed log with a minted key is the one minted there: every committed
datum was minted (only the store's updates move the committed requested entries). -/
theorem kv_committed_minted (γr : RKVNames) (l : List LogEntry) (d d0 : List w8)
    (k : w64 × w64) (E : CoPset) (HE : ↑rkvN ⊆ E) (Hd : some d ∈ l.map odOf)
    (Hk : opKey d = some k) :
    ⊢ rkvInv (GF := GF) γr -∗ isCommittedLogLb γr.cluster l -∗
      k ↪[γr.mint]□ d0 ={E}=∗ ⌜d0 = d⌝ := by
  iintro #Hinv #Hl #Hmint
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γr.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  have Hd' : some d ∈ ops.map odOf :=
    (Hpre.map odOf).subset (odOf_mem_opsOf l d Hd)
  obtain ⟨k', Hk', HMik⟩ := Hodm d Hd'
  rw [Hk] at Hk'; cases Hk'
  icases ghost_map_lookup $$ HMi Hmint with %HMi0
  rw [HMik] at HMi0
  cases HMi0
  imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
  · inext
    iexists ops, S, Mi, O, U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU HS HMi HO
    ipureintro; exact ⟨Hok, Hodm, Hrm⟩
  imodintro
  ipureintro; rfl

/-- The history now is a lower bound, at the client's state. -/
theorem kvLb_current (γr : RKVNames) (x : KVMap) (E : CoPset) (HE1 : ↑rkvN ⊆ E) :
    ⊢ rkvInv (GF := GF) γr -∗ rkvVal γr x ={E}=∗
      rkvVal γr x ∗ ∃ L, kvLb γr L ∗ ⌜kvFold L = x⌝ := by
  iintro #Hinv Hx
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  ihave %Hxeq := rkvVal_agree γr (logHist ops) x $$ Hv Hx
  icases ownCommittedOps_get_lb γr.cluster ops $$ Hops with ⟨Hops, %l, #Hl, %Hl⟩
  imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
  · inext
    iexists ops, S, Mi, O, U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU HS HMi HO
    ipureintro; exact ⟨Hok, Hodm, Hrm⟩
  imodintro
  iframe Hx
  iexists logHist ops
  isplitl
  · unfold kvLb
    iexists l
    iframe Hl
    ipureintro; rw [← Hl, logHist_opsOf]
  ipureintro; exact Hxeq

/-- A slot of another datum keeps its state as the history grows by `d`. -/
theorem opSlot_grow (γr : RKVNames) (d' d : List w8) (γp : GName × GName) (H : List (List w8))
    (Hne : d' ≠ d) :
    ⊢ opSlot (GF := GF) γr d' γp H -∗ opSlot γr d' γp (H ++ [d]) := by
  unfold opSlot
  iintro ⟨%Φ, #Hsp, Hst⟩
  iexists Φ
  iframe Hsp
  icases Hst with (⟨%Hn, Hlc, Hau⟩ | ⟨%H0, %Hp, HQ⟩)
  · ileft
    iframe Hlc Hau
    ipureintro
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨Hn, Hne⟩
  · iright
    iexists H0
    iframe HQ
    ipureintro
    exact ⟨Hp.1.trans (List.prefix_append _ _), Hp.2⟩

/-- **The update `Node.Propose` takes** for the operation's datum `d` (non-empty), whose slot is
`γp` (see the file header): when an entry of it commits, the history moves by `d`; at its first
occurrence (`d` not yet in the history) the client's update runs from the slot, with the slot's
later credit. Persistent: every proposal of `d`, a retry included, gets one. -/
theorem kv_propAu (γr : RKVNames) (d : List w8) (γp : GName × GName) (Hne : d ≠ []) :
    ⊢ rkvInv (GF := GF) γr -∗ d ↪[γr.ops]□ γp -∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvRaftN, ∅
        <{ ∀∀ (t : w64), ownCommittedOps γr.cluster (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]),
           COMM True }> := by
  iintro #Hinv #Hop
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_raftN
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  icases ghost_map_lookup $$ HO Hop with %HOd
  have HMd : Minted Mi d := Hok.2.1 d γp HOd
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kvRaftN) \ ↑rkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · -- abort: nothing moved
    iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
    · inext
      iexists ops, S, Mi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hv HU HS HMi HO
      ipureintro; exact ⟨Hok, Hodm, Hrm⟩
    imodintro
    iempintro
  · -- commit: the requested entries grow by `d`'s
    iintro %t Hops
    imod Hclose2 with -
    have Hod : odOf (⟨t, W32 0, d⟩ : LogEntry) = some d := by
      unfold odOf; rw [if_pos ⟨rfl, Hne⟩]
    have Hhist : logHist (ops ++ [⟨t, W32 0, d⟩]) = histStep (logHist ops) (some d) := by
      unfold logHist; rw [List.map_append, List.map_singleton, Hod, histOf_snoc]
    have Hodm' : ∀ d', some d' ∈ (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]).map odOf → Minted Mi d' := by
      intro d' h
      rw [List.map_append, List.map_singleton, Hod] at h
      rcases List.mem_append.mp h with h | h
      · exact Hodm d' h
      · simp only [List.mem_singleton, Option.some.injEq] at h; subst h; exact HMd
    have Hrm' : RmReqs (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]) := by
      intro e he hty
      rcases List.mem_append.mp he with h | h
      · exact Hrm e h hty
      · simp only [List.mem_singleton] at h; subst h; exact absurd rfl hty
    by_cases Hm : d ∈ logHist ops
    · -- a later occurrence: the history does not move
      have Hocc : logHist (ops ++ [⟨t, W32 0, d⟩]) = logHist ops := by
        rw [Hhist, histStep_mem _ _ Hm]
      imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
      · inext
        iexists ops ++ [⟨t, W32 0, d⟩], S, Mi, O, U
        rw [Hocc]
        iframe Hsl
        unfold kvCore
        rw [Hocc]
        iframe Hops Hv HU HS HMi HO
        ipureintro; exact ⟨Hok, Hodm', Hrm'⟩
      imodintro
      itrivial
    · -- the first occurrence: the client's update runs, from the slot
      have Hocc : logHist (ops ++ [⟨t, W32 0, d⟩]) = logHist ops ++ [d] := by
        rw [Hhist, histStep_nmem _ _ Hm]
      ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
      icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
        iprop(▷ opSlot (GF := GF) γr d γp (logHist ops))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
      iunfold opSlot at Hsd
      icases Hsd with ⟨%Φ, #Hsp, Hst⟩
      icases Hst with (⟨>%Hn, >Hlc, Hau⟩ | ⟨%H0, >%Hp, -⟩)
      · imod lc_fupd_elim_later $$ Hlc Hau with Hau
        iunfold opAu at Hau
        ihave Hacc := aupd_aacc $$ Hau
        unfold atomic_acc kvMask
        imod Hacc with Hacc
        isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
        icases Hacc with ⟨%x, Hx, Hucl⟩
        ihave %Hxeq := rkvVal_agree γr (logHist ops) x $$ Hv Hx
        subst Hxeq
        have Hf : kvFold (logHist ops ++ [d]) = kvApply (kvFold (logHist ops)) d :=
          kvFold_snoc _ _
        imod rkvVal_update γr (logHist ops) (kvFold (logHist ops)) (logHist ops ++ [d])
          $$ Hv Hx with ⟨Hv, Hx⟩
        icases Hucl with ⟨-, Hcommit⟩
        isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
        rw [Hf]
        imod Hcommit $$ [Hx] with HΦ
        · rw [← Hf]; iexact Hx
        imod Hclose $$ [Hops Hv HU HS HMi HO Hsl HΦ] with -
        · inext
          iexists ops ++ [⟨t, W32 0, d⟩], S, Mi, O, U
          rw [Hocc]
          isplitl [Hops Hv HU HS HMi HO]
          · unfold kvCore
            rw [Hocc]
            iframe Hops Hv HU HS HMi HO
            ipureintro; exact ⟨Hok, Hodm', Hrm'⟩
          iapply (BigSepM.bigSepM_delete (Φ := fun d' γp' =>
            opSlot (GF := GF) γr d' γp' (logHist ops ++ [d])) HOd).2
          isplitl [HΦ]
          · unfold opSlot
            iexists Φ
            iframe Hsp
            iright
            iexists logHist ops
            isplitr
            · ipureintro; exact ⟨List.prefix_refl _, Hm⟩
            ileft
            rw [Hf]
            iexact HΦ
          iapply BigSepM.bigSepM_impl $$ Hsl
          imodintro
          iintro %k %v %Hkv Hs
          have Hne' : k ≠ d := (Iris.Std.LawfulPartialMap.get?_delete_some_iff.mp Hkv).1.symm
          iapply opSlot_grow γr k d v (logHist ops) Hne' $$ Hs
        imodintro
        itrivial
      · exact absurd (Hp.1.subset (List.mem_append_right _ (List.mem_singleton_self d))) Hm

/-- **The update `Node.ProposeConfChange` takes** for a conf change (`RemoveMember`'s): its entry
carries no datum, so the history does not move. -/
theorem kv_ccAu (γr : RKVNames) (id : w64) (Hsh : RmShrink id) :
    ⊢ rkvInv (GF := GF) γr -∗
      AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvRaftN, ∅
        <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some (.v1 (rmCC id))) bs⌝ ∗
             ownCommittedOps γr.cluster
               (ops ++ [(⟨t, confChangeEntryType (some (.v1 (rmCC id))), bs⟩ : LogEntry)]),
           COMM True }> := by
  iintro #Hinv
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_raftN
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kvRaftN) \ ↑rkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
    · inext
      iexists ops, S, Mi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hv HU HS HMi HO
      ipureintro; exact ⟨Hok, Hodm, Hrm⟩
    imodintro
    iempintro
  · iintro %t %bs ⟨%Hbs, Hops⟩
    imod Hclose2 with -
    have Hod : odOf (⟨t, confChangeEntryType (some (.v1 (rmCC id))), bs⟩ : LogEntry) = none := by
      unfold odOf; rw [if_neg]
      rintro ⟨h, -⟩
      exact absurd h (by simp only [confChangeEntryType]; intro h1; revert h1; word)
    have Hocc : logHist (ops ++ [⟨t, confChangeEntryType (some (.v1 (rmCC id))), bs⟩]) = logHist ops := by
      unfold logHist; rw [List.map_append, List.map_singleton, Hod, histOf_snoc]; rfl
    imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
    · inext
      iexists ops ++ [⟨t, confChangeEntryType (some (.v1 (rmCC id))), bs⟩], S, Mi, O, U
      rw [Hocc]
      iframe Hsl
      unfold kvCore
      rw [Hocc]
      iframe Hops Hv HU HS HMi HO
      ipureintro
      refine ⟨Hok, fun d' h => ?_, ?_⟩
      · rw [List.map_append, List.map_singleton, Hod] at h
        rcases List.mem_append.mp h with h | h
        · exact Hodm d' h
        · simp at h
      · intro e he hty
        rcases List.mem_append.mp he with h | h
        · exact Hrm e h hty
        · simp only [List.mem_singleton] at h; subst h
          exact ⟨rfl, id, Hbs, Hsh⟩
    imodintro
    itrivial

/-- Collecting an operation's result: given a committed log `l`, whose entries' data are `ods`, in
which `d` first occurs at position `m`, the ticket buys the result of the client's update at `d`'s
key's value after the history before it and `d`, under two laters (the invariant it was stored
in; the saved predicate naming it). -/
theorem kv_collect (γr : RKVNames) (d : List w8) (γp : GName × GName) (Ψ : List w8 → IProp GF)
    (l : List LogEntry) (ods : List (Option (List w8))) (m : Nat) (E : CoPset)
    (HE1 : ↑rkvN ⊆ E) :
    ods = l.map odOf → ods[m]? = some (some d) → d ∉ histOf (ods.take m) →
    ⊢ rkvInv (GF := GF) γr -∗ d ↪[γr.ops]□ γp -∗
      savedPredOwn γp.1 DFrac.discard Ψ -∗ token γp.2 -∗ isCommittedLogLb γr.cluster l ={E}=∗
      ▷ ▷ Ψ (kvFold (histOf (ods.take m) ++ [d]) (dkey d)) := by
  intro Hods Hm Hfirst
  iintro #Hinv #Hop #Hsp Htok #Hl
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γr.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  icases ghost_map_lookup $$ HO Hop with %HOd
  -- `d` is in the history, right after `histOf (ods.take m)`
  have Htk : ods.take (m + 1) = ods.take m ++ [some d] := by
    rw [List.take_add_one, Hm]; rfl
  have h1 : histOf (ods.take (m + 1)) = histOf (ods.take m) ++ [d] := by
    rw [Htk, histOf_snoc, histStep_nmem _ _ Hfirst]
  have Hocc : histOf (ods.take m) ++ [d] <+: logHist ops := by
    rw [← h1]
    refine (histOf_prefix_of_prefix _ _ (List.take_prefix _ _)).trans ?_
    rw [Hods]; exact logHist_le_ops l ops Hpre
  have HdL : d ∈ logHist ops :=
    Hocc.subset (List.mem_append_right _ (List.mem_singleton_self d))
  ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
  icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
    iprop(▷ opSlot (GF := GF) γr d γp (logHist ops))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
  iunfold opSlot at Hsd
  icases Hsd with ⟨%Φ', #Hsp', Hst⟩
  icases Hst with (⟨>%Hn, -, -⟩ | ⟨%H0, >%HH0, HQ⟩)
  · exact absurd HdL Hn
  have HH0eq : H0 = histOf (ods.take m) :=
    hist_prefix_before_unique _ _ _ d (histOf_nodup _) HH0.1 Hocc
  subst HH0eq
  icases HQ with (HQ | >Htok')
  · ihave #Heq : ▷ ▷ (Φ' (kvFold (histOf (ods.take m) ++ [d]) (dkey d)) ≡
        Ψ (kvFold (histOf (ods.take m) ++ [d]) (dkey d))) $$ []
    · inext
      iapply saved_pred_agree γp.1 DFrac.discard DFrac.discard Φ' Ψ _ $$ Hsp' Hsp
    imod Hclose $$ [Hops Hv HU HS HMi HO Hsl Htok] with -
    · inext
      iexists ops, S, Mi, O, U
      isplitl [Hops Hv HU HS HMi HO]
      · unfold kvCore
        iframe Hops Hv HU HS HMi HO
        ipureintro; exact ⟨Hok, Hodm, Hrm⟩
      iapply (BigSepM.bigSepM_delete (Φ := fun d γp =>
        opSlot (GF := GF) γr d γp (logHist ops)) HOd).2
      iframe Hsl
      unfold opSlot
      iexists Φ'
      iframe Hsp'
      iright
      iexists histOf (ods.take m)
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

/-- **A committed conf-change entry is a `RemoveMember`'s** (2026-10-27): an entry of type `1` (a
`ConfChange`, never a filler) of a committed log is among the committed requested entries
(`ownCommittedOps_lb_prefix`), whose conf changes are `RemoveMember`'s (`RmReqs`): its bytes
decode to `rmCC id` for some `id`. What `run` applies with `node.ApplyConfChange`. -/
theorem kv_committed_cc (γr : RKVNames) (l : List LogEntry) (e : LogEntry) (E : CoPset)
    (HE : ↑rkvN ⊆ E) :
    e ∈ l → e.type = W32 1 →
    ⊢ rkvInv (GF := GF) γr -∗ isCommittedLogLb γr.cluster l ={E}=∗
      ⌜∃ id, ccDecodeV1 e.data = some (rmCC id) ∧ RmShrink id⌝ := by
  intro Hel Hty
  iintro #Hinv #Hl
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%ops, %S, %Mi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, HS, HMi, HO, %Hok, %Hodm, %Hrm⟩
  ihave %Hpre := ownCommittedOps_lb_prefix γr.cluster ops l $$ [Hops Hl]
  · iframe Hops Hl
  have Hnf : ¬ e.isFiller := by
    rintro ⟨-, h⟩; rw [Hty] at h; revert h; word
  have Hin : e ∈ ops := Hpre.subset (List.mem_filter.mpr ⟨Hel, by simp [Hnf]⟩)
  have Hne : e.type ≠ W32 0 := by rw [Hty]; intro h; revert h; word
  obtain ⟨-, id, Hm, Hsh⟩ := Hrm e Hin Hne
  imod Hclose $$ [Hops Hv HU HS HMi HO Hsl] with -
  · inext
    iexists ops, S, Mi, O, U
    iframe Hsl
    unfold kvCore
    iframe Hops Hv HU HS HMi HO
    ipureintro; exact ⟨Hok, Hodm, Hrm⟩
  imodintro
  ipureintro
  exact ⟨id, Hm, Hsh⟩

end lemmas

/-! ## Raft's read states, at the store

The store's own view of a `Ready`'s read states (`rsOk`). -/

section pb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `ReadState` values of a `Ready`'s read states (`readStatesPts`'s big separating
conjunction), each `rsOk`. -/
theorem rsOk_of_readStates (γ : Cluster) :
    ∀ (vs : List ReadState) (sts : List ReadStateM),
    ([∗list] v;st ∈ vs;sts, ⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx') ∗
      ([∗list] st ∈ sts, readStateOk (GF := GF) γ kvRaftN st.RequestCtx' st.Index') ⊢
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
    · ihave H := rsOk_of_readStates γ vs sts $$ [Hb' Hok']
      · iframe Hb' Hok'
      iexact H

/-- The `ReadState` values a `Ready` hands out (`readStatesPts`, persistent), each `rsOk`: what
`run` appends to its pending read states and `answer` takes. -/
theorem readStatesPts_rsOk (γ : Cluster) (rs : GoSlice) (sts : List ReadStateM) :
    readStatesPts (GF := GF) rs sts ∗
      ([∗list] st ∈ sts, readStateOk γ kvRaftN st.RequestCtx' st.Index') ⊢
      ∃ vs : List ReadState, rs ↦*□ vs ∗ [∗list] v ∈ vs, rsOk γ v := by
  iintro ⟨H, #Hok⟩
  iunfold readStatesPts at H
  icases H with ⟨%vs, #Hs, #Hb⟩
  iexists vs
  iframe Hs
  ihave H := rsOk_of_readStates γ vs sts $$ [Hb Hok]
  · iframe Hb Hok
  iexact H

end pb

end EtcdGrove
end Perennial
