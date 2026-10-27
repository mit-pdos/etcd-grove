/-
Lean-first (no Rocq counterpart).

# The key-value store's ghost lemmas (2026-10-10; 2026-10-14, stage R: raft's persistent updates)

- `kvStor_register`: a new storage joins the registry (`kvStorInv`, `Defs.lean`).
- `kv_mint`: a new sequence number mints the operation's fresh token (`MintOk`) and the
  operation's slot, holding the client's atomic update (`opSlot`).
- `kv_deposited_minted`: a deposited datum (raft's registry) was minted, so a datum with
  a minted key is the one minted there.
- `kv_mint_read` (2026-10-13): a new sequence number mints a read's context and its fresh
  token for raft's read registry; `kv_read_minted`: a deposited context with a minted key is
  the one minted there.
- `kvLb_current`: the history now is a lower bound (`kvLb`), at the client's state.
- `kv_propAu`: the persistent atomic update over raft's full log that `Node.Propose` deposits
  for an operation's datum: at every committed occurrence it moves the store's log, and at
  the first it runs the client's update from the operation's slot (the linearization point);
  `kv_noopAu`, the standing update for raft's own entries; `kv_readAu`, a read's update.
- `kv_collect`: the client's result, from its slot, with its ticket.
- `rkvVal_agree`, `rkvVal_update`: the client's half of the history's ghost variable against the
  invariant's (2026-10-19).
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The applier's table, pure -/

theorem occStep_mem (L : List (List w8)) (d : List w8) (h : d ∈ L) : occStep L (some d) = L := by
  show (if d ∈ L then _ else _) = _; rw [ite_eq_left h]

theorem occStep_nmem (L : List (List w8)) (d : List w8) (h : d ∉ L) :
    occStep L (some d) = L ++ [d] := by
  show (if d ∈ L then _ else _) = _; rw [ite_eq_right h]

theorem appliedOk_skip (A : GMap (List w8) Bool) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hd : decodeOp d = none ∨ d ∈ L) : AppliedOk A (occStep L (some d)) := by
  by_cases Hm : d ∈ L
  · rw [occStep_mem L d Hm]; exact HA
  · have Hd' : decodeOp d = none := by rcases Hd with h | h; exact h; exact absurd h Hm
    rw [occStep_nmem L d Hm]
    intro d'
    rw [HA d']
    by_cases Heq : d' = d
    · subst Heq; simp [Hd', Hm]
    · simp [List.mem_append, Heq]

theorem appliedOk_insert (A : GMap (List w8) Bool) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hm : d ∉ L) (Hd : (decodeOp d).isSome) :
    AppliedOk (A.insert d true) (L ++ [d]) := by
  intro d'
  by_cases Heq : d' = d
  · subst Heq; rw [GMap.lookup_insert_eq]; simp [Hd]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq), HA d']
    simp [List.mem_append, Heq]

theorem appliedOk_lookup (A : GMap (List w8) Bool) (L : List (List w8)) (d : List w8)
    (HA : AppliedOk A L) (Hd : (decodeOp d).isSome) : (A !! d).getD false = decide (d ∈ L) := by
  rw [HA d]
  by_cases Hm : d ∈ L <;> simp [Hm, Hd]

theorem firstOcc_prefix_of_prefix (a b : List (Option (List w8))) (h : a <+: b) :
    firstOcc a <+: firstOcc b := by
  obtain ⟨t, rfl⟩ := h
  exact firstOcc_append_prefix a t

/-! ## Minting, pure -/

/-- A new sequence number's key is fresh: no datum, token, read token or slot has it. -/
theorem mintOk_fresh [GooseExts] (M F : GMap (List w8) Unit) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (id ns : w64)
    (d : List w8) (Hok : MintOk M F S Mi O) (HS : S !! id = some ns)
    (Hkey : opKey d = some (id, ns + W64 1)) (Hns : uint.Z ns + 1 < 2 ^ 64) :
    Mi !! (id, ns + W64 1) = none ∧ M !! d = none ∧ F !! d = none ∧ O !! d = none := by
  have Hsucc : uint.Z (ns + W64 1) = uint.Z ns + 1 := by word
  have HMi0 : Mi !! (id, ns + W64 1) = none := by
    cases h : Mi !! (id, ns + W64 1) with
    | none => rfl
    | some d' =>
      obtain ⟨n, Hn, Hle⟩ := Hok.2.1 _ _ _ h
      rw [HS] at Hn; cases Hn
      omega
  have HM0 : M !! d = none := by
    cases h : M !! d with
    | none => rfl
    | some u =>
      cases u
      obtain ⟨k, Hk, Hk'⟩ := Hok.1 d h
      rw [Hkey] at Hk; cases Hk
      rw [HMi0] at Hk'; cases Hk'
  refine ⟨HMi0, HM0, ?_, ?_⟩
  · cases h : F !! d with
    | none => rfl
    | some u =>
      cases u
      obtain ⟨k, Hk, Hk'⟩ := Hok.2.2.1 d h
      rw [Hkey] at Hk; cases Hk
      rw [HMi0] at Hk'; cases Hk'
  · cases h : O !! d with
    | none => rfl
    | some γp =>
      have := Hok.2.2.2 d γp h
      rw [HM0] at this; cases this

/-- Minting `d` at a new sequence number, with new tokens only of `d` and slots of minted data. -/
theorem mintOk_step [GooseExts] (M M' F F' : GMap (List w8) Unit) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O O' : GMap (List w8) (GName × GName)) (id ns : w64)
    (d : List w8)
    (Hok : MintOk M F S Mi O) (HS : S !! id = some ns) (Hkey : opKey d = some (id, ns + W64 1))
    (Hns : uint.Z ns + 1 < 2 ^ 64)
    (HM' : ∀ d', M' !! d' = some () → M !! d' = some () ∨ d' = d)
    (HF' : ∀ c, F' !! c = some () → F !! c = some () ∨ c = d)
    (HO' : ∀ d' γp, O' !! d' = some γp → M' !! d' = some ()) :
    MintOk M' F' (S.insert id (ns + W64 1)) (Mi.insert (id, ns + W64 1) d) O' := by
  obtain ⟨HMi0, -, -, -⟩ := mintOk_fresh M F S Mi O id ns d Hok HS Hkey Hns
  have Hsucc : uint.Z (ns + W64 1) = uint.Z ns + 1 := by word
  -- an old minted key is not the new one
  have Hold : ∀ x k, opKey x = some k → Mi !! k = some x →
      (Mi.insert (id, ns + W64 1) d) !! k = some x := by
    intro x k _ Hk'
    have Hne : (id, ns + W64 1) ≠ k := by
      intro h; subst h; rw [HMi0] at Hk'; cases Hk'
    rw [GMap.lookup_insert_ne _ _ Hne]; exact Hk'
  refine ⟨?_, ?_, ?_, HO'⟩
  · intro d' Hd'
    rcases HM' d' Hd' with h | rfl
    · obtain ⟨k, Hk, Hk'⟩ := Hok.1 d' h
      exact ⟨k, Hk, Hold d' k Hk Hk'⟩
    · exact ⟨_, Hkey, GMap.lookup_insert_eq _ _ _⟩
  · intro i s d' Hs
    by_cases Hk : (i, s) = (id, ns + W64 1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hk
      exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, Int.le_refl _⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hk)] at Hs
      obtain ⟨n, Hn, Hle⟩ := Hok.2.1 _ _ _ Hs
      by_cases Hi : i = id
      · subst Hi
        rw [HS] at Hn; cases Hn
        exact ⟨ns + W64 1, GMap.lookup_insert_eq _ _ _, by omega⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hi)]
        exact ⟨n, Hn, Hle⟩
  · intro c Hc
    rcases HF' c Hc with h | rfl
    · obtain ⟨k, Hk, Hk'⟩ := Hok.2.2.1 c h
      exact ⟨k, Hk, Hold c k Hk Hk'⟩
    · exact ⟨_, Hkey, GMap.lookup_insert_eq _ _ _⟩

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
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

/-- A new sequence number mints the operation's fresh token and records it; the operation's
slot, with the client's atomic update and a later credit (2026-10-14, stage R). -/
theorem kv_mint (γr : RKVNames) (id ns : w64) (kind : w8) (key val : List w8)
    (Ψ : List w8 → IProp GF) (E : CoPset) (HE : ↑rkvN ⊆ E) (Hns : uint.Z ns + 1 < 2 ^ 64)
    (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γr -∗ id ↪[γr.seq] ns -∗ £ 1 -∗ opAu γr (kvNext kind key val) key Ψ ={E}=∗
      id ↪[γr.seq] (ns + W64 1) ∗
      (id, ns + W64 1) ↪[γr.mint]□ encodeOp id (ns + W64 1) kind key val ∗
      propFresh γr.raft (encodeOp id (ns + W64 1) kind key val) ∗
      ∃ γp : GName × GName, encodeOp id (ns + W64 1) kind key val ↪[γr.ops]□ γp ∗
        savedPredOwn γp.1 DFrac.discard Ψ ∗ token γp.2 := by
  iintro #Hinv Hseq Hlc Hau
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  icases ghost_map_lookup $$ HS Hseq with %HSi
  have Hf : (fun x => kvApply x (encodeOp id (ns + W64 1) kind key val)) = kvNext kind key val :=
    funext fun x => kvApply_encodeOp x id (ns + W64 1) kind key val Hk
  have Hdk : dkey (encodeOp id (ns + W64 1) kind key val) = key := dkey_encodeOp _ _ _ _ _ Hk
  generalize Hd : encodeOp id (ns + W64 1) kind key val = d at Hf Hdk ⊢
  have Hkey : opKey d = some (id, ns + W64 1) := by rw [← Hd]; exact opKey_encodeOp _ _ _ _ _ Hk
  obtain ⟨HMi0, HM0, -, HO0⟩ := mintOk_fresh M F S Mi O id ns d Hok HSi Hkey Hns
  have Hdn : d ∉ firstOcc ods := fun h => by
    have := Hodm d ((mem_firstOcc ods d).mp h)
    rw [HM0] at this; cases this
  imod ghost_map_update (ns + W64 1) $$ HS Hseq with ⟨HS, Hseq⟩
  imod ghost_map_insert_persist (id, ns + W64 1) d HMi0 $$ HMi with ⟨HMi, #Hmint⟩
  imod ghost_map_insert d () HM0 $$ HM with ⟨HM, Hfresh⟩
  imod saved_pred_alloc Ψ DFrac.discard trivial with ⟨%γq, #Hsp⟩
  imod token_alloc (GF := GF) with ⟨%γk, Htok⟩
  imod ghost_map_insert_persist d ((γq, γk) : GName × GName) HO0 $$ HO with ⟨HO, #Hop⟩
  imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl Hlc Hau] with -
  · inext
    iexists L, ods, M.insert d (), F, S.insert id (ns + W64 1), Mi.insert (id, ns + W64 1) d,
      O.insert d (γq, γk)
    isplitl [HrL Hv HM HF HS HMi HO]
    · unfold kvCore
      iframe HrL Hods Hv HM HF HS HMi HO
      ipureintro
      refine ⟨mintOk_step M _ F F S Mi O _ id ns d Hok HSi Hkey Hns ?_ (fun c h => .inl h) ?_, ?_⟩
      · intro d' Hd'
        by_cases Heq : d' = d
        · exact .inr Heq
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hd'; exact .inl Hd'
      · intro d' γp' Hd'
        by_cases Heq : d' = d
        · subst Heq; exact GMap.lookup_insert_eq _ _ _
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hd' ⊢
          exact Hok.2.2.2 d' γp' Hd'
      · intro d' Hd'
        by_cases Heq : d' = d
        · subst Heq; exact GMap.lookup_insert_eq _ _ _
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)]; exact Hodm d' Hd'
    iapply (BigSepM.bigSepM_insert (Φ := fun d γp => opSlot (GF := GF) γr d γp (firstOcc ods))
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
  isplitl [Hfresh]
  · unfold propFresh; iexact Hfresh
  iexists (γq, γk)
  iframe Hop Hsp Htok

/-- A new sequence number mints a read's context (2026-10-13) and (2026-10-14, stage R) its
fresh token for raft's read registry (`rdFresh`), and records it. -/
theorem kv_mint_read (γr : RKVNames) (id ns : w64) (key : List w8) (E : CoPset)
    (HE : ↑rkvN ⊆ E) (Hns : uint.Z ns + 1 < 2 ^ 64) (Hk : (key.length : Int) < 2 ^ 64) :
    ⊢ rkvInv (GF := GF) γr -∗ id ↪[γr.seq] ns ={E}=∗
      id ↪[γr.seq] (ns + W64 1) ∗
      (id, ns + W64 1) ↪[γr.mint]□ encodeOp id (ns + W64 1) opReadB key [] ∗
      rdFresh γr.raft (encodeOp id (ns + W64 1) opReadB key []) := by
  iintro #Hinv Hseq
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  icases ghost_map_lookup $$ HS Hseq with %HSi
  generalize Hd : encodeOp id (ns + W64 1) opReadB key [] = d
  have Hkey : opKey d = some (id, ns + W64 1) := by rw [← Hd]; exact opKey_encodeOp _ _ _ _ _ Hk
  obtain ⟨HMi0, -, HF0, -⟩ := mintOk_fresh M F S Mi O id ns d Hok HSi Hkey Hns
  imod ghost_map_update (ns + W64 1) $$ HS Hseq with ⟨HS, Hseq⟩
  imod ghost_map_insert_persist (id, ns + W64 1) d HMi0 $$ HMi with ⟨HMi, #Hmint⟩
  imod ghost_map_insert d () HF0 $$ HF with ⟨HF, Hfresh⟩
  imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
  · inext
    iexists L, ods, M, F.insert d (), S.insert id (ns + W64 1), Mi.insert (id, ns + W64 1) d, O
    iframe Hsl
    unfold kvCore
    iframe HrL Hods Hv HM HF HS HMi HO
    ipureintro
    refine ⟨mintOk_step M M F _ S Mi O O id ns d Hok HSi Hkey Hns (fun d' h => .inl h) ?_
      Hok.2.2.2, Hodm⟩
    intro c Hc
    by_cases Heq : c = d
    · exact .inr Heq
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm Heq)] at Hc; exact .inl Hc
  imodintro
  iframe Hseq Hmint
  unfold rdFresh
  iexact Hfresh

/-- A deposited read context with a minted key is the one minted there (2026-10-13; since
2026-10-14, stage R, through its fresh token, which raft's read registry keeps). -/
theorem kv_read_minted (γr : RKVNames) (c c0 : List w8) (Lc : List EntryM)
    (k : w64 × w64) (E : CoPset) (HE1 : ↑rkvN ⊆ E) (HE2 : ↑raftN ⊆ E \ ↑rkvN)
    (Hk : opKey c = some k) :
    ⊢ rkvInv (GF := GF) γr -∗ raftCommitInv γr.raft -∗ readReq γr.raft c Lc -∗
      k ↪[γr.mint]□ c0 ={E}=∗ ⌜c0 = c⌝ := by
  iintro #Hinv #Hcinv #Hrq #Hmint
  unfold readReq
  icases Hrq with ⟨%γq, #Hel, -⟩
  ihave #Hri := raftCommitInv_reg γr.raft $$ Hcinv
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  have HE3 : (↑raftRegN : CoPset) ⊆ E \ ↑rkvN := raftRegN_of HE2
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, Hq, Hregs⟩ Hclose2
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold readsReg at Hreads
  icases Hreads with ⟨>Hra, Hs⟩
  icases ghost_map_lookup $$ Hra Hel with %HRc
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun c r =>
    iprop(▷ (readSlot (GF := GF) γr.raft r l ∗ rdFresh γr.raft c))) HRc).1 $$ Hs
    with ⟨⟨Hsl', >Hf⟩, Hsback⟩
  iunfold rdFresh at Hf
  icases ghost_map_lookup $$ HF Hf with %HFc
  ihave Hs := Hsback $$ [Hsl' Hf]
  · inext; iframe Hsl'; unfold rdFresh; iexact Hf
  imod Hclose2 $$ [Hq Hprops Hra Hs] with -
  · inext
    iexists l
    iframe Hq
    unfold regsAt readsReg
    iexists R, RR
    iframe Hprops Hnoop Hra
    iexact Hs
  obtain ⟨k', Hk', HMik⟩ := Hok.2.2.1 c HFc
  rw [Hk] at Hk'; cases Hk'
  icases ghost_map_lookup $$ HMi Hmint with %HMi0
  rw [HMik] at HMi0
  cases HMi0
  imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
  · inext
    iexists L, ods, M, F, S, Mi, O
    iframe Hsl
    unfold kvCore
    iframe HrL Hods Hv HM HF HS HMi HO
    ipureintro; exact ⟨Hok, Hodm⟩
  imodintro
  ipureintro; rfl

/-- Every committed log is a prefix of the store's log (the global one). -/
theorem kv_log_prefix (γr : RKVNames) (L l : List EntryM) (E : CoPset)
    (HE : ↑raftLogN ⊆ E) :
    ⊢ raftCommitInv (GF := GF) γr.raft -∗ rLog γr.raft L -∗ isCommitted γr.raft l ={E}=∗
      rLog γr.raft L ∗ ⌜l <+: L⌝ := by
  iintro #Hcinv HrL #Hl
  ihave #Hli := raftCommitInv_log γr.raft $$ Hcinv
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose
  iunfold rLog at HrL
  ihave %HLeq := ghostVar_agree γr.raft.reRLog P rlq L (1 : Qp).half $$ Hq1 HrL
  subst HLeq
  ihave %Hpre := isCommitted_prefix γr.raft l P $$ Hl HP
  imod Hclose $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hj Htbl Hwt Hds Hq1
  imodintro
  unfold rLog
  iframe HrL
  ipureintro; exact Hpre

/-- The history now is a lower bound, at the client's state (2026-10-13). -/
theorem kvLb_current (γr : RKVNames) (x : KVMap) (E : CoPset)
    (HE1 : ↑rkvN ⊆ E) (HE2 : ↑raftN ⊆ E \ ↑rkvN) :
    ⊢ rkvInv (GF := GF) γr -∗ raftCommitInv γr.raft -∗ rkvVal γr x ={E}=∗
      rkvVal γr x ∗ ∃ L, kvLb γr L ∗ ⌜kvFold L = x⌝ := by
  iintro #Hinv #Hcinv Hx
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  ihave %Hxeq := rkvVal_agree γr (firstOcc ods) x $$ Hv Hx
  have HE3 : (↑raftLogN : CoPset) ⊆ E \ ↑rkvN := raftLogN_of HE2
  imod rLog_committed γr.raft L _ HE3 $$ Hcinv HrL with ⟨HrL, #HLc⟩
  imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
  · inext
    iexists L, ods, M, F, S, Mi, O
    iframe Hsl
    unfold kvCore
    iframe HrL Hods Hv HM HF HS HMi HO
    ipureintro; exact ⟨Hok, Hodm⟩
  imodintro
  iframe Hx
  iexists firstOcc ods
  isplitl
  · unfold kvLb
    iexists L, ods
    iframe HLc Hods
    ipureintro; rfl
  ipureintro; exact Hxeq

/-- A deposited datum was minted (its fresh token is raft's registry's, and every token
was minted), so it is the one minted at its key. -/
theorem kv_deposited_minted (γr : RKVNames) (d d0 : List w8) (k : w64 × w64) (E : CoPset)
    (HE1 : ↑rkvN ⊆ E) (HE2 : ↑raftN ⊆ E \ ↑rkvN) (Hk : opKey d = some k) :
    ⊢ rkvInv (GF := GF) γr -∗ raftCommitInv γr.raft -∗ deposited γr.raft d -∗
      k ↪[γr.mint]□ d0 ={E}=∗ ⌜d0 = d⌝ := by
  iintro #Hinv #Hcinv #Hdep #Hmint
  ihave #Hri := raftCommitInv_reg γr.raft $$ Hcinv
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  -- the datum's fresh token is in raft's registry: `d ∈ M`
  have HE3 : (↑raftRegN : CoPset) ⊆ E \ ↑rkvN := raftRegN_of HE2
  unfold raftRegInv regsOwn
  iinv Hri with ⟨%l, Hq, Hregs⟩ Hclose2
  iunfold regsAt at Hregs
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  iunfold propsOwn at Hprops
  icases Hprops with ⟨>Hra, Hs⟩
  unfold deposited
  icases Hdep with ⟨%γq, #Hfr⟩
  icases ghost_map_lookup $$ Hra Hfr with %HR
  ihave Hs := (BigSepM.bigSepM_later).1 $$ Hs
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun d (p : PropRec) =>
    iprop(▷ (propSlot (GF := GF) γr.raft d p l ∗ propFresh γr.raft d))) HR).1 $$ Hs
    with ⟨⟨Hsl', >Hf⟩, Hsback⟩
  iunfold propFresh at Hf
  icases ghost_map_lookup $$ HM Hf with %HMd
  ihave Hs := Hsback $$ [Hsl' Hf]
  · inext; iframe Hsl'; unfold propFresh; iexact Hf
  imod Hclose2 $$ [Hq Hreads Hra Hs] with -
  · inext
    iexists l
    iframe Hq
    unfold regsAt propsOwn
    iexists R, RR
    iframe Hreads Hnoop Hra
    iexact Hs
  obtain ⟨k', Hk', HMik⟩ := Hok.1 d HMd
  rw [Hk] at Hk'; cases Hk'
  icases ghost_map_lookup $$ HMi Hmint with %HMi0
  rw [HMik] at HMi0
  cases HMi0
  imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
  · inext
    iexists L, ods, M, F, S, Mi, O
    iframe Hsl
    unfold kvCore
    iframe HrL Hods Hv HM HF HS HMi HO
    ipureintro; exact ⟨Hok, Hodm⟩
  imodintro
  ipureintro; rfl

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

/-- The persistent atomic update over raft's full log that `Node.Propose` deposits for the
operation's datum `d`, whose slot is `γp` (2026-10-14, stage R; see the file header). At every
committed occurrence it moves the store's log; at the first (`d` not yet in the history) it
runs the client's update from the slot, with the slot's later credit, and moves the value. -/
theorem kv_propAu (γr : RKVNames) (d : List w8) (γp : GName × GName) :
    ⊢ rkvInv (GF := GF) γr -∗ d ↪[γr.ops]□ γp -∗ propAu γr.raft d (fun _ => iprop(True)) := by
  iintro #Hinv #Hop
  unfold propAu
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_raftN
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  icases ghost_map_lookup $$ HO Hop with %HOd
  have HMd : M !! d = some () := Hok.2.2.2 d γp HOd
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑raftN) \ ↑rkvN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists L
  iframe HrL
  isplit
  · -- abort: nothing moved
    iintro HrL
    imod Hclose2 with -
    imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
    · inext
      iexists L, ods, M, F, S, Mi, O
      iframe Hsl
      unfold kvCore
      iframe HrL Hods Hv HM HF HS HMi HO
      ipureintro; exact ⟨Hok, Hodm⟩
    imodintro
    iempintro
  · -- commit: the log grows by `e`, holding `d`
    iintro %e ⟨HrL, #He, -⟩
    imod Hclose2 with -
    ihave #Hods' : iprop([∗list] e;o ∈ L ++ [e];ods ++ [some d], entDataIs γr.raft e o) $$ []
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ e o => entDataIs (GF := GF) γr.raft e o)).2
      iframe Hods He
    have Hodm' : ∀ d', some d' ∈ ods ++ [some d] → M !! d' = some () := by
      intro d' h
      rcases List.mem_append.mp h with h | h
      · exact Hodm d' h
      · simp only [List.mem_singleton, Option.some.injEq] at h; subst h; exact HMd
    by_cases Hm : d ∈ firstOcc ods
    · -- a later occurrence: the history does not move
      have Hocc : firstOcc (ods ++ [some d]) = firstOcc ods := by
        rw [firstOcc_snoc, occStep_mem _ _ Hm]
      imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
      · inext
        iexists L ++ [e], ods ++ [some d], M, F, S, Mi, O
        rw [Hocc]
        iframe Hsl
        unfold kvCore
        rw [Hocc]
        iframe HrL Hods' Hv HM HF HS HMi HO
        ipureintro; exact ⟨Hok, Hodm'⟩
      imodintro
      itrivial
    · -- the first occurrence: the client's update runs, from the slot
      have Hocc : firstOcc (ods ++ [some d]) = firstOcc ods ++ [d] := by
        rw [firstOcc_snoc, occStep_nmem _ _ Hm]
      ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
      icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
        iprop(▷ opSlot (GF := GF) γr d γp (firstOcc ods))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
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
        ihave %Hxeq := rkvVal_agree γr (firstOcc ods) x $$ Hv Hx
        subst Hxeq
        have Hf : kvFold (firstOcc ods ++ [d]) = kvApply (kvFold (firstOcc ods)) d :=
          kvFold_snoc _ _
        imod rkvVal_update γr (firstOcc ods) (kvFold (firstOcc ods)) (firstOcc ods ++ [d])
          $$ Hv Hx with ⟨Hv, Hx⟩
        icases Hucl with ⟨-, Hcommit⟩
        isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
        rw [Hf]
        imod Hcommit $$ [Hx] with HΦ
        · rw [← Hf]; iexact Hx
        imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl HΦ] with -
        · inext
          iexists L ++ [e], ods ++ [some d], M, F, S, Mi, O
          rw [Hocc]
          isplitl [HrL Hv HM HF HS HMi HO]
          · unfold kvCore
            rw [Hocc]
            iframe HrL Hods' Hv HM HF HS HMi HO
            ipureintro; exact ⟨Hok, Hodm'⟩
          iapply (BigSepM.bigSepM_delete (Φ := fun d' γp' =>
            opSlot (GF := GF) γr d' γp' (firstOcc ods ++ [d])) HOd).2
          isplitl [HΦ]
          · unfold opSlot
            iexists Φ
            iframe Hsp
            iright
            iexists firstOcc ods
            isplitr
            · ipureintro; exact ⟨List.prefix_refl _, Hm⟩
            ileft
            rw [Hf]
            iexact HΦ
          iapply BigSepM.bigSepM_impl $$ Hsl
          imodintro
          iintro %k %v %Hkv Hs
          have Hne : k ≠ d := (Iris.Std.LawfulPartialMap.get?_delete_some_iff.mp Hkv).1.symm
          iapply opSlot_grow γr k d v (firstOcc ods) Hne $$ Hs
        imodintro
        itrivial
      · exact absurd (Hp.1.subset (List.mem_append_right _ (List.mem_singleton_self d))) Hm

/-- The standing update for raft's own entries (2026-10-14, stage R): the store's log
grows, its history and value do not. -/
theorem kv_noopAu (γr : RKVNames) :
    ⊢ rkvInv (GF := GF) γr -∗ noopAu γr.raft := by
  iintro #Hinv
  unfold noopAu
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_raftN
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑raftN) \ ↑rkvN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists L
  iframe HrL
  isplit
  · iintro HrL
    imod Hclose2 with -
    imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
    · inext
      iexists L, ods, M, F, S, Mi, O
      iframe Hsl
      unfold kvCore
      iframe HrL Hods Hv HM HF HS HMi HO
      ipureintro; exact ⟨Hok, Hodm⟩
    imodintro
    iempintro
  · iintro %e ⟨HrL, #He, -⟩
    imod Hclose2 with -
    ihave #Hods' : iprop([∗list] e;o ∈ L ++ [e];ods ++ [none], entDataIs γr.raft e o) $$ []
    · iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ e o => entDataIs (GF := GF) γr.raft e o)).2
      iframe Hods He
    have Hocc : firstOcc (ods ++ [none]) = firstOcc ods := by rw [firstOcc_snoc]; rfl
    imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
    · inext
      iexists L ++ [e], ods ++ [none], M, F, S, Mi, O
      rw [Hocc]
      iframe Hsl
      unfold kvCore
      rw [Hocc]
      iframe HrL Hods' Hv HM HF HS HMi HO
      ipureintro
      refine ⟨Hok, fun d' h => ?_⟩
      rcases List.mem_append.mp h with h | h
      · exact Hodm d' h
      · simp at h
    imodintro
    itrivial

/-- A read's update (2026-10-14, stage R): the log lent and returned, nothing moved. -/
theorem kv_readAu (γr : RKVNames) :
    ⊢ rkvInv (GF := GF) γr -∗ readAu γr.raft (fun _ => iprop(True)) := by
  iintro #Hinv
  unfold readAu
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_raftN
  iinv Hinv with ⟨%L, %ods, %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods, Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑raftN) \ ↑rkvN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down]
  iexists L
  iframe HrL
  isplit
  · iintro HrL
    imod Hclose2 with -
    imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
    · inext
      iexists L, ods, M, F, S, Mi, O
      iframe Hsl
      unfold kvCore
      iframe HrL Hods Hv HM HF HS HMi HO
      ipureintro; exact ⟨Hok, Hodm⟩
    imodintro
    iempintro
  · iintro HrL
    imod Hclose2 with -
    imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl] with -
    · inext
      iexists L, ods, M, F, S, Mi, O
      iframe Hsl
      unfold kvCore
      iframe HrL Hods Hv HM HF HS HMi HO
      ipureintro; exact ⟨Hok, Hodm⟩
    imodintro
    itrivial

/-- Collecting an operation's result (2026-10-14, stage R; until then raft's `prop_collect`):
given a committed log `l` with its entries' data `ods`, in which `d` first occurs at
position `m`, the ticket buys the result of the client's update at `d`'s key's value after
the history before it and `d`, under two laters (the invariant it was stored in; the saved
predicate naming it). -/
theorem kv_collect (γr : RKVNames) (d : List w8) (γp : GName × GName) (Ψ : List w8 → IProp GF)
    (l : List EntryM) (ods : List (Option (List w8))) (m : Nat) (E : CoPset)
    (HE1 : ↑rkvN ⊆ E) (HE2 : ↑raftN ⊆ E \ ↑rkvN) :
    ods[m]? = some (some d) → d ∉ firstOcc (ods.take m) →
    ⊢ rkvInv (GF := GF) γr -∗ raftCommitInv γr.raft -∗ d ↪[γr.ops]□ γp -∗
      savedPredOwn γp.1 DFrac.discard Ψ -∗ token γp.2 -∗ isCommitted γr.raft l -∗
      ([∗list] e;o ∈ l;ods, entDataIs γr.raft e o) ={E}=∗
      ▷ ▷ Ψ (kvFold (firstOcc (ods.take m) ++ [d]) (dkey d)) := by
  intro Hm Hfirst
  iintro #Hinv #Hcinv #Hop #Hsp Htok #Hl #Hds
  unfold rkvInv rkvInvBody
  iinv Hinv with ⟨%L, %ods', %M, %F, %S, %Mi, %O, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨HrL, #Hods', Hv, HM, HF, HS, HMi, HO, %Hok, %Hodm⟩
  have HE3 : (↑raftLogN : CoPset) ⊆ E \ ↑rkvN := raftLogN_of HE2
  imod kv_log_prefix γr L l _ HE3 $$ Hcinv HrL Hl with ⟨HrL, %Hpre⟩
  icases ghost_map_lookup $$ HO Hop with %HOd
  -- `d` is in the history, right after `firstOcc (ods.take m)`
  have Hlt := (List.getElem?_eq_some_iff.mp Hm).1
  have Htk : ods.take (m + 1) = ods.take m ++ [some d] := by
    rw [List.take_add_one, Hm]; rfl
  have h1 : firstOcc (ods.take (m + 1)) = firstOcc (ods.take m) ++ [d] := by
    rw [Htk, firstOcc_snoc]
    show (if d ∈ firstOcc (ods.take m) then _ else _) = _
    rw [ite_eq_right Hfirst]
  ihave %Hocc : ⌜firstOcc (ods.take m) ++ [d] <+: firstOcc ods'⌝ $$ []
  · ihave %Hop' := entDataIs_list_prefix γr.raft l L ods ods' Hpre $$ Hds Hods'
    ipureintro
    rw [← h1]
    exact (firstOcc_prefix_of_prefix _ _ (List.take_prefix _ _)).trans
      (firstOcc_prefix_of_prefix _ _ Hop')
  have HdL : d ∈ firstOcc ods' :=
    Hocc.subset (List.mem_append_right _ (List.mem_singleton_self d))
  ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
  icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
    iprop(▷ opSlot (GF := GF) γr d γp (firstOcc ods'))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
  iunfold opSlot at Hsd
  icases Hsd with ⟨%Φ', #Hsp', Hst⟩
  icases Hst with (⟨>%Hn, -, -⟩ | ⟨%H0, >%HH0, HQ⟩)
  · exact absurd HdL Hn
  have HH0eq : H0 = firstOcc (ods.take m) :=
    prefix_before_unique _ _ _ d (firstOcc_nodup ods') HH0.1 Hocc
  subst HH0eq
  icases HQ with (HQ | >Htok')
  · ihave #Heq : ▷ ▷ (Φ' (kvFold (firstOcc (ods.take m) ++ [d]) (dkey d)) ≡
        Ψ (kvFold (firstOcc (ods.take m) ++ [d]) (dkey d))) $$ []
    · inext
      iapply saved_pred_agree γp.1 DFrac.discard DFrac.discard Φ' Ψ _ $$ Hsp' Hsp
    imod Hclose $$ [HrL Hv HM HF HS HMi HO Hsl Htok] with -
    · inext
      iexists L, ods', M, F, S, Mi, O
      isplitl [HrL Hv HM HF HS HMi HO]
      · unfold kvCore
        iframe HrL Hods' Hv HM HF HS HMi HO
        ipureintro; exact ⟨Hok, Hodm⟩
      iapply (BigSepM.bigSepM_delete (Φ := fun d γp =>
        opSlot (GF := GF) γr d γp (firstOcc ods')) HOd).2
      iframe Hsl
      unfold opSlot
      iexists Φ'
      iframe Hsp'
      iright
      iexists firstOcc (ods.take m)
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

end lemmas

/-! ## Conf-change entries, at the applier (2026-10-15, stage N) -/

section confs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The data of the last entry of a committed log. -/
theorem node_entry_data (γ : NodeNames) (id : w64) (n : Loc) (l : List EntryM)
    (e : EntryM) (E : CoPset) (HE : ↑raftN ⊆ E) :
    ⊢ isNode γ id n -∗ isCommitted γ.raft (l ++ [e]) ={E}=∗ ∃ o, entDataIs (GF := GF) γ.raft e o := by
  iintro #Hnode #Hc
  imod node_committed_data γ id n (l ++ [e]) E HE $$ Hnode Hc with ⟨%ods, #Hl⟩
  ihave ⟨%o, %-, Ho⟩ := (BigSepL2.bigSepL2_lookup_left (Φ := fun _ e o => entDataIs (GF := GF) γ.raft e o)
    (l1 := l ++ [e]) (l2 := ods) (i := l.length) (x1 := e) (by simp)) $$ Hl
  imodintro
  iexists o
  iexact Ho

/-- An entry of a type other than `EntryConfChange` is no conf-change entry, in the cluster: its
conf-change entries are all of that type (`KVCC`). -/
theorem kvCC_notConf (γn : NodeNames) (op : CCOp) (c0 c1 : CCState) (H : KVCC γn op c0 c1)
    (e : EntryM) (o : Option (List w8)) :
    ⊢ entDataIs (GF := GF) γn.raft e o -∗ ⌜e.Type' ≠ W32 1 → ¬ IsConfEnt e⌝ := by
  iintro He
  cases o with
  | some d =>
    simp only [entDataIs, propDataIs]
    icases He with ⟨⟨%Hd, -⟩, -⟩
    ipureintro
    intro _ hc
    unfold IsConfEnt at hc
    rw [Hd.2.2] at hc
    rcases hc with h | h <;> revert h <;> word
  | none =>
    simp only [entDataIs, propDataIs]
    icases He with (%Hz | %Hcc)
    · ipureintro
      intro _ hc
      unfold IsConfEnt at hc
      rw [Hz.1] at hc
      rcases hc with h | h <;> revert h <;> word
    · ipureintro
      intro hn _
      exact hn (H.2.1 _ _ Hcc.2.2).1

/-- (2026-10-20, W4) A cluster that admits no conf change (`KVCCS`) commits no conf-change entry. -/
theorem kvCCS_noConf (γn : NodeNames) (H : KVCCS γn) (e : EntryM) (o : Option (List w8)) :
    ⊢ entDataIs (GF := GF) γn.raft e o -∗ ⌜¬ IsConfEnt e⌝ := by
  iintro He
  cases o with
  | some d =>
    simp only [entDataIs, propDataIs]
    icases He with ⟨⟨%Hd, -⟩, -⟩
    ipureintro
    intro hc
    unfold IsConfEnt at hc
    rw [Hd.2.2] at hc
    rcases hc with h | h <;> revert h <;> word
  | none =>
    simp only [entDataIs, propDataIs]
    icases He with (%Hz | %Hcc)
    · ipureintro
      intro hc
      unfold IsConfEnt at hc
      rw [Hz.1] at hc
      rcases hc with h | h <;> revert h <;> word
    · exfalso; exact H.2.1 _ _ Hcc.2.2

/-- `kvCC_notConf` in either kind of cluster (2026-10-20, W4). -/
theorem kvCC_notConf' (γn : NodeNames) (op : CCOp) (c0 c1 : CCState)
    (H : KVCC γn op c0 c1 ∨ KVCCS γn) (e : EntryM) (o : Option (List w8)) :
    ⊢ entDataIs (GF := GF) γn.raft e o -∗ ⌜e.Type' ≠ W32 1 → ¬ IsConfEnt e⌝ := by
  rcases H with H | H
  · exact kvCC_notConf γn op c0 c1 H e o
  · iintro He
    ihave %Hn := kvCCS_noConf γn H e o $$ He
    ipureintro; exact fun _ => Hn

/-- A conf-change entry of the cluster carries `op` (`KVCC`): its bytes decode to a `ConfChange`
whose change is `op` (raft v3.7, stage R6b: pure, over the record's bytes, D6; until then the
entry's slice was read through the proposed slices' invariant). -/
theorem kvCC_confData (γn : NodeNames) (op : CCOp) (c0 c1 : CCState) (H : KVCC γn op c0 c1)
    (e : EntryM) (o : Option (List w8)) (Hty : e.Type' = W32 1) :
    ⊢ entDataIs (GF := GF) γn.raft e o -∗
      ⌜∃ m : CCV1M, ccDecodeV1 e.Data' = some m ∧ ccV2Of (.v1 m) = op⌝ := by
  iintro He
  cases o with
  | some d =>
    simp only [entDataIs, propDataIs]
    icases He with ⟨⟨%Hd, -⟩, -⟩
    exfalso; rw [Hd.2.2] at Hty; revert Hty; word
  | none =>
    simp only [entDataIs, propDataIs]
    icases He with (%Hz | %Hcc)
    · exfalso; rw [Hz.1] at Hty; revert Hty; word
    · obtain ⟨-, m, Hm, Hop⟩ := H.2.1 _ _ Hcc.2.2
      ipureintro; exact ⟨m, Hm, Hop⟩

end confs

/-! ## Raft's read states, at the store (raft v3.7, 2026-10-16, stage R6b)

The store's own view of a `Ready`'s read states (`rsOk`). What the store needed of
`InvPb.lean`'s message predicates moved to raft's shared files on 2026-10-16 (stage R7a):
`msgPtsC_persist_els`, `msgPtsC_store_Entries`, `msgPtsC_fields_acc`, `entsPts_elim`
(`InvPbMsg.lean`), `csPts_of_struct_ro`, `ownCCV1_persistent`, `ownCCV1_persist`
(`InvPb.lean`). -/

section pb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `ReadState` values of a `Ready`'s read states (`readStatesPts`'s big separating
conjunction), each `rsOk`. -/
theorem rsOk_of_readStates (γ : RaftNames) :
    ∀ (vs : List ReadState) (sts : List ReadStateM),
    ([∗list] v;st ∈ vs;sts, ⌜v.Index' = st.Index'⌝ ∗ v.RequestCtx' ↦*□ st.RequestCtx') ∗
      ([∗list] st ∈ sts, readStateOk (GF := GF) γ st) ⊢ [∗list] v ∈ vs, rsOk γ v
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
theorem readStatesPts_rsOk (γ : RaftNames) (rs : GoSlice) (sts : List ReadStateM) :
    readStatesPts (GF := GF) rs sts ∗ ([∗list] st ∈ sts, readStateOk γ st) ⊢
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
