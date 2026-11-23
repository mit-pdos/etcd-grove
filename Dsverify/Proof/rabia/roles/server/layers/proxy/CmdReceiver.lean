/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/CmdReceiver.lean`, run `rabia-r1wake-1`.)

`(*Proxy).CmdReceiver` (stage 2): client requests are batched, up to `ProxyBatchSize =
cf.batchSize` of them; a batch is sent as the new object `(k, ProSeq)` when full, or, if not
empty, when the ticker fires (`CliIds[:IdsSqsCtr]`, ...). Each request carries one command, so the
slices advance together. The pending batch `P` keeps its requests' receipts; at the send
`newBatch_step` records it (`newObj`'s batch: the requests distinct, the keys free, since the
proxy's `robj` keys are those of the requests `R` already sent and receipts are exclusive) and
mints the object's permit `crTok`. `ProSeq` stays below `2^32`: each object has a request, and
the requests sent are distinct and within `nC × opBudget`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.Basics
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.proxy

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia.roles.server.layers.consensus rabia

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.proxy.Assumptions]

/-- The pairs `(c, n)` of the clients' requests within the budget. -/
def reqBox : List (Nat × Nat) :=
  (List.range nC).flatMap fun c => (List.range opBudget).map fun n => (c, n)

theorem reqBox_length : reqBox.length = nC * opBudget := by
  unfold reqBox nC
  simp [List.range_succ]
  omega

theorem mem_reqBox {r : Nat × Nat} (h : r.1 < nC ∧ r.2 < opBudget) : r ∈ reqBox := by
  simp only [reqBox, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨r.1, h.1, r.2, h.2, rfl⟩

/-- The pure part of the proxy's objects' state: `q` objects made, for the requests `R` (distinct,
within the budget; each object has at least one), the proxy's keys `K` those of the objects, the
permits `Q` minted those of the objects. -/
def ObjsOk (q : Nat) (R : List (Nat × Nat)) (K : List FKey) (Q : GMap Nat Unit) : Prop :=
  q ≤ R.length ∧ R.Nodup ∧ (∀ r ∈ R, r.1 < nC ∧ r.2 < opBudget) ∧
  (∀ key ∈ K, key.isObj = true ∧ (∀ X r, key = .robj X r → r ∈ R) ∧
    (∀ X j, key = .pobj (X, j) → j < q)) ∧
  (∀ j, Q.lookup j ≠ none → j < q)

theorem nodup_bound {R : List (Nat × Nat)} (hnd : R.Nodup) (hb : ∀ r ∈ R, r.1 < nC ∧ r.2 < opBudget) :
    R.length ≤ nC * opBudget := by
  rw [← reqBox_length]
  exact hnd.length_le_of_subset (fun r hr => mem_reqBox (hb r hr))

theorem rabiaN_srvKeysN (k : Nat) : (↑rabiaN : CoPset) ⊆ ⊤ \ ↑(srvKeysN k) := by
  have hd : (↑rabiaN : CoPset) ## ↑(srvKeysN k) := by
    unfold rabiaN srvKeysN
    exact ndot_preserve_disjoint_r _ (ndot_ne_disjoint rabiaR (by decide))
  intro x hx
  exact Iris.Std.LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h => hd x ⟨hx, h⟩⟩

/-- The proxy's objects' ghost state. -/
def objsRes (γl : SrvNames) (q : Nat) (R : List (Nat × Nat)) (K : List FKey) (Q : GMap Nat Unit) :
    IProp GF :=
  iprop(keysPart γl true K ∗ crAuth γl Q ∗ ([∗list] r ∈ R, pRcpt γl r.1 r.2) ∗ ⌜ObjsOk q R K Q⌝)

theorem objsRes_init (γl : SrvNames) :
    keysPart (GF := GF) γl true [] ∗ crAuth γl ∅ ⊢ objsRes γl 0 [] [] ∅ := by
  unfold objsRes
  iintro ⟨Hkp, Hcr⟩
  iframe Hkp Hcr
  isplitr
  · iapply BigSepL.bigSepL_nil.2; itrivial
  ipureintro
  exact ⟨Nat.le_refl _, List.nodup_nil, by simp, by simp, fun j h => absurd rfl h⟩

/-- A pending request (in the batch being formed): its id and its command. -/
abbrev PReq := (Nat × Nat) × GoString

/-- The pending requests are proxy `k`'s clients', within the budget, with valid commands. -/
def PendOk (cf : RCfg) (k : Nat) (P : List PReq) : Prop :=
  ∀ p ∈ P, p.1.1 < nC ∧ p.1.1 % cf.n = k ∧ p.1.2 < opBudget ∧
    ∃ i, p.2 = cmdOf i ∧ inputOk i ∧ p.2.length < cmdBound

/-- Receipts are exclusive: a request whose receipt is held is not among `L`'s. -/
theorem pRcpt_notin (γl : SrvNames) (L : List (Nat × Nat)) (c n : Nat) :
    pRcpt (GF := GF) γl c n ∗ ([∗list] r ∈ L, pRcpt γl r.1 r.2) ⊢ ⌜(c, n) ∉ L⌝ := by
  iintro ⟨Hrc, HR⟩
  iintro %hmem
  ihave Hr := BigSepL.bigSepL_mem (Φ := fun r : Nat × Nat => pRcpt (GF := GF) γl r.1 r.2) hmem $$ HR
  unfold pRcpt
  ihave %hne := ghostMapElem_ne γl.prc (c, n) (c, n) _ () () $$ Hrc Hr
  exact absurd rfl hne

/-- A new object `(k, q)` for the batch `P` of pending requests (their receipts held): recorded
(`newObj`), its permit minted. -/
theorem newBatch_step (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (q : Nat)
    (R : List (Nat × Nat)) (K : List FKey) (Q : GMap Nat Unit) (P : List PReq)
    (hP : PendOk cf k P) (hne : P ≠ []) (hnd : (R ++ P.map Prod.fst).Nodup) :
    isRabia (GF := GF) γ.rab ∗ cfgIs γ.rab cf ∗ isSrvKeys γ k γl ∗
      regFacts γ.rab (P.map Prod.fst) (P.map Prod.snd) ∗
      ([∗list] r ∈ P.map Prod.fst, pRcpt γl r.1 r.2) ∗ objsRes γl q R K Q ⊢
    |={⊤}=> ∃ K', objsRes γl (q + 1) (R ++ P.map Prod.fst) K' (Q.insert q ()) ∗ crTok γl q ∗
      fact γ.rab (.pobj (k, q)) (.reqs (P.map Prod.fst)) := by
  iintro ⟨#Hrab, #Hcfg, #Hkeys, #Hreg, HP, Hres⟩
  unfold objsRes
  icases Hres with ⟨Hkp, Hcr, HR, %hok⟩
  obtain ⟨hl, hRnd, hb, hK, hQ⟩ := hok
  have hdisj : ∀ r ∈ P.map Prod.fst, r ∉ R := by
    intro r hr hR
    exact (List.nodup_append.mp hnd).2.2 r hR r hr rfl
  -- the keys
  imod srvKeys_acc γ k γl true ⊤ (fun _ _ => CoPset.mem_full) K $$ [$Hkeys $Hkp]
    with ⟨%Kall, %Ko, HK, %hKo, Hclose⟩
  obtain ⟨hperm, hKo⟩ := hKo
  have hq : FKey.pobj (k, q) ∉ Kall := by
    intro h
    rcases List.mem_append.mp (hperm.mem_iff.mp h) with h | h
    · have := (hK _ h).2.2 k q rfl; omega
    · have := hKo _ h; simp [model.FKey.isObj] at this
  have hr : ∀ r ∈ P.map Prod.fst, FKey.robj k r ∉ Kall := by
    intro r hrP h
    rcases List.mem_append.mp (hperm.mem_iff.mp h) with h | h
    · exact hdisj r hrP ((hK _ h).2.1 k r rfl)
    · have := hKo _ h; simp [model.FKey.isObj] at this
  have hX : ∀ r ∈ P.map Prod.fst, r.1 % cf.n = k := by
    intro r hrP
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrP
    exact (hP p hp).2.1
  have hne' : P.map Prod.fst ≠ [] := by simpa using hne
  imod newObj γ.rab _ (rabiaN_srvKeysN k) cf k q Kall (P.map Prod.fst) (P.map Prod.snd) hne'
      (List.nodup_append.mp hnd).2.1 hX hq hr $$ [$Hrab $Hcfg $HK $Hreg]
    with ⟨HK, #Hpo, -⟩
  imod Hclose $$ %((P.map Prod.fst).map (FKey.robj k) ++ .pobj (k, q) :: Kall)
      %((P.map Prod.fst).map (FKey.robj k) ++ .pobj (k, q) :: K) [HK] with Hkp
  · iframe HK
    ipureintro
    refine ⟨?_, ?_⟩
    · rw [List.append_assoc, List.cons_append]
      exact List.Perm.append_left _ (List.Perm.cons _ hperm)
    · intro key hkey
      simp only [List.mem_append, List.mem_cons, List.mem_map] at hkey
      rcases hkey with ⟨r, -, rfl⟩ | rfl | h
      · rfl
      · rfl
      · exact (hK _ h).1
  -- the permit
  have hQq : Q.lookup q = none := by
    cases h : Q.lookup q with
    | none => rfl
    | some u => exact absurd (hQ q (by simp [h])) (Nat.lt_irrefl _)
  unfold crAuth
  imod ghost_map_insert q () hQq $$ Hcr with ⟨Hcr, Htok⟩
  imodintro
  iexists (P.map Prod.fst).map (FKey.robj k) ++ .pobj (k, q) :: K
  iframe Hkp Hcr Hpo
  isplitr [Htok]
  · isplitl [HR HP]
    · iapply BigSepL.bigSepL_append.2
      iframe HR HP
    ipureintro
    have hPl : 1 ≤ P.length := by
      cases P with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    refine ⟨by simp; omega, hnd, ?_, ?_, ?_⟩
    · intro r hr'
      rcases List.mem_append.mp hr' with h | h
      · exact hb r h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact ⟨(hP p hp).1, (hP p hp).2.2.1⟩
    · intro key hkey
      simp only [List.mem_append, List.mem_cons, List.mem_map] at hkey
      rcases hkey with ⟨r, hrP, rfl⟩ | rfl | h
      · refine ⟨rfl, ?_, ?_⟩
        · intro X r' e; cases e; exact List.mem_append_right _ (List.mem_map.mpr hrP)
        · intro X j e; cases e
      · refine ⟨rfl, ?_, ?_⟩
        · intro X r e; cases e
        · intro X j e; cases e; omega
      · obtain ⟨h1, h2, h3⟩ := hK _ h
        exact ⟨h1, fun X r e => List.mem_append_left _ (h2 X r e),
          fun X j e => by have := h3 X j e; omega⟩
    · intro j hj
      by_cases e : j = q
      · omega
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hj; have := hQ j hj; omega
  · unfold crTok; iexact Htok

/-- The batch being formed: the slices (of `batchSize` elements) hold the pending requests' ids,
sequence numbers and commands in their first `|P|` places, `|P| < batchSize`. -/
def BatchOk (cf : RCfg) (k : Nat) (P : List PReq) (l1 l2 : List w32) (l3 : List GoString) :
    Prop :=
  l1.length = cf.batchSize ∧ l2.length = cf.batchSize ∧ l3.length = cf.batchSize ∧
  P.length < cf.batchSize ∧ l1.take P.length = P.map (fun p => BitVec.ofNat 32 p.1.1) ∧
  l2.take P.length = P.map (fun p => BitVec.ofNat 32 p.1.2) ∧
  l3.take P.length = P.map Prod.snd ∧ PendOk cf k P

theorem objsRes_notin (γl : SrvNames) (q : Nat) (R : List (Nat × Nat)) (K : List FKey)
    (Q : GMap Nat Unit) (c n : Nat) :
    pRcpt (GF := GF) γl c n ∗ objsRes γl q R K Q ⊢ ⌜(c, n) ∉ R⌝ := by
  unfold objsRes
  iintro ⟨Hrc, ⟨-, -, HR, -⟩⟩
  iapply pRcpt_notin γl R c n $$ [Hrc HR]
  iframe

theorem objsRes_bound (γl : SrvNames) (q : Nat) (R : List (Nat × Nat)) (K : List FKey)
    (Q : GMap Nat Unit) : objsRes (GF := GF) γl q R K Q ⊢ ⌜q ≤ nC * opBudget⌝ := by
  unfold objsRes
  iintro ⟨-, -, -, %h⟩
  ipureintro
  exact Nat.le_trans h.1 (nodup_bound h.2.1 h.2.2.1)

theorem regFacts_snocP (γ : RabiaNames) (P : List PReq) (x : PReq) :
    regFacts (GF := GF) γ (P.map Prod.fst) (P.map Prod.snd) ∗ fact γ (.reg x.1) (.cmd x.2) ⊢
      regFacts γ ((P ++ [x]).map Prod.fst) ((P ++ [x]).map Prod.snd) := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  exact regFacts_snoc γ _ _ x.1 x.2

theorem rcpts_snocP (γl : SrvNames) (P : List PReq) (x : PReq) :
    ([∗list] r ∈ P.map Prod.fst, pRcpt (GF := GF) γl r.1 r.2) ∗ pRcpt γl x.1.1 x.1.2 ⊢
      [∗list] r ∈ (P ++ [x]).map Prod.fst, pRcpt γl r.1 r.2 := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  exact BigSepL.bigSepL_snoc.2

/-- The batch's object (made by proxy `k` as its object `q`) carries its requests' facts. -/
theorem objOk_batch (γ : Names) (cf : RCfg) (k : Nat) (id ps : w32) (q : Nat) (P : List PReq)
    (hid : id.toNat = k) (hk : k < cf.n) (hps : ps.toNat = q) (hP : PendOk cf k P)
    (hne : P ≠ []) (hPB : P.length ≤ cf.batchSize) :
    fact (GF := GF) γ.rab (.pobj (k, q)) (.reqs (P.map Prod.fst)) ∗
      regFacts γ.rab (P.map Prod.fst) (P.map Prod.snd) ⊢
    objOk γ cf ⟨id, ps, 0, false, P.map (fun p => BitVec.ofNat 32 p.1.1),
      P.map (fun p => BitVec.ofNat 32 p.1.2), P.map Prod.snd⟩ := by
  iintro ⟨#Hpo, #Hreg⟩
  unfold objOk
  iexists P.map Prod.fst
  dsimp only
  rw [hps, hid]
  iframe Hpo Hreg
  ipureintro
  refine ⟨rfl, by simp [List.map_map], by simp [List.map_map], ?_, by simpa using hPB, ?_,
    by omega, ?_⟩
  · cases P with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨h1, -, h3, -⟩ := hP x hx
    exact ⟨h1, by simp only [opBudget] at h3; omega⟩
  · intro cmd hcmd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcmd
    exact (hP x hx).2.2.2

theorem bmsgOk_batch (γ : Names) (cf : RCfg) (k : Nat) (o : ObjV) (ho : o.proId.toNat = k) :
    objOk (GF := GF) γ cf o ⊢ bmsgOk γ cf k ⟨W32 0, 0, 0, some o⟩ := by
  iintro Ho
  unfold bmsgOk
  simp only [show (W32 0 : w32) = tyClientRequest from rfl, ↓reduceIte]
  iexists o
  iframe Ho
  ipureintro; exact ⟨rfl, ho⟩

theorem take_set_succ {α : Type} (l : List α) (n : Nat) (x : α) (h : n < l.length) :
    (l.set n x).take (n + 1) = l.take n ++ [x] := by
  induction l generalizing n with
  | nil => simp at h
  | cons a l ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append]
      rw [ih n (by simp at h; omega)]

theorem batchSize_bounds {cf : RCfg} (h : cf.Ok) : 1 ≤ cf.batchSize ∧ cf.batchSize ≤ 10 := by
  obtain ⟨-, hb, -, -⟩ := h
  unfold RCfg.batchSize
  have : cf.batch = 0 ∨ cf.batch = 1 ∨ cf.batch = 2 ∨ cf.batch = 3 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

theorem batchMs_bounds {cf : RCfg} (h : cf.Ok) : 1 ≤ cf.batchMs ∧ cf.batchMs ≤ 50 := by
  obtain ⟨-, -, hb, -⟩ := h
  unfold RCfg.batchMs
  have : cf.bms = 0 ∨ cf.bms = 1 ∨ cf.bms = 2 ∨ cf.bms = 3 ∨ cf.bms = 4 := by omega
  rcases this with h | h | h | h | h <;> rw [h] <;> decide

set_option maxHeartbeats 1000000 in
theorem Proxy.CmdReceiver.wp_proof : Proxy.CmdReceiver.spec (GF := GF) := by
  intro γ cf k γl ch p
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  ihave %hcf : ⌜cf.Ok⌝ $$ [Hcfg]
  · unfold cfgIs; icases Hcfg with ⟨-, %h⟩; ipureintro; exact h
  obtain ⟨hB1, hB10⟩ := batchSize_bounds hcf
  obtain ⟨hM1, hM50⟩ := batchMs_bounds hcf
  wp_apply wp_with_defer as %dfr Hdfr
  unfold proxyCmdRes
  icases Hres with ⟨%wg, %t, %kv, %ledger, %hk, #Hf, #Hchans, #Hkeys, Hkp, Hcr⟩
  unfold proxyFields
  icases Hf with ⟨%id, %hid, #HSvrId, #HWg, #HDone, #HCin, #HToNet, #HNetIn, #HTCP, #HKV, #HExec,
    #HExecR, #HLedger, -⟩
  icases confRO_val $$ Hconf with ⟨%ps, #Hc⟩
  iStructNamed Hc
  wp_auto
  wp_apply time.wp_NewTicker as %tk %tch %γt #Htk
  · ipureintro; word
  simp only [confVal]
  wp_apply wp_slice_make2 (V := w32) _ as %s1 ⟨Hs1, Hs1c⟩
  · ipureintro; word
  wp_apply wp_slice_make2 (V := w32) _ as %s2 ⟨Hs2, Hs2c⟩
  · ipureintro; word
  wp_apply wp_slice_make2 (V := GoString) _ as %s3 ⟨Hs3, Hs3c⟩
  · ipureintro; word
  unfold shared
  icases Hsh with ⟨#Hrab, -⟩
  unfold time.isTicker
  icases Htk with ⟨#HtC, -, -, #Htbag⟩
  unfold srvChans
  icases Hchans with ⟨#Hbdone, #Hbc2p, #Hbp2n, #Hbn2p, -⟩
  have hBz : sint.nat (W64 (cf.batchSize : Int)) = cf.batchSize := by word
  have hBz' : sint.nat (W64 (cf.batchSize : Int) * W64 1) = cf.batchSize := by word
  ihave IH : iprop(∃ (q : Nat) (R : List (Nat × Nat)) (K : List FKey) (Q : GMap Nat Unit)
      (P : List PReq) (s1 s2 s3 : GoSlice) (l1 l2 : List w32) (l3 : List GoString),
      "CliIds" ∷ CliIds_ptr ↦ s1 ∗ "Hs1" ∷ s1 ↦* l1 ∗ "CliSqs" ∷ CliSqs_ptr ↦ s2 ∗
      "Hs2" ∷ s2 ↦* l2 ∗ "Values" ∷ Values_ptr ↦ s3 ∗ "Hs3" ∷ s3 ↦* l3 ∗
      "%Hls" ∷ ⌜BatchOk cf k P l1 l2 l3 ∧ (R ++ P.map Prod.fst).Nodup⌝ ∗
      "IdsSqsCtr" ∷ IdsSqsCtr_ptr ↦ W64 (P.length : Int) ∗
      "ValuesCtr" ∷ ValuesCtr_ptr ↦ W64 (P.length : Int) ∗
      "ProSeq" ∷ ProSeq_ptr ↦ W64 (q : Int) ∗ "Hobjs" ∷ objsRes γl q R K Q ∗
      "HP" ∷ ([∗list] r ∈ P.map Prod.fst, pRcpt γl r.1 r.2) ∗
      "#Hreg" ∷ regFacts γ.rab (P.map Prod.fst) (P.map Prod.snd))
      $$ [CliIds Hs1 CliSqs Hs2 Values Hs3 IdsSqsCtr ValuesCtr ProSeq Hkp Hcr]
  · iexists 0, ([] : List (Nat × Nat)), ([] : List FKey), (∅ : GMap Nat Unit), ([] : List PReq),
      s1, s2, s3
    iexists _, _, _
    simp only [Int.natCast_zero, List.length_nil, List.map_nil]
    iframe CliIds Hs1 CliSqs Hs2 Values Hs3 IdsSqsCtr ValuesCtr ProSeq
    isplitr
    · ipureintro
      refine ⟨⟨?_, ?_, ?_, ?_, by simp, by simp, by simp, by simp [PendOk]⟩, List.nodup_nil⟩
      · simp only [List.length_replicate]; exact hBz
      · simp only [List.length_replicate]; exact hBz
      · simp only [List.length_replicate]; exact hBz'
      · simp; omega
    isplitl [Hkp Hcr]
    · iapply objsRes_init $$ [$Hkp $Hcr]
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iapply regFacts_nil
  wp_for_core
  iNamed IH
  wp_auto_lc 1
  irename Hlc1 => Hlc0
  cleanup_bool_decide
  wp_auto_lc 1
  irename Hlc1 => Hlc2
  irename Hlc0 => Hlc1
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `Done`: nothing comes
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbdone
    iapply bag_false_recv_au γl.done ch.done doneP (fun _ => .rfl) $$ [$Hlc1 $Hlc2] Hbdone
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a request
    simp only [chan.blockingClausePre]
    iexists Command, inferInstance, inferInstance, inferInstance, inferInstance, ch.c2p, γl.c2p
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbc2p
    iapply bag_recv_au γl.c2p ch.c2p (c2pP γ cf k γl) _ $$ [$Hlc1 $Hlc2] Hbc2p
    inext
    iintro %v Hv
    unfold c2pP
    icases Hv with ⟨%c, %qc, %hcq, #Hcrep, Hreq, Hrc⟩
    obtain ⟨hc, hck, hqb, hqlen⟩ := hcq
    unfold reqOk
    icases Hreq with ⟨%cmd, %hreq, #Hregc⟩
    obtain ⟨hcid, hcmds, -, i, hcmd, hi⟩ := hreq
    unfold cmdRep
    icases Hcrep with ⟨%hv, #Hvcmds⟩
    obtain ⟨⟨hl1, hl2, hl3, hPB, ht1, ht2, ht3, hPok⟩, hnd⟩ := Hls
    ihave %hnew1 := objsRes_notin γl q R K Q c qc.cliSeq.toNat $$ [Hrc Hobjs]
    · iframe
    ihave %hnew2 := pRcpt_notin γl (P.map Prod.fst) c qc.cliSeq.toNat $$ [Hrc HP]
    · iframe
    ihave %Hs1l := ownSlice_len _ _ _ $$ Hs1
    ihave %Hs2l := ownSlice_len _ _ _ $$ Hs2
    ihave %Hs3l := ownSlice_len _ _ _ $$ Hs3
    ihave %Hvcl := ownSlice_len _ _ _ $$ Hvcmds
    have h1 : sint.Z s1.len = cf.batchSize := by obtain ⟨a, b⟩ := Hs1l; rw [hl1] at a; word
    have h2 : sint.Z s2.len = cf.batchSize := by obtain ⟨a, b⟩ := Hs2l; rw [hl2] at a; word
    have h3 : sint.Z s3.len = cf.batchSize := by obtain ⟨a, b⟩ := Hs3l; rw [hl3] at a; word
    have h4 : sint.Z v.Commands'.len = 1 := by
      obtain ⟨a, b⟩ := Hvcl; rw [hcmds] at a; simp at a; word
    have hnZ : sint.Z (W64 (P.length : Int)) = P.length := by word
    wp_auto
    rw [ite_eq_left (by rw [hnZ, h1]; omega)]
    wp_apply wp_store_slice_index $$ [$Hs1] as Hs1
    · ipureintro; rw [hnZ, hl1]; omega
    rw [ite_eq_left (by rw [hnZ, h2]; omega)]
    wp_apply wp_store_slice_index $$ [$Hs2] as Hs2
    · ipureintro; rw [hnZ, hl2]; omega
    ihave IH2 : iprop(∃ (j : w64) (vv : GoString) (vc : w64) (l3' : List GoString),
        "i" ∷ i_ptr ↦ j ∗ "v" ∷ v_ptr ↦ vv ∗ "ValuesCtr" ∷ ValuesCtr_ptr ↦ vc ∗ "Hs3" ∷ s3 ↦* l3' ∗
        "%Hj" ∷ ⌜(j = W64 0 ∧ vc = W64 (P.length : Int) ∧ l3' = l3) ∨
          (j = W64 1 ∧ vc = W64 ((P.length + 1 : Nat) : Int) ∧ l3' = l3.set P.length cmd)⌝)
        $$ [i v ValuesCtr Hs3]
    · iexists _, _, _, l3
      iframe
      ipureintro; left; exact ⟨rfl, rfl, rfl⟩
    wp_for IH2
    wp_if_destruct
    · rcases Hj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rw [ite_eq_left (by rw [h4]; decide)]
        wp_apply wp_load_slice_index _ _ _ _ cmd (by decide) $$ [$Hvcmds] as -
        · ipureintro; rw [hcmds]; rfl
        rw [ite_eq_left (by rw [hnZ, h3]; omega)]
        wp_apply wp_store_slice_index $$ [$Hs3] as Hs3
        · ipureintro; rw [hnZ, hl3]; omega
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro; right
        refine ⟨rfl, by word, by rw [hnZ]; rfl⟩
      · exfalso; revert Hif; rw [h4]; decide
    rcases Hj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exfalso; revert Hif; rw [h4]; decide
    -- the batch with the new request
    have hcid' : v.CliId' = BitVec.ofNat 32 c := hv.1.trans hcid
    have hseq' : v.CliSeq' = BitVec.ofNat 32 qc.cliSeq.toNat := by rw [hv.2.1]; simp
    have hcmdb : cmd.length < cmdBound := Nat.lt_of_lt_of_le (cmd_lt_encCmd hcmds) hqlen
    have hPok' : PendOk cf k (P ++ [((c, qc.cliSeq.toNat), cmd)]) := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hPok x h
      · simp only [List.mem_singleton] at h; subst h; exact ⟨hc, hck, hqb, i, hcmd, hi, hcmdb⟩
    have ht1' : (l1.set P.length v.CliId').take (P.length + 1) =
        (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.1) := by
      rw [take_set_succ _ _ _ (by omega), ht1, hcid']; simp
    have ht2' : (l2.set P.length v.CliSeq').take (P.length + 1) =
        (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.2) := by
      rw [take_set_succ _ _ _ (by omega), ht2, hseq']; simp
    have ht3' : (l3.set P.length cmd).take (P.length + 1) =
        (P ++ [((c, qc.cliSeq.toNat), cmd)]).map Prod.snd := by
      rw [take_set_succ _ _ _ (by omega), ht3]; simp
    have hnd' : (R ++ (P ++ [((c, qc.cliSeq.toNat), cmd)]).map Prod.fst).Nodup := by
      rw [List.map_append, ← List.append_assoc]
      refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
      intro a ha b hb e
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb; subst e
      rcases List.mem_append.mp ha with h | h
      · exact hnew1 h
      · exact hnew2 h
    ihave #Hreg' := regFacts_snocP γ.rab P ((c, qc.cliSeq.toNat), cmd) $$ [Hreg Hregc]
    · dsimp only; isplit <;> iassumption
    ihave HP' := rcpts_snocP γl P ((c, qc.cliSeq.toNat), cmd) $$ [HP Hrc]
    · dsimp only; iframe
    have hlen' : (P ++ [((c, qc.cliSeq.toNat), cmd)]).length = P.length + 1 := by simp
    wp_if_destruct
    · -- a full batch: sent
      have hfull : P.length + 1 = cf.batchSize := by
        have := congrArg (fun w : w64 => sint.Z w) Hif
        word
      simp only [hnZ, Int.toNat_natCast]
      have hf1 : l1.set P.length v.CliId' =
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.1) := by
        rw [← ht1', List.take_of_length_le (by simp [hl1]; omega)]
      have hf2 : l2.set P.length v.CliSeq' =
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.2) := by
        rw [← ht2', List.take_of_length_le (by simp [hl2]; omega)]
      have hf3 : l3.set P.length cmd = (P ++ [((c, qc.cliSeq.toNat), cmd)]).map Prod.snd := by
        rw [← ht3', List.take_of_length_le (by simp [hl3]; omega)]
      rw [hf1, hf2, hf3]
      imod newBatch_step γ cf k γl q R K Q _ hPok' (by simp) hnd'
          $$ [$Hrab $Hcfg $Hkeys $Hreg' $HP' $Hobjs] with ⟨%K', Hobjs, Htok, #Hpo⟩
      ihave %hqb' := objsRes_bound γl (q + 1) _ K' _ $$ [Hobjs]
      · iframe
      have hq32 : q < 2 ^ 32 := by simp only [nC, opBudget] at hqb'; omega
      have hq : (W32 (sint.Z (W64 (q : Int)))).toNat = q := by word
      ipersist obj
      ipersist Hs1
      ipersist Hs2
      ipersist Hs3
      wp_apply wp_bag_send γl.p2n ch.p2n _ (p2nP γ cf k γl) $$ [$Hbp2n Htok]
      · unfold p2nP
        iexists (⟨W32 0, 0, 0, some ⟨id, W32 (sint.Z (W64 (q : Int))), 0, false,
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.1),
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.2),
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map Prod.snd⟩⟩ : MsgV), (⟨id, W32 (sint.Z (W64 (q : Int))), 0, false,
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.1),
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map (fun p => BitVec.ofNat 32 p.1.2),
          (P ++ [((c, qc.cliSeq.toNat), cmd)]).map Prod.snd⟩ : ObjV)
        isplitr
        · ipureintro; exact ⟨(rfl : (W32 0 : w32) = tyClientRequest), rfl⟩
        isplitr
        · unfold msgRep
          isplitr
          · ipureintro; exact ⟨rfl, rfl, rfl⟩
          dsimp only
          iexists _
          iframe obj
          unfold objRep
          iframe Hs1 Hs2 Hs3
          ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
        isplitr
        · iapply bmsgOk_batch γ cf k _ hid
          iapply objOk_batch γ cf k id _ q _ hid hk hq hPok' (by simp) (by rw [hlen']; omega)
            $$ [Hpo Hreg']
          isplit <;> iassumption
        dsimp only
        rw [hq]
        iexact Htok
      wp_apply wp_slice_make2 (V := w32) _ as %s1' ⟨Hs1', -⟩
      · ipureintro; word
      wp_apply wp_slice_make2 (V := w32) _ as %s2' ⟨Hs2', -⟩
      · ipureintro; word
      wp_apply wp_slice_make2 (V := GoString) _ as %s3' ⟨Hs3', -⟩
      · ipureintro; word
      wp_for_post
      iframe
      iexists q + 1, R ++ (P ++ [((c, qc.cliSeq.toNat), cmd)]).map Prod.fst, K', Q.insert q (),
        ([] : List PReq), s1', s2', s3'
      iexists _, _, _
      have hq1 : W64 (q : Int) + W64 1 = W64 ((q + 1 : Nat) : Int) := by word
      rw [hq1]
      simp only [List.length_nil, List.map_nil, Int.natCast_zero]
      iframe
      isplitr
      · ipureintro
        refine ⟨⟨?_, ?_, ?_, by simp; omega, by simp, by simp, by simp, by simp [PendOk]⟩, ?_⟩
        · simp only [List.length_replicate]; exact hBz
        · simp only [List.length_replicate]; exact hBz
        · simp only [List.length_replicate]; exact hBz'
        · simpa using hnd'
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      iapply regFacts_nil
    · -- not full yet
      have hnfull : P.length + 1 < cf.batchSize := by
        have : P.length + 1 ≠ cf.batchSize := by
          intro e; apply Hif; rw [← e]; word
        omega
      wp_for_post
      iframe
      iexists q, R, K, Q, P ++ [((c, qc.cliSeq.toNat), cmd)], s1, s2, s3
      iexists _, _, _
      iframe
      have hctr : W64 (P.length : Int) + W64 1 =
          W64 ((P ++ [((c, qc.cliSeq.toNat), cmd)]).length : Int) := by rw [hlen']; word
      rw [hctr]
      have hctr' : W64 ((P.length + 1 : Nat) : Int) =
          W64 ((P ++ [((c, qc.cliSeq.toNat), cmd)]).length : Int) := by rw [hlen']
      rw [hctr']
      simp only [hnZ, Int.toNat_natCast]
      iframe
      isplitr
      · ipureintro
        refine ⟨⟨by simp [hl1], by simp [hl2], by simp [hl3], by rw [hlen']; omega, ?_, ?_, ?_, hPok'⟩,
          hnd'⟩
        · rw [hlen']; exact ht1'
        · rw [hlen']; exact ht2'
        · rw [hlen']; exact ht3'
      iexact Hreg'
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the ticker: a partial batch, if any request is pending
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au γt tch (fun _ => iprop(True)) _ $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %v -
    wp_auto
    wp_if_destruct
    · wp_for_post
      iframe
      iexists q, R, K, Q, P, s1, s2, s3, l1, l2, l3
      iframe
      isplitr
      · ipureintro; exact Hls
      iexact Hreg
    obtain ⟨⟨hl1, hl2, hl3, hPB, ht1, ht2, ht3, hPok⟩, hnd⟩ := Hls
    have hnZ : sint.Z (W64 (P.length : Int)) = P.length := by word
    have hz0 : sint.Z (W64 0) = 0 := rfl
    have hne : P ≠ [] := by
      intro e; apply Hif; rw [e]; rfl
    clear Hif
    ihave %Hs1l := ownSlice_len _ _ _ $$ Hs1
    ihave %Hs2l := ownSlice_len _ _ _ $$ Hs2
    ihave %Hs3l := ownSlice_len _ _ _ $$ Hs3
    ihave %Hw1 := ownSlice_wf _ _ _ $$ Hs1
    ihave %Hw2 := ownSlice_wf _ _ _ $$ Hs2
    ihave %Hw3 := ownSlice_wf _ _ _ $$ Hs3
    have h1 : sint.Z s1.len = cf.batchSize := by obtain ⟨a, b⟩ := Hs1l; rw [hl1] at a; word
    have h2 : sint.Z s2.len = cf.batchSize := by obtain ⟨a, b⟩ := Hs2l; rw [hl2] at a; word
    have h3 : sint.Z s3.len = cf.batchSize := by obtain ⟨a, b⟩ := Hs3l; rw [hl3] at a; word
    rw [ite_eq_left (by rw [hnZ, hz0]; omega)]
    wp_auto
    rw [ite_eq_left (by rw [hnZ, hz0]; omega)]
    wp_auto
    rw [ite_eq_left (by rw [hnZ, hz0]; omega)]
    wp_auto
    imod newBatch_step γ cf k γl q R K Q P hPok hne hnd
        $$ [$Hrab $Hcfg $Hkeys $Hreg $HP $Hobjs] with ⟨%K', Hobjs, Htok, #Hpo⟩
    ihave %hqb' := objsRes_bound γl (q + 1) _ K' _ $$ [Hobjs]
    · iframe
    have hq32 : q < 2 ^ 32 := by simp only [nC, opBudget] at hqb'; omega
    have hq : (W32 (sint.Z (W64 (q : Int)))).toNat = q := by word
    have hnN : sint.nat (W64 (P.length : Int)) = P.length := by word
    have hz0' : sint.nat (W64 0) = 0 := rfl
    ihave Hs1' := (ownSlice_slice (W64 0) (W64 (P.length : Int)) s1 (DFrac.own 1) l1
      ⟨by rw [hz0]; omega, by rw [hz0, hnZ]; omega, by rw [hnZ, h1]; omega⟩).1 $$ Hs1
    icases Hs1' with ⟨-, Hs1, -⟩
    ihave Hs2' := (ownSlice_slice (W64 0) (W64 (P.length : Int)) s2 (DFrac.own 1) l2
      ⟨by rw [hz0]; omega, by rw [hz0, hnZ]; omega, by rw [hnZ, h2]; omega⟩).1 $$ Hs2
    icases Hs2' with ⟨-, Hs2, -⟩
    ihave Hs3' := (ownSlice_slice (W64 0) (W64 (P.length : Int)) s3 (DFrac.own 1) l3
      ⟨by rw [hz0]; omega, by rw [hz0, hnZ]; omega, by rw [hnZ, h3]; omega⟩).1 $$ Hs3
    icases Hs3' with ⟨-, Hs3, -⟩
    rw [hz0', hnN]
    simp only [subslice, List.drop_zero]
    rw [ht1, ht2, ht3]
    ipersist obj
    ipersist Hs1
    ipersist Hs2
    ipersist Hs3
    wp_apply wp_bag_send γl.p2n ch.p2n _ (p2nP γ cf k γl) $$ [$Hbp2n Htok]
    · unfold p2nP
      iexists (⟨W32 0, 0, 0, some ⟨id, W32 (sint.Z (W64 (q : Int))), 0, false,
          P.map (fun p => BitVec.ofNat 32 p.1.1), P.map (fun p => BitVec.ofNat 32 p.1.2),
          P.map Prod.snd⟩⟩ : MsgV), (⟨id, W32 (sint.Z (W64 (q : Int))), 0, false,
          P.map (fun p => BitVec.ofNat 32 p.1.1), P.map (fun p => BitVec.ofNat 32 p.1.2),
          P.map Prod.snd⟩ : ObjV)
      isplitr
      · ipureintro; exact ⟨(rfl : (W32 0 : w32) = tyClientRequest), rfl⟩
      isplitr
      · unfold msgRep
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        dsimp only
        iexists _
        iframe obj
        unfold objRep
        iframe Hs1 Hs2 Hs3
        ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      isplitr
      · iapply bmsgOk_batch γ cf k _ hid
        iapply objOk_batch γ cf k id _ q _ hid hk hq hPok hne (by omega) $$ [Hpo Hreg]
        isplit <;> iassumption
      dsimp only
      rw [hq]
      iexact Htok
    wp_apply wp_slice_make2 (V := w32) _ as %s1' ⟨Hs1', -⟩
    · ipureintro; word
    wp_apply wp_slice_make2 (V := w32) _ as %s2' ⟨Hs2', -⟩
    · ipureintro; word
    wp_apply wp_slice_make2 (V := GoString) _ as %s3' ⟨Hs3', -⟩
    · ipureintro; word
    wp_for_post
    iframe
    iexists q + 1, R ++ P.map Prod.fst, K', Q.insert q (), ([] : List PReq), s1', s2', s3'
    iexists _, _, _
    have hq1 : W64 (q : Int) + W64 1 = W64 ((q + 1 : Nat) : Int) := by word
    rw [hq1]
    simp only [List.length_nil, List.map_nil, Int.natCast_zero]
    iframe
    isplitr
    · ipureintro
      refine ⟨⟨?_, ?_, ?_, by simp; omega, by simp, by simp, by simp, by simp [PendOk]⟩, ?_⟩
      · simp only [List.length_replicate]; exact hBz
      · simp only [List.length_replicate]; exact hBz
      · simp only [List.length_replicate]; exact hBz'
      · simpa using hnd
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iapply regFacts_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `NetIn`: nothing comes
    simp only [chan.blockingClausePre]
    iexists Msg, inferInstance, inferInstance, inferInstance, inferInstance, ch.n2p, γl.n2p
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbn2p
    iapply bag_false_recv_au γl.n2p ch.n2p n2pP (fun _ => .rfl) $$ [$Hlc1 $Hlc2] Hbn2p
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof
end Perennial.rabia.roles.server.layers.proxy
