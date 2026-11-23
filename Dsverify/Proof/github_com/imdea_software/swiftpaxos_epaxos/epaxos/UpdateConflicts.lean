/-
`(*Replica).updateConflicts` against the model's `updateConflicts`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The pair `updateConflicts` records for command `c`. -/
def ucPair (σ : RState) (q : Nat) (n : w32) (c : WCmd) : InstPair :=
  match σ.conflicts q c.key with
  | some p =>
    ⟨if p.last.slt n then n else p.last,
     if p.lastWrite.slt n ∧ c.op ≠ opGET then n else p.lastWrite⟩
  | none => ⟨n, if c.op ≠ opGET then n else W32 (-1)⟩

/-- The `maxSeqPerKey` entry `updateConflicts` records for command `c`. -/
def ucSeq (σ : RState) (seq : w32) (c : WCmd) : w32 :=
  match σ.maxSeqPerKey c.key with
  | some s => if s.slt seq then seq else s
  | none => seq

/-- `lastScan` after `updateConflicts` records command `c`. -/
def ucScan (σ : RState) (q : Nat) (n : w32) (c : WCmd) : Nat → w32 :=
  if c.op = opSCAN ∧ (σ.lastScan q).slt n then upd σ.lastScan q n else σ.lastScan

/-- `lastPut` after `updateConflicts` records command `c`. -/
def ucPut (σ : RState) (q : Nat) (n : w32) (c : WCmd) : Nat → w32 :=
  if c.op = opPUT ∧ (σ.lastPut q).slt n then upd σ.lastPut q n else σ.lastPut

theorem uc_take_succ (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) (j : Nat)
    (c : WCmd) (hc : cmds[j]? = some c) :
    updateConflicts σ (cmds.take (j + 1)) q n seq =
      { updateConflicts σ (cmds.take j) q n seq with
        conflicts := upd (updateConflicts σ (cmds.take j) q n seq).conflicts q
          (upd ((updateConflicts σ (cmds.take j) q n seq).conflicts q) c.key
            (some (ucPair (updateConflicts σ (cmds.take j) q n seq) q n c))),
        lastScan := ucScan (updateConflicts σ (cmds.take j) q n seq) q n c,
        lastPut := ucPut (updateConflicts σ (cmds.take j) q n seq) q n c,
        maxSeqPerKey := upd (updateConflicts σ (cmds.take j) q n seq).maxSeqPerKey c.key
            (some (ucSeq (updateConflicts σ (cmds.take j) q n seq) seq c)) } := by
  unfold updateConflicts
  rw [List.take_succ, hc, List.foldl_append]
  rfl

theorem uc_take_succ_scan (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) (j : Nat)
    (c : WCmd) (hc : cmds[j]? = some c) :
    (updateConflicts σ (cmds.take (j + 1)) q n seq).lastScan =
      ucScan (updateConflicts σ (cmds.take j) q n seq) q n c := by
  rw [uc_take_succ _ _ _ _ _ _ _ hc]

theorem uc_take_succ_put (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) (j : Nat)
    (c : WCmd) (hc : cmds[j]? = some c) :
    (updateConflicts σ (cmds.take (j + 1)) q n seq).lastPut =
      ucPut (updateConflicts σ (cmds.take j) q n seq) q n c := by
  rw [uc_take_succ _ _ _ _ _ _ _ hc]

theorem uc_take_succ_conf (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) (j : Nat)
    (c : WCmd) (hc : cmds[j]? = some c) :
    (updateConflicts σ (cmds.take (j + 1)) q n seq).conflicts q =
      upd ((updateConflicts σ (cmds.take j) q n seq).conflicts q) c.key
        (some (ucPair (updateConflicts σ (cmds.take j) q n seq) q n c)) := by
  rw [uc_take_succ _ _ _ _ _ _ _ hc]; simp [upd]

theorem uc_take_succ_msk (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) (j : Nat)
    (c : WCmd) (hc : cmds[j]? = some c) :
    (updateConflicts σ (cmds.take (j + 1)) q n seq).maxSeqPerKey =
      upd (updateConflicts σ (cmds.take j) q n seq).maxSeqPerKey c.key
        (some (ucSeq (updateConflicts σ (cmds.take j) q n seq) seq c)) := by
  rw [uc_take_succ _ _ _ _ _ _ _ hc]

theorem msk_insert (gm : GMap w64 w32) (f : w64 → Option w32) (h : ∀ k, gm !! k = f k)
    (K : w64) (v : w32) : ∀ k, (<[K := v]> gm) !! k = upd f K (some v) k := by
  intro k
  rw [GMap.lookup_insert_eq_iff]; unfold upd
  by_cases hk : k = K
  · subst hk; simp
  · rw [if_neg (Ne.symm hk), if_neg hk]; exact h k

theorem ucSeq_none (σ : RState) (seq : w32) (c : WCmd) (h : σ.maxSeqPerKey c.key = none) :
    ucSeq σ seq c = seq := by unfold ucSeq; rw [h]

theorem ucSeq_some (σ : RState) (seq s : w32) (c : WCmd) (h : σ.maxSeqPerKey c.key = some s) :
    ucSeq σ seq c = if sint.Z s < sint.Z seq then seq else s := by
  unfold ucSeq; rw [h]; simp only
  by_cases hs : sint.Z s < sint.Z seq
  · rw [if_pos ((slt_iff _ _).mpr hs), if_pos hs]
  · rw [if_neg (fun e => hs ((slt_iff _ _).mp e)), if_neg hs]

theorem upd_self_some (f : w64 → Option w32) (K : w64) (s : w32) (h : f K = some s) :
    ∀ k, f k = upd f K (some s) k := by
  intro k; unfold upd; split
  · subst_vars; exact h
  · rfl

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- The pair of a present key, opened (its pointer, then the row with a new pair there). -/
theorem conflictRow_present (m : GoMap) (row : w64 → Option InstPair) (K : w64) (p : InstPair)
    (h : row K = some p) :
    ownConflictRow (GF := GF) m row ⊢ ∃ (g : GMap w64 Loc) (l : Loc), m ↦$ g ∗ ⌜g.lookup K = some l⌝ ∗
      l ↦ epaxos.InstPair.mk p.last p.lastWrite ∗
      (∀ p' : InstPair, m ↦$ g -∗ l ↦ epaxos.InstPair.mk p'.last p'.lastWrite -∗
        ownConflictRow m (upd row K (some p'))) := by
  unfold ownConflictRow
  iintro ⟨%g, Hm, %Hdom, Hps⟩
  have hK : (g.lookup K).isSome = true := by rw [Hdom, h]; rfl
  obtain ⟨l, hl⟩ : ∃ l, g.lookup K = some l := Option.isSome_iff_exists.mp hK
  icases BigSepM.bigSepM_lookup_acc_impl hl $$ Hps with ⟨Hl, Hclose⟩
  iexists g, l
  iframe Hm
  isplitr
  · ipureintro; exact hl
  isplitl [Hl]
  · rw [h]; simp only [Option.map_some, Option.getD_some]; iexact Hl
  iintro %p' Hm Hl
  iexists g
  iframe Hm
  isplitr
  · ipureintro; intro k; unfold upd; split
    · subst_vars; rw [hl]; rfl
    · exact Hdom k
  iapply Hclose
  · iintro !> %k %v %_ %hk Hv
    unfold upd; rw [if_neg hk]; iexact Hv
  · unfold upd; simp only [if_true, Option.map_some, Option.getD_some]; iexact Hl

/-- An absent key (insert a new pair). -/
theorem conflictRow_absent (m : GoMap) (row : w64 → Option InstPair) (K : w64)
    (h : row K = none) :
    ownConflictRow (GF := GF) m row ⊢ ∃ (g : GMap w64 Loc), m ↦$ g ∗ ⌜g.lookup K = none⌝ ∗
      (∀ (l : Loc) (p' : InstPair), m ↦$ (g.insert K l) -∗
        l ↦ epaxos.InstPair.mk p'.last p'.lastWrite -∗ ownConflictRow m (upd row K (some p'))) := by
  unfold ownConflictRow
  iintro ⟨%g, Hm, %Hdom, Hps⟩
  have hK : g.lookup K = none := by
    have := Hdom K; rw [h] at this; simpa using this
  iexists g
  iframe Hm
  isplitr
  · ipureintro; exact hK
  iintro %l %p' Hm Hl
  iexists g.insert K l
  iframe Hm
  isplitr
  · ipureintro; intro k; unfold upd
    by_cases hk : k = K
    · subst hk; simp [GMap.lookup_insert]
    · rw [if_neg hk, GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact Hdom k
  iapply (BigSepM.bigSepM_insert (by exact hK)).2
  isplitl [Hl]
  · unfold upd; simp only [if_true, Option.map_some, Option.getD_some]; iexact Hl
  iapply (BigSepM.bigSepM_mono (fun {k v} hkv => ?_)) $$ Hps
  have hk : k ≠ K := by intro e; subst e; rw [show g.lookup k = _ from hkv] at hK; simp at hK
  unfold upd; rw [if_neg hk]

theorem wp_updateConflicts (r : Loc) (σ : RState) (cs : GoSlice) (cmds : List WCmd) (dq : DFrac)
    (q n seq : w32) (hq : 0 ≤ zz q ∧ zz q < nR) :
    {{ pkgInit_epaxos (GF := GF) ∗ ownCmds cs cmds dq ∗ repConf r σ.conflicts ∗ repMsk r σ.maxSeqPerKey ∗
        repRowArr r go!"lastScan" σ.lastScan ∗ repRowArr r go!"lastPut" σ.lastPut }}
      (App (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"updateConflicts")) (Val #cs)) (Val #q)) (Val #n)) (Val #seq))
    {{ RET #(); ownCmds cs cmds dq ∗
        repConf r (updateConflicts σ cmds (toN q) n seq).conflicts ∗
        repMsk r (updateConflicts σ cmds (toN q) n seq).maxSeqPerKey ∗
        repRowArr r go!"lastScan" (updateConflicts σ cmds (toN q) n seq).lastScan ∗
        repRowArr r go!"lastPut" (updateConflicts σ cmds (toN q) n seq).lastPut }} := by
  wp_start as ⟨Hcs, Hconf, Hmsk, HlS, HlP⟩
  unfold repRowArr
  icases HlS with ⟨%slS, #HslS, HlSs⟩
  icases HlP with ⟨%slP, #HslP, HlPs⟩
  icases ownCmds_open _ _ _ $$ Hcs with ⟨%vs, Hcs, %Hvslen, Hcms⟩
  ihave %Hcslen := ownSlice_len _ _ _ $$ Hcs
  unfold repConf repMsk
  icases Hconf with ⟨%cfs, %cms, #Hcfs, #Hcms', %Hcmlen, Hrows⟩
  icases Hmsk with ⟨%mm, %gm, #Hmm, Hgm, %Hgmeq⟩
  have hq' : toN q < nR := by have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  obtain ⟨mq, Hmq⟩ : ∃ mq, cms[toN q]? = some mq :=
    ⟨cms[toN q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  icases bigSepL_set_acc' Hmq $$ Hrows with ⟨Hrow, Hrclose⟩
  wp_auto
  ihave HI : (∃ k : w64,
      "Hi" ∷ i_ptr ↦ k ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ cmds.length⌝ ∗
      "Hrow" ∷ ownConflictRow mq
        ((updateConflicts σ (cmds.take (sint.nat k)) (toN q) n seq).conflicts (toN q)) ∗
      "Hgm" ∷ (∃ g : GMap w64 w32, mm ↦$ g ∗ ⌜∀ key, g.lookup key =
        (updateConflicts σ (cmds.take (sint.nat k)) (toN q) n seq).maxSeqPerKey key⌝) ∗
      "HlSs" ∷ slS ↦* ((List.range nR).map
        (updateConflicts σ (cmds.take (sint.nat k)) (toN q) n seq).lastScan) ∗
      "HlPs" ∷ slP ↦* ((List.range nR).map
        (updateConflicts σ (cmds.take (sint.nat k)) (toN q) n seq).lastPut) :
      IProp GF) $$ [«i» Hrow Hgm HlSs HlPs]
  · iexists W64 0; iframe «i»
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    rw [show updateConflicts σ [] (toN q) n seq = σ from rfl]
    isplitr
    · ipureintro; constructor <;> word
    iframe Hrow HlSs HlPs
    iexists gm; iframe Hgm; ipureintro; exact Hgmeq
  irename «instance» => Hinstance
  wp_for HI
  wp_if_destruct
  · -- an iteration
    have hkl : sint.nat k < cmds.length := by have := Hcslen.1; rw [← Hvslen]; word
    obtain ⟨c, hc⟩ : ∃ c, cmds[sint.nat k]? = some c :=
      ⟨cmds[sint.nat k], List.getElem?_eq_getElem hkl⟩
    obtain ⟨v, hv⟩ : ∃ v, vs[sint.nat k]? = some v :=
      ⟨vs[sint.nat k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    icases Hcms with #Hcms
    ihave ⟨%c', %hc', #Hok⟩ := BigSepL.bigSepL_lookup hv $$ Hcms
    rw [hc] at hc'; cases hc'
    unfold cmdOk
    icases Hok with ⟨%Hokp, #Hokv⟩
    icases ownSlice_elem_acc (sint.Z k) v cs dq vs Hk.1 hv $$ Hcs with ⟨Hv, Hcsc⟩
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z cs.len := ⟨Hk.1, by have := Hcslen.1; word⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    ihave %Hvnn := typedPointsto_not_null _ _ _ $$ Hv
    iStructNamed Hv
    wp_auto
    ihave %Hcmlen' := ownSlice_len _ _ _ $$ Hcms'
    have eq : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
    have h4 : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z cfs.len := by
      have := hq.1; have := hq.2; have := Hcmlen'.1; rw [Hcmlen] at this
      simp only [toN, zz, nR] at *; constructor <;> word
    simp only [h4, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index cfs _ cms _ mq h4.1 $$ [$Hcms'] as -
    · ipureintro; rw [eq]; exact Hmq
    rw [Hokp.2, Hokp.1]
    have hkk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
      have := Hcslen.1; have := Hk.1; unfold sint.nat at *; word
    -- the conflicts map's entry
    wp_join iprop(ownConflictRow mq
          ((updateConflicts σ (List.take (sint.nat k + 1) cmds) (toN q) n seq).conflicts (toN q)) ∗
        r_ptr ↦ r ∗ replica_ptr ↦ q ∗ cmds_ptr ↦ cs ∗
        i_ptr ↦ k ∗ instance_ptr ↦ n ∗
        (sliceIndexRef state.Command (sint.Z k) cs).[state.Command, go!"Op"] ↦{dq} c.op ∗
        (sliceIndexRef state.Command (sint.Z k) cs).[state.Command, go!"K"] ↦{dq} c.key)
      at next with [Hrow r replica cmds Hi Hinstance Op K]
      as ⟨Hrow, r, replica, cmds, Hi, Hinstance, Op, K⟩
    · rcases hp : (updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq).conflicts (toN q)
        c.key with _ | pr
      · -- absent
        icases conflictRow_absent _ _ _ hp $$ Hrow with ⟨%g, Hm, %Hgl, Hrclose2⟩
        wp_apply wp_map_lookup2 $$ [$Hm] as Hm
        rw [show (g !! c.key) = none from Hgl]
        cleanup_bool_decide
        simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
        wp_auto
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_auto
        simp only [h4, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index cfs _ cms _ mq h4.1 $$ [$Hcms'] as -
        · ipureintro; rw [eq]; exact Hmq
        wp_apply wp_mapInsert $$ [$Hm] as Hm
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_if_destruct
        · -- GET: `lastWrite` stays -1
          have hpair : ucPair (updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq) (toN q)
              n c = ⟨n, W32 (-1)⟩ := by
            unfold ucPair; rw [hp]; simp [opGET, Hif]
          ihave Hrow := Hrclose2 $$ %«$r0_ptr» %(⟨n, W32 (-1)⟩ : InstPair) Hm «$r0»
          rw [← hpair, ← uc_take_succ_conf _ _ _ _ _ _ _ hc]
          wp_join_done
        · -- not GET: `lastWrite = instance`
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_auto
          simp only [h4, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index cfs _ cms _ mq h4.1 $$ [$Hcms'] as -
          · ipureintro; rw [eq]; exact Hmq
          wp_apply wp_map_lookup1 $$ [$Hm] as Hm
          have hpair : ucPair (updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq) (toN q)
              n c = ⟨n, n⟩ := by
            unfold ucPair; rw [hp]; simp only; rw [if_pos (show c.op ≠ opGET from Hif)]
          ihave Hrow := Hrclose2 $$ %«$r0_ptr» %(⟨n, n⟩ : InstPair) Hm «$r0»
          rw [← hpair, ← uc_take_succ_conf _ _ _ _ _ _ _ hc]
          wp_join_done
      · -- present
        icases conflictRow_present _ _ _ _ hp $$ Hrow with ⟨%g, %l, Hm, %Hgl, Hl, Hrclose2⟩
        wp_apply wp_map_lookup2 $$ [$Hm] as Hm
        rw [show (g !! c.key) = some l from Hgl]
        cleanup_bool_decide
        simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
        wp_auto
        wp_if_destruct
        focus
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_auto
          simp only [h4, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index cfs _ cms _ mq h4.1 $$ [$Hcms'] as -
          · ipureintro; rw [eq]; exact Hmq
          wp_apply wp_map_lookup1 $$ [$Hm] as Hm
          rw [show g !! c.key = some l from Hgl]
          simp only [Option.getD_some]
          wp_auto
          ihave Hl : l ↦ epaxos.InstPair.mk (if pr.last.slt n then n else pr.last) pr.lastWrite $$ [Hl]
          · rw [if_pos ((slt_iff _ _).mpr Hif)]; iexact Hl
        rotate_left
        focus
          ihave Hl : l ↦ epaxos.InstPair.mk (if pr.last.slt n then n else pr.last) pr.lastWrite $$ [Hl]
          · rw [if_neg (fun h => Hif ((slt_iff _ _).mp h))]; iexact Hl
        all_goals
          wp_if_destruct
          focus
            have Hlw := Hif
            simp only [hb, _root_.and_self, ↓reduceIte]
            wp_auto
            try rw [Hokp.1]
            wp_if_destruct
            focus
              ihave Hl : l ↦ epaxos.InstPair.mk (if pr.last.slt n then n else pr.last) (if pr.lastWrite.slt n ∧ c.op ≠ opGET then n else pr.lastWrite) $$ [Hl]
              · rw [if_neg (show ¬(pr.lastWrite.slt n = true ∧ c.op ≠ opGET) from
                  fun h => h.2 (by unfold opGET; exact Hif))]; iexact Hl
            rotate_left
            focus
              simp only [hb, _root_.and_self, ↓reduceIte]
              wp_auto
              simp only [h4, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index cfs _ cms _ mq h4.1 $$ [$Hcms'] as -
              · ipureintro; rw [eq]; exact Hmq
              wp_apply wp_map_lookup1 $$ [$Hm] as Hm
              rw [show g !! c.key = some l from Hgl]
              simp only [Option.getD_some]
              wp_auto
              ihave Hl : l ↦ epaxos.InstPair.mk (if pr.last.slt n then n else pr.last) (if pr.lastWrite.slt n ∧ c.op ≠ opGET then n else pr.lastWrite) $$ [Hl]
              · rw [if_pos (show pr.lastWrite.slt n = true ∧ c.op ≠ opGET from
                  ⟨(slt_iff _ _).mpr Hlw, by unfold opGET; exact Hif⟩)]; iexact Hl
          rotate_right
          focus
            ihave Hl : l ↦ epaxos.InstPair.mk (if pr.last.slt n then n else pr.last) (if pr.lastWrite.slt n ∧ c.op ≠ opGET then n else pr.lastWrite) $$ [Hl]
            · rw [if_neg (show ¬(pr.lastWrite.slt n = true ∧ c.op ≠ opGET) from
                fun h => Hif ((slt_iff _ _).mp h.1))]; iexact Hl
          all_goals
            have hpair : ucPair (updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq)
                (toN q) n c = ⟨(if pr.last.slt n then n else pr.last), (if pr.lastWrite.slt n ∧ c.op ≠ opGET then n else pr.lastWrite)⟩ := by
              unfold ucPair; rw [hp]
            ihave Hrow := Hrclose2 $$ %(⟨(if pr.last.slt n then n else pr.last), (if pr.lastWrite.slt n ∧ c.op ≠ opGET then n else pr.lastWrite)⟩ : InstPair) Hm [Hl]
            · iexact Hl
            rw [← hpair, ← uc_take_succ_conf _ _ _ _ _ _ _ hc]
            wp_join_done
    -- `lastScan` (fix S1)
    have hqq : (sint.Z (W64 (sint.Z q))).toNat = toN q := by rw [eq]; rfl
    ihave %HlSlen := ownSlice_len _ _ _ $$ HlSs
    ihave %HlPlen := ownSlice_len _ _ _ $$ HlPs
    have hbS : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z slS.len := by
      have := hq.1; have := hq.2; have := HlSlen.1
      simp only [List.length_map, List.length_range] at this
      simp only [toN, zz, nR] at *; constructor <;> word
    have hbP : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z slP.len := by
      have := hq.1; have := hq.2; have := HlPlen.1
      simp only [List.length_map, List.length_range] at this
      simp only [toN, zz, nR] at *; constructor <;> word
    wp_join iprop(slS ↦* ((List.range nR).map
          (ucScan (updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq) (toN q) n c)) ∗
        r_ptr ↦ r ∗ replica_ptr ↦ q ∗ cmds_ptr ↦ cs ∗
        i_ptr ↦ k ∗ instance_ptr ↦ n ∗
        (sliceIndexRef state.Command (sint.Z k) cs).[state.Command, go!"Op"] ↦{dq} c.op)
      at next with [HlSs r replica cmds Hi Hinstance Op]
      as ⟨HlSs, r, replica, cmds, Hi, Hinstance, Op⟩
    · simp only [hb, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_if_destruct
      · -- SCAN
        have hs : c.op = opSCAN := by unfold opSCAN; simpa using Hif
        simp only [hbS, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index slS _ _ _
          ((updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq).lastScan (toN q)) hbS.1
          $$ [$HlSs] as HlSs
        · ipureintro; rw [hqq]; simp [hq']
        wp_if_destruct
        · simp only [hbS, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index $$ [$HlSs] as HlSs
          · ipureintro; refine ⟨hbS.1, ?_⟩
            have := hq.1; have := hq.2
            simp only [List.length_map, List.length_range, toN, zz, nR] at *; word
          wp_join_done
          unfold ucScan
          rw [if_pos ⟨hs, (slt_iff _ _).mpr Hif⟩, map_range_upd _ _ _ _ hq', ← hqq]
          iframe
        · wp_join_done
          unfold ucScan
          rw [if_neg (fun h => Hif ((slt_iff _ _).mp h.2))]
          iframe
      · have hs : ¬ c.op = opSCAN := by unfold opSCAN; simpa using Hif
        wp_join_done
        unfold ucScan
        rw [if_neg (fun h => hs h.1)]
        iframe
    -- `lastPut` (fix S1)
    wp_join iprop(slP ↦* ((List.range nR).map
          (ucPut (updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq) (toN q) n c)) ∗
        r_ptr ↦ r ∗ replica_ptr ↦ q ∗ cmds_ptr ↦ cs ∗
        i_ptr ↦ k ∗ instance_ptr ↦ n ∗
        (sliceIndexRef state.Command (sint.Z k) cs).[state.Command, go!"Op"] ↦{dq} c.op)
      at next with [HlPs r replica cmds Hi Hinstance Op]
      as ⟨HlPs, r, replica, cmds, Hi, Hinstance, Op⟩
    · simp only [hb, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_if_destruct
      · -- PUT
        have hs : c.op = opPUT := by unfold opPUT; simpa using Hif
        simp only [hbP, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index slP _ _ _
          ((updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq).lastPut (toN q)) hbP.1
          $$ [$HlPs] as HlPs
        · ipureintro; rw [hqq]; simp [hq']
        wp_if_destruct
        · simp only [hbP, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index $$ [$HlPs] as HlPs
          · ipureintro; refine ⟨hbP.1, ?_⟩
            have := hq.1; have := hq.2
            simp only [List.length_map, List.length_range, toN, zz, nR] at *; word
          wp_join_done
          unfold ucPut
          rw [if_pos ⟨hs, (slt_iff _ _).mpr Hif⟩, map_range_upd _ _ _ _ hq', ← hqq]
          iframe
        · wp_join_done
          unfold ucPut
          rw [if_neg (fun h => Hif ((slt_iff _ _).mp h.2))]
          iframe
      · have hs : ¬ c.op = opPUT := by unfold opPUT; simpa using Hif
        wp_join_done
        unfold ucPut
        rw [if_neg (fun h => hs h.1)]
        iframe
    -- `maxSeqPerKey`
    icases Hgm with ⟨%gm', Hgm, %Hgmeq'⟩
    try simp only [hb, _root_.and_self, ↓reduceIte]
    try wp_auto
    wp_apply wp_map_lookup2 $$ [$Hgm] as Hgm
    rw [show gm' !! c.key = _ from Hgmeq' c.key]
    rcases hms : (updateConflicts σ (List.take (sint.nat k) cmds) (toN q) n seq).maxSeqPerKey
      c.key with _ | ms
    · cleanup_bool_decide
      simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
      wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_apply wp_mapInsert $$ [$Hgm] as Hgm
      ihave Hv : sliceIndexRef state.Command (sint.Z k) cs ↦{dq} v $$ [Op K V]
      · iapply typedPointsto_combine _ _ _ Hvnn
        simp only [TypedPointsto.typedPointstoDef]
        rw [← Hokp.2]
        try rw [← Hokp.1]
        iframe Op K V
      ihave Hcs := Hcsc $$ Hv
      rw [list_set_lookup_self _ _ _ hv]
      wp_for_post
      iframe
      iframe Hcms
      iexists k + W64 1
      rw [hkk1, uc_take_succ_msk _ _ _ _ _ _ _ hc, uc_take_succ_scan _ _ _ _ _ _ _ hc,
        uc_take_succ_put _ _ _ _ _ _ _ hc]
      iframe
      isplitr
      · ipureintro; have := Hcslen.1; have := Hk.1; unfold sint.nat at *; constructor <;> word
      iexists <[c.key := seq]> gm'; iframe; ipureintro
      rw [ucSeq_none _ _ _ hms]; exact msk_insert _ _ Hgmeq' _ _
    · cleanup_bool_decide
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      wp_auto
      wp_if_destruct
      · simp only [hb, _root_.and_self, ↓reduceIte]
        wp_auto
        wp_apply wp_mapInsert $$ [$Hgm] as Hgm
        ihave Hv : sliceIndexRef state.Command (sint.Z k) cs ↦{dq} v $$ [Op K V]
        · iapply typedPointsto_combine _ _ _ Hvnn
          simp only [TypedPointsto.typedPointstoDef]
          rw [← Hokp.2]
          try rw [← Hokp.1]
          iframe Op K V
        ihave Hcs := Hcsc $$ Hv
        rw [list_set_lookup_self _ _ _ hv]
        wp_for_post
        iframe
        iframe Hcms
        iexists k + W64 1
        rw [hkk1, uc_take_succ_msk _ _ _ _ _ _ _ hc, uc_take_succ_scan _ _ _ _ _ _ _ hc,
        uc_take_succ_put _ _ _ _ _ _ _ hc]
        iframe
        isplitr
        · ipureintro; have := Hcslen.1; have := Hk.1; unfold sint.nat at *; constructor <;> word
        iexists <[c.key := seq]> gm'; iframe; ipureintro
        rw [ucSeq_some _ _ _ _ hms, if_pos Hif]; exact msk_insert _ _ Hgmeq' _ _
      · ihave Hv : sliceIndexRef state.Command (sint.Z k) cs ↦{dq} v $$ [Op K V]
        · iapply typedPointsto_combine _ _ _ Hvnn
          simp only [TypedPointsto.typedPointstoDef]
          rw [← Hokp.2]
          try rw [← Hokp.1]
          iframe Op K V
        ihave Hcs := Hcsc $$ Hv
        rw [list_set_lookup_self _ _ _ hv]
        wp_for_post
        iframe
        iframe Hcms
        iexists k + W64 1
        rw [hkk1, uc_take_succ_msk _ _ _ _ _ _ _ hc, uc_take_succ_scan _ _ _ _ _ _ _ hc,
        uc_take_succ_put _ _ _ _ _ _ _ hc]
        iframe
        isplitr
        · ipureintro; have := Hcslen.1; have := Hk.1; unfold sint.nat at *; constructor <;> word
        iexists gm'; iframe; ipureintro
        rw [ucSeq_some _ _ _ _ hms, if_neg Hif]; intro key; rw [Hgmeq']; exact upd_self_some _ _ _ hms key
  · -- the loop's end
    have hk : sint.nat k = cmds.length := by
      have := Hcslen.1; have := Hk.2; rw [← Hvslen]; word
    rw [hk, List.take_length]
    icases Hgm with ⟨%g, Hgm, %Hgeq⟩
    ihave Hrows := Hrclose $$ %(fun q' m => ownConflictRow m
      ((updateConflicts σ cmds (toN q) n seq).conflicts q')) %mq [] Hrow
    · ipureintro; intro q' hq'q; funext m
      simp only [updateConflicts_other_row _ _ _ _ _ _ hq'q]
    have hset : cms.set (toN q) mq = cms := by
      have := List.getElem?_eq_some_iff.mp Hmq
      rw [← this.2]; exact List.set_getElem_self this.1
    rw [hset]
    iapply HΦ
    isplitl [Hcs Hcms]
    · iapply ownCmds_close _ _ _ vs; iframe Hcs Hcms; ipureintro; exact Hvslen
    isplitl [Hrows]
    · iexists cfs, cms; iframe Hcfs Hcms' Hrows; ipureintro; exact Hcmlen
    isplitl [Hgm]
    · iexists mm, g; iframe Hmm Hgm; ipureintro; exact Hgeq
    isplitl [HlSs]
    · iexists slS; isplitr
      · iexact HslS
      · iexact HlSs
    · iexists slP; isplitr
      · iexact HslP
      · iexact HlPs

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
