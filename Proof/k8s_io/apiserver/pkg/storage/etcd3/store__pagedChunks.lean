/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__pagedChunks.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__pagedChunks
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getList
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__listReadError

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem pageKvsL_snd_le (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (l : Nat) :
    (pageKvsL s kp recur st l).2 ≤ s.kvs.length := by
  unfold pageKvsL; exact List.length_filter_le _ _

theorem pageKvsL_fst_le (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (l : Nat) :
    (pageKvsL s kp recur st l).1.length ≤ (pageKvsL s kp recur st l).2 := by
  unfold pageKvsL
  by_cases hl : l = 0
  · simp [hl]
  · simp only [hl, ↓reduceIte, List.length_take]; omega

theorem pageKvsL_more (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (l : Nat)
    (h : (pageKvsL s kp recur st l).1.length < (pageKvsL s kp recur st l).2) :
    (pageKvsL s kp recur st l).1 ≠ [] := by
  unfold pageKvsL at h ⊢
  by_cases hl : l = 0
  · simp [hl] at h
  · simp only [hl, ↓reduceIte, List.length_take] at h ⊢
    intro he
    have := congrArg List.length he
    simp only [List.length_take, List.length_nil] at this
    omega

theorem pageKvsL_mem (s : KVStore) (kp : GoString) (recur : Bool) (st : GoString) (l : Nat)
    (kv : EtcdKv) (h : kv ∈ (pageKvsL s kp recur st l).1) : kv ∈ s.kvs := by
  unfold pageKvsL at h
  by_cases hl : l = 0
  · simp only [hl, ↓reduceIte] at h; exact (List.mem_filter.1 h).1
  · simp only [hl, ↓reduceIte] at h; exact (List.mem_filter.1 (List.mem_of_mem_take h)).1

theorem pageKvsL_key_nomore (s : KVStore) (kp : GoString) :
    ¬ (pageKvsL s kp false kp 1).1.length < (pageKvsL s kp false kp 1).2 := by
  rw [pageKvsL_key]; exact Nat.lt_irrefl _

theorem limN_W64 (n : Nat) (h : n < 2 ^ 63) : limN (W64 (n : Int)) = n := by
  unfold limN
  split <;> word

theorem pagesL_succ (s : KVStore) (kp : GoString) (recur : Bool) (lim0 i : Nat) :
    pagesL s kp recur lim0 (i + 1) =
      ((((pageKvsL s kp recur (pagesL s kp recur lim0 i).1
          (if recur then (pagesL s kp recur lim0 i).2 else 1)).1.getLast?.map EtcdKv.key).getD
          (pagesL s kp recur lim0 i).1) ++ [W8 0],
        if (pagesL s kp recur lim0 i).2 < 10000 then min (2 * (pagesL s kp recur lim0 i).2) 10000
        else (pagesL s kp recur lim0 i).2) := rfl

/-- The iterator's state before page `i ≥ 1` (pure): the first page's state `σ` and revision `R`,
the limit and continue key of page `i` (`pagesL`). -/
def pageInv (kp : GoString) (recur : Bool) (rev0 lim0 : w64) (σ : KVState) (R lm : w64)
    (ck : GoString) (i : Nat) : Prop :=
  R = (if uint.Z rev0 = 0 then W64 (σ.rev : Int) else rev0) ∧ 0 < sint.Z R ∧
    uint.nat R ≤ σ.rev ∧ σ.rev + 1 < 2 ^ 63 ∧ recur = true ∧
    ck = (pagesL (σ.at (uint.nat R)) kp recur (limN lim0) i).1 ∧ ck ≠ [] ∧
    ck.length ≤ opKeyMax ∧
    lm = W64 ((pagesL (σ.at (uint.nat R)) kp recur (limN lim0) i).2 : Int) ∧
    (pagesL (σ.at (uint.nat R)) kp recur (limN lim0) i).2 ≤ max (limN lim0) 10000

theorem store.pagedChunks.wp_proof
    (wp_getList : store.getList.spec (GF := GF) (hG := hG))
    (wp_listReadError : store.listReadError.spec (GF := GF) (hG := hG)) :
    store.pagedChunks.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd kp opts rev0 lim0 Q P hkp hrev hlim hcont hrk hQ hP
  wp_start as ⟨#Hst, #Hctx, #Hce, %htb⟩
  (try wp_auto)
  iapply HΦ
  iunfold pagesOk
  iintro %y %J %Φ' Htt HQ #HP HJ #Hy #Herr Hend
  wp_auto
  ihave HI : (∃ (i : Nat) (wr lm : w64) (ck : GoString) (o : Option (KVState × w64)),
      "withRev" ∷ withRev_ptr ↦ wr ∗ "limit" ∷ limit_ptr ↦ lm ∗
      "continueKey" ∷ continueKey_ptr ↦ ck ∗ "Htt" ∷ threadTok ∗ "HJ" ∷ J o i ∗
      "Hi" ∷ (if i = 0 then iprop(⌜o = none ∧ wr = rev0 ∧ lm = lim0 ∧ ck = []⌝ ∗
          (∀ R, |==> □ [∧list] x ∈ c.ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)))
        else iprop(∃ (σ : KVState) (R : w64), □ Q (W64 (σ.rev : Int)) σ ∗
          ⌜o = some (σ, R) ∧ wr = R ∧ pageInv kp opts.Recursive' rev0 lim0 σ R lm ck i⌝)) :
      IProp GF) $$ [withRev limit continueKey Htt HJ HQ]
  · iexists 0, rev0, lim0, [], none
    iframe withRev limit continueKey Htt HJ
    simp only [↓reduceIte]
    isplitr
    · ipureintro; simp
    iexact HQ
  wp_for HI
  (try simp only [_root_.decide_true, ↓reduceIte])
  cases i with
  | zero =>
    simp only [↓reduceIte]
    icases Hi with ⟨%Hi0, HQ⟩
    obtain ⟨rfl, hwr, hlm, rfl⟩ := Hi0
    subst wr lm
    (try wp_auto)
    wp_apply (wp_getList Obj sp c ci cd kp opts.Recursive'
        (go_etcd_io.etcd.client.v3.kubernetes.ListOptions.mk rev0 lim0 []) Q hkp (by simp) hrev hlim
        (fun _ => rfl)) $$ [Htt HQ] as %resp %gerr ⟨Htt, Hres⟩
    · iframe # Htt
      isplitr
      · ipureintro; exact htb
      iexact HQ
    (try wp_auto)
    icases Hres with (⟨%Hge, %σ, #HQσ, %Hrd, Hresp⟩ | ⟨%Hge, #Herr0⟩)
    · subst Hge
      ihave %Hwf := (hQ _ σ) $$ HQσ
      obtain ⟨⟨-, -, -, hσb⟩, hwh, hks⟩ := Hwf
      change σ.rev + 1 < 2 ^ 63 at hσb
      iunfold listRespIs at Hresp
      icases Hresp with ⟨%Hrc, %ps, Hkvs, #Hps⟩
      ihave %Hpsl := BigSepL2.bigSepL2_length $$ Hps
      ihave %Hkl := ownSlice_len $$ Hkvs
      have hrr : σ.readRev rev0 =
          uint.nat (if uint.Z rev0 = 0 then W64 (σ.rev : Int) else rev0) := by
        unfold KVState.readRev
        split <;> split <;> word
      have hRle : uint.nat (if uint.Z rev0 = 0 then W64 (σ.rev : Int) else rev0) ≤ σ.rev := by
        rw [← hrr]; exact Hrd
      rw [hrr] at Hpsl Hrc
      rw [hrr]
      generalize hR0 : (if uint.Z rev0 = 0 then W64 (σ.rev : Int) else rev0) = R0 at Hpsl Hrc hRle
      have hpg2 := (hks (uint.nat R0) hRle).1
      have hpg2' := pageKvsL_snd_le (σ.at (uint.nat R0)) kp opts.Recursive' kp
        (if opts.Recursive' = true then limN lim0 else 1)
      have hpg1 := pageKvsL_fst_le (σ.at (uint.nat R0)) kp opts.Recursive' kp
        (if opts.Recursive' = true then limN lim0 else 1)
      (try wp_auto)
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ withRev_ptr ↦ R0 ∗
          getResp_ptr ↦ resp))) $$ [withRev getResp]
      · by_cases h0 : rev0 = W64 0
        · rw [show decide (rev0 = W64 0) = true from decide_eq_true h0]
          (try wp_auto)
          iframe getResp
          rw [Hrc.1, ← hR0, if_pos (by rw [h0]; rfl)]
          iframe withRev; ipureintro; rfl
        · rw [show decide (rev0 = W64 0) = false from decide_eq_false h0]
          (try wp_auto)
          iframe getResp
          have : ¬ uint.Z rev0 = 0 := by intro h; apply h0; word
          rw [← hR0, if_neg this]
          iframe withRev; ipureintro; rfl
      iintro %v ⟨%hv, withRev, getResp⟩
      subst hv
      (try wp_auto)
      generalize hpgdef : pageKvsL (σ.at (uint.nat R0)) kp opts.Recursive' kp
        (if opts.Recursive' = true then limN lim0 else 1) = pg at Hpsl Hrc hpg1 hpg2'
      have hlen : sint.nat resp.Kvs'.len = pg.1.length := by rw [← Hkl.1]; exact Hpsl
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
          continueKey_ptr ↦ (if pg.1 = [] then [] else
            (pagesL (σ.at (uint.nat R0)) kp opts.Recursive' (limN lim0) 1).1) ∗
          getResp_ptr ↦ resp ∗ resp.Kvs' ↦* ps))) $$ [continueKey getResp Hkvs]
      · by_cases hne : pg.1 = []
        · have hl0' : sint.Z resp.Kvs'.len = 0 := by rw [hne] at hlen; simp at hlen; word
          rw [show decide (sint.Z (W64 0) < sint.Z resp.Kvs'.len) = false by
            simp only [hl0']; decide]
          (try wp_auto)
          rw [if_pos hne]
          iframe; ipureintro; rfl
        · have hlp : 0 < sint.Z resp.Kvs'.len := by
            have := List.length_pos_iff.2 hne; word
          rw [show decide (sint.Z (W64 0) < sint.Z resp.Kvs'.len) = true by
            simp only [decide_eq_true_eq]; word]
          (try wp_auto)
          have hpsn : 0 < ps.length := by rw [Hpsl]; exact List.length_pos_iff.2 hne
          obtain ⟨plast, hpl⟩ : ∃ p, ps[ps.length - 1]? = some p :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨kvl, hkvl⟩ : ∃ kv, pg.1[ps.length - 1]? = some kv :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          ihave #Hkv := BigSepL2.bigSepL2_lookup hpl hkvl $$ Hps
          have hi : (sint.Z (resp.Kvs'.len - W64 1)).toNat = ps.length - 1 := by word
          rw [if_pos (by word)]
          wp_apply (wp_load_slice_index resp.Kvs' _ ps (DFrac.own 1) plast (by word)) $$ [Hkvs]
            as Hkvs
          · iframe Hkvs; ipureintro; rw [hi]; exact hpl
          iunfold txn.kvIs at Hkv
          icases Hkv with ⟨%keySl, %valSl, #Hk, #Hksl, -, -, -, -, -, -, %Hnn⟩
          (try wp_auto)
          wp_apply (wp_bytes_to_string keySl kvl.key) $$ [$Hksl] as -
          (try wp_auto)
          have hlast : (pagesL (σ.at (uint.nat R0)) kp opts.Recursive' (limN lim0) 1).1 =
              kvl.key ++ [W8 0] := by
            simp only [pagesL, hpgdef]
            rw [List.getLast?_eq_getElem?, ← Hpsl, hkvl]; rfl
          rw [if_neg hne, hlast]
          iframe
          ipureintro; rfl
      iintro %v ⟨%hv, continueKey, getResp, Hkvs⟩
      subst hv
      (try wp_auto)
      ipersist revision
      have hhm : decide (sint.Z resp.Kvs'.len < sint.Z resp.Count') =
          decide (pg.1.length < pg.2) := by
        rw [Hrc.2]; apply decide_eq_decide.2; constructor <;> intro h <;> word
      rw [hhm]
      wp_bind (App (App (Val #y) _) _)
      iapply (wp_wand (Φ := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗
          if b then J (some (σ, R0)) (0 + 1) else (threadTok -∗ Φ' #()))))
        $$ [HJ Hkvs]
      · iapply Hy $$ %σ %R0 %0
          %(k8s_io.apiserver.pkg.storage.etcd3.listChunk.mk resp.Kvs' revision_ptr resp.Count'
            (decide (pg.1.length < pg.2))) [HJ] [] [Hkvs]
        · simp only [↓reduceIte]; iexact HJ
        · simp only [↓reduceIte]
          iframe HQσ
          ipureintro; exact ⟨hR0.symm, hRle⟩
        · iunfold chunkIs
          simp only [pagesL, hpgdef]
          iframe revision
          isplitr
          · ipureintro; exact ⟨Hrc.2, trivial⟩
          iexists ps
          iframe Hkvs Hps
      iintro %v ⟨%b, %hv, HJ⟩
      subst hv
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        wp_for_post
        iapply HJ $$ Htt
      simp only [↓reduceIte]
      by_cases hm : ¬ pg.1.length < pg.2
      · rw [show decide (pg.1.length < pg.2) = false from decide_eq_false hm]
        (try wp_auto)
        wp_for_post
        iapply Hend $$ %σ %R0 %0 HJ [] Htt
        ipureintro
        simp only [pageMore, pagesL, hpgdef]
        exact decide_eq_false hm
      rw [Decidable.not_not] at hm
      rw [show decide (pg.1.length < pg.2) = true from decide_eq_true hm]
      (try wp_auto)
      have hl0 : limN lim0 = sint.nat lim0 := by unfold limN; split <;> word
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ limit_ptr ↦
          W64 ((if limN lim0 < 10000 then min (2 * limN lim0) 10000 else limN lim0 : Nat) : Int))))
        $$ [limit]
      · wp_if_destruct
        · (try wp_auto)
          rename_i h1
          wp_if_destruct
          · (try wp_auto)
            have e : W64 ((if limN lim0 < 10000 then min (2 * limN lim0) 10000 else limN lim0 : Nat) :
                Int) = W64 10000 := by
              rw [hl0, if_pos (by word), Nat.min_eq_right (by word)]; rfl
            rw [e]; iframe limit
          · (try wp_auto)
            have e : W64 ((if limN lim0 < 10000 then min (2 * limN lim0) 10000 else limN lim0 : Nat) :
                Int) = lim0 * W64 2 := by
              rw [hl0, if_pos (by word), Nat.min_eq_left (by word)]; word
            rw [e]; iframe limit
        · (try wp_auto)
          have e : W64 ((if limN lim0 < 10000 then min (2 * limN lim0) 10000 else limN lim0 : Nat) :
              Int) = lim0 := by
            rw [hl0, if_neg (by word)]; word
          rw [e]; iframe limit
      iintro %v ⟨%hv, limit⟩
      subst hv
      wp_for_post
      have hne : pg.1 ≠ [] := by rw [← hpgdef] at hm ⊢; exact pageKvsL_more _ _ _ _ _ hm
      have hmem : ∀ kv ∈ pg.1, kv ∈ (σ.at (uint.nat R0)).kvs := by
        intro kv h; rw [← hpgdef] at h; exact pageKvsL_mem _ _ _ _ _ kv h
      have hinv : pageInv kp opts.Recursive' rev0 lim0 σ R0
          (W64 ((if limN lim0 < 10000 then min (2 * limN lim0) 10000 else limN lim0 : Nat) : Int))
          (pagesL (σ.at (uint.nat R0)) kp opts.Recursive' (limN lim0) 1).1 1 := by
        obtain ⟨kl, hkl⟩ : ∃ kl, pg.1.getLast? = some kl := by
          cases h : pg.1.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
          | some kl => exact ⟨kl, rfl⟩
        have hklm : kl ∈ pg.1 := List.mem_of_getLast? hkl
        have hck : (pagesL (σ.at (uint.nat R0)) kp opts.Recursive' (limN lim0) 1).1 =
            kl.key ++ [W8 0] := by
          simp only [pagesL, hpgdef, hkl]; rfl
        unfold pageInv
        refine ⟨hR0.symm, ?_, hRle, hσb, ?_, rfl, ?_, ?_, ?_, ?_⟩
        · obtain ⟨kv0, hkv0⟩ := List.exists_mem_of_ne_nil _ hne
          have h1 := (hwh (uint.nat R0) hRle kv0 (hmem kv0 hkv0)).2
          rw [← hR0] at h1 ⊢
          split at h1 <;> split <;> word
        · cases hr : opts.Recursive'
          · exfalso
            rw [hr] at hpgdef
            apply pageKvsL_key_nomore (σ.at (uint.nat R0)) kp
            rw [show (if false = true then limN lim0 else 1) = 1 from rfl] at hpgdef
            rw [hpgdef]; exact hm
          · rfl
        · rw [hck]; simp
        · rw [hck]
          have := (hks (uint.nat R0) hRle).2 kl (hmem kl hklm)
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · rfl
        · simp only [pagesL]; by_cases h : limN lim0 < 10000 <;> simp only [h, ↓reduceIte] <;> omega
      rw [if_neg hne]
      iframe
      iexists 1, R0, _, _, some (σ, R0)
      iframe withRev limit continueKey Htt HJ
      simp only [Nat.one_ne_zero, ↓reduceIte]
      iexists σ, R0
      iframe HQσ
      ipureintro
      exact ⟨rfl, rfl, hinv⟩
    · -- the read failed
      cases gerr with
      | nil => exact absurd rfl Hge
      | ok gi =>
        (try wp_auto)
        rw [hcont]
        (try wp_auto)
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        (try wp_auto)
        wp_apply (wp_listReadError Obj sp c ci cd _ rev0 _ _ Q hrk) $$ [] as %e He
        · iframe #
        (try wp_auto)
        wp_bind (App (App (Val #y) _) _)
        iapply (wp_wand (Φ := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗ (threadTok -∗ Φ' #()))))
          $$ [HJ He]
        · iapply Herr $$ %none %0 %e HJ
          icases He with (⟨He, %σ, #HQσ, %Hlt⟩ | He)
          · ileft
            iframe He
            isplitr
            · ipureintro; rfl
            iexists σ
            iframe HQσ
            ipureintro; word
          · iright; iexact He
        iintro %v ⟨%b, %hv, Hfin⟩
        subst hv
        (try wp_auto)
        wp_for_post
        iapply Hfin
        iexact Htt
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    icases Hi with ⟨%σ, %R, #HQσ, %Hinv⟩
    obtain ⟨rfl, hwr, hR0, hRpos, hRle, hσb, hrec, hck, hckne, hckl, hlm, hlb⟩ := Hinv
    subst wr ck lm
    ihave %Hwf := (hQ _ σ) $$ HQσ
    obtain ⟨-, hwh, hks⟩ := Hwf
    generalize hL : pagesL (σ.at (uint.nat R)) kp opts.Recursive' (limN lim0) (n + 1) = L
      at hckne hckl hlb
    have hlimb : limN lim0 < 2 ^ 63 := by unfold limN; split <;> word
    have hLb : L.2 < 2 ^ 63 := by omega
    (try wp_auto)
    wp_apply (wp_getList Obj sp c ci cd kp opts.Recursive'
        (go_etcd_io.etcd.client.v3.kubernetes.ListOptions.mk R (W64 (L.2 : Int)) L.1)
        (fun _ => P σ) hkp hckl (by word) (by word) (fun h => absurd hrec (by rw [h]; decide)))
        $$ [Htt] as %resp %gerr ⟨Htt, Hres⟩
    · iframe # Htt
      isplitr
      · ipureintro; exact htb
      iintro %R'
      iapply HP $$ %(W64 (σ.rev : Int)) %σ HQσ
    (try wp_auto)
    icases Hres with (⟨%Hge, %σ', #HPσ, %Hrd, Hresp⟩ | ⟨%Hge, #Herr0⟩)
    · subst Hge
      ihave %Hh := (hP _ σ σ') $$ [HQσ HPσ]
      · iframe HQσ HPσ
      obtain ⟨hsh, hle'⟩ := Hh
      have hrr : σ'.readRev R = uint.nat R := by unfold KVState.readRev; split <;> word
      have hat : σ'.at (uint.nat R) = σ.at (uint.nat R) :=
        (kvSameHist_at σ σ' (uint.nat R) hsh hRle (by omega)).symm
      iunfold listRespIs at Hresp
      icases Hresp with ⟨%Hrc, %ps, Hkvs, #Hps⟩
      ihave %Hpsl := BigSepL2.bigSepL2_length $$ Hps
      ihave %Hkl := ownSlice_len $$ Hkvs
      rw [hrr, hat, if_neg hckne, limN_W64 _ hLb] at Hpsl Hrc
      rw [hrr, hat, if_neg hckne, limN_W64 _ hLb]
      have hpg2 := (hks (uint.nat R) hRle).1
      have hpg2' := pageKvsL_snd_le (σ.at (uint.nat R)) kp opts.Recursive' L.1
        (if opts.Recursive' = true then L.2 else 1)
      have hpg1 := pageKvsL_fst_le (σ.at (uint.nat R)) kp opts.Recursive' L.1
        (if opts.Recursive' = true then L.2 else 1)
      (try wp_auto)
      rw [show decide (R = W64 0) = false from decide_eq_false (by intro h; rw [h] at hRpos; simp at hRpos)]
      (try wp_auto)
      generalize hpgdef : pageKvsL (σ.at (uint.nat R)) kp opts.Recursive' L.1
        (if opts.Recursive' = true then L.2 else 1) = pg at Hpsl Hrc hpg1 hpg2'
      have hlen : sint.nat resp.Kvs'.len = pg.1.length := by rw [← Hkl.1]; exact Hpsl
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
          continueKey_ptr ↦ (if pg.1 = [] then L.1 else
            (pagesL (σ.at (uint.nat R)) kp opts.Recursive' (limN lim0) (n + 1 + 1)).1) ∗
          getResp_ptr ↦ resp ∗ resp.Kvs' ↦* ps))) $$ [continueKey getResp Hkvs]
      · by_cases hne : pg.1 = []
        · have hl0' : sint.Z resp.Kvs'.len = 0 := by rw [hne] at hlen; simp at hlen; word
          rw [show decide (sint.Z (W64 0) < sint.Z resp.Kvs'.len) = false by
            simp only [hl0']; decide]
          (try wp_auto)
          rw [if_pos hne]
          iframe; ipureintro; rfl
        · have hlp : 0 < sint.Z resp.Kvs'.len := by
            have := List.length_pos_iff.2 hne; word
          rw [show decide (sint.Z (W64 0) < sint.Z resp.Kvs'.len) = true by
            simp only [decide_eq_true_eq]; word]
          (try wp_auto)
          have hpsn : 0 < ps.length := by rw [Hpsl]; exact List.length_pos_iff.2 hne
          obtain ⟨plast, hpl⟩ : ∃ p, ps[ps.length - 1]? = some p :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          obtain ⟨kvl, hkvl⟩ : ∃ kv, pg.1[ps.length - 1]? = some kv :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          ihave #Hkv := BigSepL2.bigSepL2_lookup hpl hkvl $$ Hps
          have hi : (sint.Z (resp.Kvs'.len - W64 1)).toNat = ps.length - 1 := by word
          rw [if_pos (by word)]
          wp_apply (wp_load_slice_index resp.Kvs' _ ps (DFrac.own 1) plast (by word)) $$ [Hkvs]
            as Hkvs
          · iframe Hkvs; ipureintro; rw [hi]; exact hpl
          iunfold txn.kvIs at Hkv
          icases Hkv with ⟨%keySl, %valSl, #Hk, #Hksl, -, -, -, -, -, -, %Hnn⟩
          (try wp_auto)
          wp_apply (wp_bytes_to_string keySl kvl.key) $$ [$Hksl] as -
          (try wp_auto)
          have hlast : (pagesL (σ.at (uint.nat R)) kp opts.Recursive' (limN lim0) (n + 1 + 1)).1 =
              kvl.key ++ [W8 0] := by
            rw [pagesL_succ, hL]
            simp only [hpgdef]
            rw [List.getLast?_eq_getElem?, ← Hpsl, hkvl]; rfl
          rw [if_neg hne, hlast]
          iframe
          ipureintro; rfl
      iintro %v ⟨%hv, continueKey, getResp, Hkvs⟩
      subst hv
      (try wp_auto)
      ipersist revision
      have hhm : decide (sint.Z resp.Kvs'.len < sint.Z resp.Count') =
          decide (pg.1.length < pg.2) := by
        rw [Hrc.2]; apply decide_eq_decide.2; constructor <;> intro h <;> word
      rw [hhm]
      wp_bind (App (App (Val #y) _) _)
      iapply (wp_wand (Φ := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗
          if b then J (some (σ, R)) (n + 1 + 1) else (threadTok -∗ Φ' #()))))
        $$ [HJ Hkvs]
      · iapply Hy $$ %σ %R %(n + 1)
          %(k8s_io.apiserver.pkg.storage.etcd3.listChunk.mk resp.Kvs' revision_ptr resp.Count'
            (decide (pg.1.length < pg.2))) [HJ] [] [Hkvs]
        · simp only [Nat.succ_ne_zero, ↓reduceIte]; iexact HJ
        · simp only [Nat.succ_ne_zero, ↓reduceIte]; itrivial
        · iunfold chunkIs
          rw [hL]
          simp only [hpgdef]
          iframe revision
          isplitr
          · ipureintro; exact ⟨Hrc.2, trivial⟩
          iexists ps
          iframe Hkvs Hps
      iintro %v ⟨%b, %hv, HJ⟩
      subst hv
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        wp_for_post
        iapply HJ $$ Htt
      simp only [↓reduceIte]
      by_cases hm : ¬ pg.1.length < pg.2
      · rw [show decide (pg.1.length < pg.2) = false from decide_eq_false hm]
        (try wp_auto)
        wp_for_post
        iapply Hend $$ %σ %R %(n + 1) HJ [] Htt
        ipureintro
        simp only [pageMore, hL, hpgdef]
        exact decide_eq_false hm
      rw [Decidable.not_not] at hm
      rw [show decide (pg.1.length < pg.2) = true from decide_eq_true hm]
      (try wp_auto)
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ limit_ptr ↦
          W64 ((if L.2 < 10000 then min (2 * L.2) 10000 else L.2 : Nat) : Int))))
        $$ [limit]
      · wp_if_destruct
        · (try wp_auto)
          rename_i h1
          wp_if_destruct
          · (try wp_auto)
            have e : W64 ((if L.2 < 10000 then min (2 * L.2) 10000 else L.2 : Nat) :
                Int) = W64 10000 := by
              rw [if_pos (by word), Nat.min_eq_right (by word)]; rfl
            rw [e]; iframe limit
          · (try wp_auto)
            have e : W64 ((if L.2 < 10000 then min (2 * L.2) 10000 else L.2 : Nat) :
                Int) = W64 (L.2 : Int) * W64 2 := by
              rw [if_pos (by word), Nat.min_eq_left (by word)]; word
            rw [e]; iframe limit
        · (try wp_auto)
          have e : W64 ((if L.2 < 10000 then min (2 * L.2) 10000 else L.2 : Nat) :
              Int) = W64 (L.2 : Int) := by
            rw [if_neg (by word)]
          rw [e]; iframe limit
      iintro %v ⟨%hv, limit⟩
      subst hv
      wp_for_post
      have hne : pg.1 ≠ [] := by rw [← hpgdef] at hm ⊢; exact pageKvsL_more _ _ _ _ _ hm
      have hmem : ∀ kv ∈ pg.1, kv ∈ (σ.at (uint.nat R)).kvs := by
        intro kv h; rw [← hpgdef] at h; exact pageKvsL_mem _ _ _ _ _ kv h
      have hinv : pageInv kp opts.Recursive' rev0 lim0 σ R
          (W64 ((if L.2 < 10000 then min (2 * L.2) 10000 else L.2 : Nat) : Int))
          (pagesL (σ.at (uint.nat R)) kp opts.Recursive' (limN lim0) (n + 1 + 1)).1 (n + 1 + 1) := by
        obtain ⟨kl, hkl⟩ : ∃ kl, pg.1.getLast? = some kl := by
          cases h : pg.1.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
          | some kl => exact ⟨kl, rfl⟩
        have hklm : kl ∈ pg.1 := List.mem_of_getLast? hkl
        have hck : (pagesL (σ.at (uint.nat R)) kp opts.Recursive' (limN lim0) (n + 1 + 1)).1 =
            kl.key ++ [W8 0] := by
          rw [pagesL_succ, hL]; simp only [hpgdef, hkl]; rfl
        unfold pageInv
        refine ⟨hR0, hRpos, hRle, hσb, hrec, rfl, ?_, ?_, ?_, ?_⟩
        · rw [hck]; simp
        · rw [hck]
          have := (hks (uint.nat R) hRle).2 kl (hmem kl hklm)
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · rw [pagesL_succ, hL]
        · rw [pagesL_succ, hL]
          by_cases h : L.2 < 10000 <;> simp only [h, ↓reduceIte] <;> omega
      rw [if_neg hne]
      iframe
      iexists n + 1 + 1, R, _, _, some (σ, R)
      iframe withRev limit continueKey Htt HJ
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      iexists σ, R
      iframe HQσ
      ipureintro
      exact ⟨rfl, rfl, hinv⟩
    · -- the read failed
      cases gerr with
      | nil => exact absurd rfl Hge
      | ok gi =>
        (try wp_auto)
        rw [hcont]
        (try wp_auto)
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        (try wp_auto)
        wp_apply (wp_listReadError Obj sp c ci cd _ R _ _ (fun _ => P σ) hrk) $$ [] as %e He
        · iframe #
        (try wp_auto)
        wp_bind (App (App (Val #y) _) _)
        iapply (wp_wand (Φ := fun v => iprop(∃ b : Bool, ⌜v = #b⌝ ∗ (threadTok -∗ Φ' #()))))
          $$ [HJ He]
        · iapply Herr $$ %(some (σ, R)) %(n + 1) %e HJ
          icases He with (⟨-, %σ'', #HPσ, %Hlt⟩ | He)
          · ihave %Hh := (hP _ σ σ'') $$ [HQσ HPσ]
            · iframe HQσ HPσ
            exfalso
            obtain ⟨-, hle⟩ := Hh
            have : sint.nat R = uint.nat R := by word
            omega
          · iright; iexact He
        iintro %v ⟨%b, %hv, Hfin⟩
        subst hv
        (try wp_auto)
        wp_for_post
        iapply Hfin
        iexact Htt

end proof

end k8s
end EtcdGrove
end Perennial
