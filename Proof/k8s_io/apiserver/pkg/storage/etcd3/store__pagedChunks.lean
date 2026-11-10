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
    · sorry
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
    sorry

end proof

end k8s
end EtcdGrove
end Perennial
