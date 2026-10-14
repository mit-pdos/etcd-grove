/-
Lemmas for `NewKV` and `Close` (`kv.go`): the wait group's `Add(2)` for the two goroutines `NewKV`
starts (they keep their own thread tokens), their `Done`, `Close`'s `Wait`, and the allocation of
the lease cache with the KV's part of its lock. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingWg_ctr_bound_owed {k d n : Nat} {T : Nat} (Hbound : T + leasingWgOwedMax ≤ 2 ^ 31)
    (Hk : k < T) (Hd : d + n ≤ leasingWgOwedMax) : k + d + n < 2 ^ 31 := by
  unfold leasingWgOwedMax at *; omega

/-- `lkv.wg.Add(2)` (`NewKV`'s, for the session monitor and `clearOldRevokes`, which keep their
own thread tokens): two owed capacities for two owed running tokens, with a fraction of the "open"
token. -/
theorem wp_leasingWg_Add2 (lkv : Loc) (γ : LeasingNames) (q : Qp)
    (Hbound : threadBound GF + leasingWgOwedMax ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗
        inv leasingWgN (leasingWgInv γ) ∗ ownToks γ.wc 2 ∗ leasingOpen γ q }}
      (App (Val (lkvWg lkv @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 2)))
    {{ RET #(); ownToks γ.wo 2 ∗ leasingOpen γ q }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hocap, Hopen⟩ HΦ
  iapply sync.WaitGroup.wp_Add (lkvWg lkv) (W64 2) γ.wg leasingWgWGN $$ [] [Hocap Hopen HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro leasingWg_mask
  iintro Hmask
  inext
  iunfold leasingWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, Hwgo, Hwt, Hrun, Hk, Hoauth, Hcap, Hcauth,
    %Hctr, %Hkd, Hwn⟩
  icases Hwn with (%Hw0 | ⟨-, Hop1⟩)
  rotate_left
  · iexfalso
    iapply leasingOpen_excl γ q $$ [$Hopen $Hop1]
  subst Hw0
  ihave Hcap' := ownToks_add_2 2 d γ.wc $$ [Hcap Hocap]
  · iframe
  icases persistent_entails_left (threadToks_lt (GF := GF) k) $$ Hk with ⟨Hk, %Hlt⟩
  icombine Hcauth Hcap' gives %Hd
  have hb := leasingWg_ctr_bound_owed (n := 2) Hbound Hlt Hd
  have h1 : sint.Z (W32 (sint.Z (W64 2))) = 2 := by decide
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have hle : sint.Z ctr + 2 ≤ 2 ^ 31 - 1 := by omega
  have hn : sint.nat (ctr + W32 (sint.Z (W64 2))) = sint.nat ctr + 2 := by
    rw [show W32 (sint.Z (W64 2)) = W32 2 from rfl]; word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hwt
  iintro Hwt Hwgo
  imod Hmask with -
  imod ownTokAuth_add 2 γ.wo d $$ Hoauth with ⟨Hoauth, Hotok⟩
  imod Hclose $$ [Hwgo Hwt Hrun Hk Hoauth Hcap' Hcauth] with -
  · inext
    unfold leasingWgInv
    iexists ctr + W32 (sint.Z (W64 2)), 0, k, d + 2
    rw [hn]
    iframe
    isplitr
    · ipureintro
      have : sint.Z (ctr + W32 (sint.Z (W64 2))) = sint.Z ctr + 2 := by
        rw [show W32 (sint.Z (W64 2)) = W32 2 from rfl]; word
      omega
    isplitr
    · ipureintro; omega
    ileft; ipureintro; rfl
  imodintro
  iapply HΦ
  iframe

/-- `lkv.wg.Done()`, with an owed running token (`NewKV`'s goroutines): the capacity it spent
comes back. -/
theorem wp_leasingWg_DoneOwed (lkv : Loc) (γ : LeasingNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗
        inv leasingWgN (leasingWgInv γ) ∗ leasingWgRunningOwed γ }}
      (App (Val (lkvWg lkv @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); ownToks γ.wc 1 }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hotok⟩ HΦ
  iapply sync.WaitGroup.wp_Done (lkvWg lkv) γ.wg leasingWgWGN $$ [] [Hotok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro leasingWg_mask
  iintro Hmask
  inext
  iunfold leasingWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, Hwgo, Hwt, Hrun, Hk, Hoauth, Hcap, Hcauth,
    %Hctr, %Hkd, Hwn⟩
  unfold leasingWgRunningOwed
  icombine Hoauth Hotok gives %Hle
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have h1 : 1 ≤ sint.Z ctr := by omega
  have hn : sint.nat (ctr - W32 1) = sint.nat ctr - 1 := by word
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  have hlt : sint.Z ctr < 2 ^ 31 := by word
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  icases ownToks_add_1 1 d' γ.wc $$ Hcap with ⟨Hcap, Hocap⟩
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.wo d' $$ Hoauth Hotok with Hoauth
  imod Hclose $$ [Hwgo Hwt Hrun Hk Hoauth Hcap Hcauth Hwn] with -
  · inext
    unfold leasingWgInv
    iexists ctr - W32 1, wn, k, d'
    rw [hn]
    iframe
    ipureintro
    omega
  imodintro
  iapply HΦ
  iexact Hocap

/-- `lkv.wg.Wait()`, by its registered waiter: returns once the counter is zero. -/
theorem wp_leasingWg_Wait (lkv : Loc) (γ : LeasingNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (lkvWg lkv) γ.wg leasingWgWGN ∗
        inv leasingWgN (leasingWgInv γ) ∗ sync.ownWaitGroupWaitToken γ.wg }}
      (App (Val (lkvWg lkv @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); sync.ownWaitGroupWaitToken γ.wg }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Htok⟩ HΦ
  iapply sync.WaitGroup.wp_Wait (lkvWg lkv) γ.wg leasingWgWGN $$ [Htok] [HΦ]
  · iframe #
    iframe
  iinv Hinv with >Hi Hclose
  · exact sync.wg_mask_ndot_ne nroot "leasingWgCounter" "leasingWaitGroup" (by decide)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold leasingWgInv at Hi
  icases Hi with ⟨%ctr, %wn, %k, %d, Hwgo, Hwt, Hrun, Hk, Hoauth, Hcap, Hcauth,
    %Hctr, %Hkd, Hwn⟩
  iexists ctr
  iframe Hwgo
  iintro %H0 Hwgo
  imod Hmask with -
  imod Hclose $$ [Hwgo Hwt Hrun Hk Hoauth Hcap Hcauth Hwn] with -
  · unfold leasingWgInv
    iexists ctr, wn, k, d
    iframe
    ipureintro; exact ⟨Hctr, Hkd⟩
  imodintro
  iintro Htok
  iapply HΦ $$ Htok

/-! ## The lease cache's allocation -/

/-- The lease cache's state when `NewKV` makes it: no entries map yet, the revocation map `rm`
(empty), no header, nothing frozen or installed. -/
def leaseCacheSt0 (rm : GoMap) : LeaseCacheSt :=
  { emap := map.nil, entries := ∅, rmap := rm, revokes := ∅, header := null,
    hm := ⟨W64 0, W64 0, W64 0, W64 0, W64 0⟩, frozen := [], installed := [] }

theorem leaseCacheSt0_wf (rm : GoMap) : LeaseCacheWf (leaseCacheSt0 rm) where
  li_inj := by intro k1 k2 e1 e2 h; simp [leaseCacheSt0] at h
  li_not_frozen := by intro k e h; simp [leaseCacheSt0] at h
  installed := by intro k li h; simp [leaseCacheSt0] at h
  entries_installed := by intro k e h; simp [leaseCacheSt0] at h
  li_ne := by intro k e h; simp [leaseCacheSt0] at h
  empty_if_nil := by intro _; rfl

/-- **The lease cache's allocation** (`NewKV`): from the `leases` field's fields as the literal
made them (the zero `RWMutex`, no entries map, the revocation map `rm`, empty, no header), the
lease cache's ghost state at `leaseCacheSt0 rm`, and the KV's part of the lock (half of `session`,
nil, and of `sessionc`, `sc`, a broadcast channel announcing `sessionReadyQ`; the log `[st0]`; the
session's readiness at `0`): the lease cache (`isLeaseCache`) and every reader slot. -/
theorem leasingCache_init (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (rm : GoMap)
    (sc : GoChan) :
    closedChInit (GF := GF) ∗
    structFieldRef leaseCache go!"mu" (lkvLeases lkv) ↦ (zero_val sync.RWMutex) ∗
    structFieldRef leaseCache go!"entries" (lkvLeases lkv) ↦ (map.nil : GoMap) ∗
    structFieldRef leaseCache go!"revokes" (lkvLeases lkv) ↦ rm ∗
    rm ↦$ (∅ : GMap GoString time.Time) ∗
    structFieldRef leaseCache go!"header" (lkvLeases lkv) ↦ (null : Loc) ∗
    ghostVar γ.lc.st 1 (leaseCacheSt0 rm) ∗ monoNatAuthOwn γ.lc.ready 1 0 ∗
    monoListAuthOwn γ.lc.inst 1 ([] : List (GoString × Loc)) ∗
    structFieldRef leasingKV go!"session" lkv ↦{DFrac.own (1 : Qp).half} (null : Loc) ∗
    structFieldRef leasingKV go!"sessionc" lkv ↦{DFrac.own (1 : Qp).half} sc ∗
    monoListAuthOwn γ.log 1 [leaseCacheSt0 rm] ∗ monoNatAuthOwn γ.sess 1 0 ∗ sessioncOk γ sc
    ={⊤}=∗ lkvCache lkv γ pfx ∗
      [∗list] _x ∈ List.replicate leasingMaxReaders (), lkvReader lkv γ pfx := by
  iintro ⟨#Hcl, Hmu, Hent, Hrv, Hrm, Hhdr, Hst, Hready, Hinst, Hs, Hsc, Hlog, Hsess, #Hsco⟩
  have h0 : (leaseCacheSt0 rm).readyN = 0 := by simp [LeaseCacheSt.readyN, leaseCacheSt0]
  imod sync.init_RWMutex (leaseCacheInv (lkvLeases lkv) γ.lc pfx (leasingX lkv γ)) (E := ⊤)
    (structFieldRef leaseCache go!"mu" (lkvLeases lkv)) $$ [Hent Hrv Hrm Hhdr Hst Hready Hinst Hs Hsc
      Hlog Hsess] Hmu with Hrds
  · inext
    unfold leaseCacheInv leaseCacheBody
    iexists leaseCacheSt0 rm
    iframe Hst
    rw [h0]
    iframe Hready
    rw [show (leaseCacheSt0 rm).installed = [] from rfl]
    iframe Hinst
    isplitl [Hent Hrv Hrm Hhdr]
    · unfold lcOwn emapOwn headerOk
      simp only [leaseCacheSt0, ↓reduceIte]
      iframe
      isplitl []
      · itrivial
      isplitl []
      · iapply BigSepM.bigSepM_empty.2; iempintro
      iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · imodintro; simp only [leaseCacheSt0]
      iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · imodintro; simp only [leaseCacheSt0]
      iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · ipureintro; exact leaseCacheSt0_wf rm
    unfold leasingX leasingXBody
    iexists ((null : Loc), sc, [leaseCacheSt0 rm])
    have hn : sessN null = 0 := by simp [sessN]
    simp only [hn]
    iframe
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro; unfold sessionOk; simp only [↓reduceIte]; itrivial
    imodintro; iexact Hsco
  obtain ⟨n, hn⟩ : ∃ n, Int.toNat sync.rwmutex.actualMaxReaders = n + 1 :=
    ⟨Int.toNat sync.rwmutex.actualMaxReaders - 1, by
      rw [sync.rwmutex.actualMaxReaders_unseal]; decide⟩
  have hn' : leasingMaxReaders = n + 1 := hn
  rw [hn']
  rw [hn, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨H1, Hrds⟩
  icases sync.ownRWMutex_guard _ _ $$ H1 with ⟨H1, #Hg⟩
  imodintro
  isplitr
  · unfold lkvCache isLeaseCache
    iframe #
  iapply BigSepL.bigSepL_cons.2
  unfold lkvReader leaseCacheReader
  iframe

end lemmas

end EtcdGrove
end Perennial
