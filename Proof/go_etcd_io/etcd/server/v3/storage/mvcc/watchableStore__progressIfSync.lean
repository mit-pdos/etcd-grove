/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressIfSync
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcher__send
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The group's all-watchers set at a fraction, lent: the group's struct and the set at `q`,
and the group back from them. -/
theorem mvcc.ownWatcherGroup_watchers_frac (wg : Loc) (W : GMap Loc mvcc.WatchRange) (q : Qp) :
    mvcc.ownWatcherGroup (GF := GF) wg W q ⊢
      ∃ v : watcherGroup, typedPointsto wg v (DFrac.own q) ∗
        mvcc.ownWatcherSet v.watchers' (domSet W) q ∗
        (typedPointsto wg v (DFrac.own q) -∗ mvcc.ownWatcherSet v.watchers' (domSet W) q -∗
          mvcc.ownWatcherGroup wg W q) := by
  iintro Hg
  unfold mvcc.ownWatcherGroup
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  iexists _
  iframe Hwg Hws
  iintro Hwg Hws
  iexists km, ws, t, KM, L
  simp only [named]
  iframe Hwg Hws Hfixed Hkm Hivt Hranges
  ipureintro; exact HL

/-- The persistent facts of a watcher under the lock (`memberRes`): its names and fixed fields;
live, its channel, a lower bound of its delivered events and its population's facts. -/
def mvcc.memberFacts (γ : mvcc.WsNames) (σ : mvcc.WsState) (w : Loc) (st : mvcc.WatcherSt) :
    IProp GF :=
  iprop(∃ (γw : mvcc.WatcherNames) (r : mvcc.WatchRange) (fcs : GoSlice),
    ⌜σ.M !! w = some γw⌝ ∗ mvcc.watcherMeta γ w γw ∗ mvcc.watcherFixed w r fcs ∗
    (⌜¬ σ.live w⌝ ∨ (⌜σ.live w⌝ ∗ mvcc.watcherChan γ w γw st.ch ∗ mvcc.filtersOk fcs ∗
      ∃ (evsw : List mvcc.EvM) (d : Nat), ⌜σ.E !! w = some (evsw, d)⌝ ∗
        monoListLbOwn γw.evs evsw ∗ mvcc.popFacts γ σ w r γw.lo st evsw d)))

instance mvcc.memberFacts_persistent (γ : mvcc.WsNames) (σ : mvcc.WsState) (w : Loc)
    (st : mvcc.WatcherSt) : Persistent (mvcc.memberFacts (GF := GF) γ σ w st) := by
  unfold mvcc.memberFacts; infer_instance

theorem mvcc.memberFacts_of (γ : mvcc.WsNames) (q : Qp) (σ : mvcc.WsState) (w : Loc)
    (st : mvcc.WatcherSt) : mvcc.memberRes (GF := GF) γ q σ w st ⊢ mvcc.memberFacts γ σ w st := by
  iintro Hmu
  iunfold mvcc.memberRes at Hmu
  icases Hmu with ⟨%γw, %r, %fcs, %HMw, #Hm, #Hf, Hmu⟩
  iunfold mvcc.memberFacts
  iexists γw, r, fcs
  iframe Hm Hf
  isplitr
  · ipureintro; exact HMw
  by_cases hl : σ.live w
  · rw [if_pos hl]
    icases Hmu with ⟨#Hc, #Hfo, -, %evsw, %d, %HE, Hevs, -, #Hpop⟩
    ihave #Hlb := monoListLbOwn_get _ _ _ $$ Hevs
    iright
    isplitr
    · ipureintro; exact hl
    iframe Hc Hfo
    iexists evsw, d
    iframe Hlb Hpop
    ipureintro; exact HE
  · ileft; ipureintro; exact hl

/-- **A synced watcher is covered** (K1b): delivered past the revision of a certified log at most
the notified one (`synced_d`), registered on its channel. -/
theorem mvcc.cov_entry_synced (γ : mvcc.WsNames) (σ : mvcc.WsState) (rev : w64) (C : mvcc.Log)
    (w : Loc) (γw' : mvcc.WatcherNames) (hok : mvcc.WsOk σ) (hsy : (σ.Ws !! w).isSome)
    (hC : C.length ≤ σ.Lmu.length) (hrev : sint.Z rev + 1 ≤ (C.length : Int))
    (hsb : σ.syncedBelow σ.Lmu.length) (hrevE : (σ.Lmu.length : Int) ≤ sint.Z rev + 1)
    (hsrb : σ.srBelow σ.Lmu.length) :
    □ ([∗map] w ↦ st ∈ σ.ST, mvcc.memberFacts (GF := GF) γ σ w st) ∗ mvcc.watcherMeta γ w γw' ⊢
      ∃ c : mvcc.CovArg, ⌜c.w = w ∧ σ.M !! w = some c.γw ∧ σ.E !! w = some (c.evsw, c.d)⌝ ∗
        mvcc.covEntry γ γw'.wc rev c := by
  iintro ⟨#HF, #Hm'⟩
  have hlive : σ.live w := Or.inl hsy
  obtain ⟨st0, hst0⟩ := Option.isSome_iff_exists.1 (hok.live_st w hlive)
  ihave #Hw := BigSepM.bigSepM_lookup hst0 $$ HF
  iunfold mvcc.memberFacts at Hw
  icases Hw with ⟨%γw, %r, %fcs, %HMw, #Hm, #Hf, Hw⟩
  icases Hw with (%hn | ⟨-, #Hc, -, %evsw, %d, %HE, #Hlb, #Hpop⟩)
  · exact absurd hlive hn
  ihave %Hag := mvcc.watcherMeta_agree γ w γw γw' $$ Hm Hm'
  subst Hag
  iunfold mvcc.popFacts at Hpop
  rw [if_pos hsy]
  icases Hpop with ⟨-, #Hwf⟩
  iunfold mvcc.watcherChan at Hc
  icases Hc with ⟨-, -, #Hreg⟩
  have hd := hok.synced_d w γw (evsw, d) hsy HMw HE
  have hb := hsb w γw (evsw, d) hsy HMw HE
  iexists ⟨w, γw, r, fcs, evsw, d⟩
  isplitr
  · ipureintro; exact ⟨rfl, HMw, HE⟩
  iunfold mvcc.covEntry
  iframe Hm Hf Hlb Hwf Hreg
  ipureintro
  have h1 : σ.Lmu.length ≤ d := (Nat.max_le.1 hd).2
  have : (C.length : Int) ≤ (d : Int) := by exact_mod_cast Nat.le_trans hC h1
  refine ⟨rfl, by simp only; omega, ?_, fun h => by
    have := hsrb w γw HMw h; simp only; omega⟩
  simp only at hb ⊢
  rcases hb with hb | hb
  · left; omega
  · right; exact hb

/-- **The synced watchers `W` are covered** (K1b): `cov_entry_synced` for each, on the channel `γc`
of all of them. -/
theorem mvcc.cov_entries (γ : mvcc.WsNames) (σ : mvcc.WsState) (rev : w64) (C : mvcc.Log)
    (γc : mvcc.WatchChanNames) (hok : mvcc.WsOk σ) (hC : C.length ≤ σ.Lmu.length)
    (hrev : sint.Z rev + 1 ≤ (C.length : Int))
    (hsb : σ.syncedBelow σ.Lmu.length) (hrevE : (σ.Lmu.length : Int) ≤ sint.Z rev + 1)
    (hsrb : σ.srBelow σ.Lmu.length) :
    ∀ W : List Loc, (∀ w ∈ W, (σ.Ws !! w).isSome) →
    □ ([∗map] w ↦ st ∈ σ.ST, mvcc.memberFacts (GF := GF) γ σ w st) ∗
      □ (∀ w : Loc, ⌜w ∈ W⌝ -∗ ∃ γw' : mvcc.WatcherNames, mvcc.watcherMeta γ w γw' ∗ ⌜γw'.wc = γc⌝) ⊢
      ∃ cs : List mvcc.CovArg, mvcc.covPre γ γc rev cs ∗ ⌜cs.map mvcc.CovArg.w = W ∧
        ∀ c ∈ cs, σ.M !! c.w = some c.γw ∧ σ.E !! c.w = some (c.evsw, c.d)⌝
  | [], _ => by
    iintro -
    iexists []
    isplitl
    · iapply mvcc.covPre_nil
    ipureintro; exact ⟨rfl, fun c hc => by cases hc⟩
  | w :: W, hW => by
    iintro ⟨#HF, #HM⟩
    icases HM $$ %w %List.mem_cons_self with ⟨%γw', #Hm, %Hwc⟩
    icases mvcc.cov_entry_synced γ σ rev C w γw' hok (hW w List.mem_cons_self) hC hrev hsb hrevE hsrb
      $$ [$HF $Hm] with ⟨%c, %hc, #Hc⟩
    irevert Hc; rw [Hwc]; iintro #Hc
    icases mvcc.cov_entries γ σ rev C γc hok hC hrev hsb hrevE hsrb W
      (fun x hx => hW x (List.mem_cons_of_mem _ hx)) $$ [] with ⟨%cs, #Hcs, %hcs⟩
    · isplit
      · iexact HF
      iintro !> %x %hx
      iapply HM
      ipureintro; exact List.mem_cons_of_mem _ hx
    iexists c :: cs
    isplitl
    · iunfold mvcc.covPre
      iapply BigSepL.bigSepL_cons.2
      iunfold mvcc.covPre at Hcs
      iframe Hc Hcs
    ipureintro
    obtain ⟨hc1, hc2, hc3⟩ := hc
    refine ⟨by simp [hc1, hcs.1], fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | h
    · rw [hc1]; exact ⟨hc2, hc3⟩
    · exact hcs.2 c' h

/-- A list without repetitions, of the same members (the stream's map can name a watcher
twice; its shares are lent once). -/
def mvcc.dedupL : List Loc → List Loc
  | [] => []
  | x :: xs => if x ∈ xs then mvcc.dedupL xs else x :: mvcc.dedupL xs

theorem mvcc.mem_dedupL {w : Loc} : ∀ {l : List Loc}, w ∈ mvcc.dedupL l ↔ w ∈ l
  | [] => by simp [mvcc.dedupL]
  | x :: xs => by
    unfold mvcc.dedupL
    split
    · rw [mvcc.mem_dedupL]
      constructor
      · exact List.mem_cons_of_mem _
      · intro h; rcases List.mem_cons.1 h with rfl | h
        · assumption
        · exact h
    · rw [List.mem_cons, List.mem_cons, mvcc.mem_dedupL]

theorem mvcc.nodup_dedupL : ∀ l : List Loc, (mvcc.dedupL l).Nodup
  | [] => by simp [mvcc.dedupL]
  | x :: xs => by
    unfold mvcc.dedupL
    split
    · exact mvcc.nodup_dedupL xs
    · rename_i h
      exact List.nodup_cons.2 ⟨fun hm => h (mvcc.mem_dedupL.1 hm), mvcc.nodup_dedupL xs⟩

/-- What a sender of a progress response borrows from a covered watcher's lock share (K2e-4):
its delivered events' and live fractions. -/
def mvcc.covLent (q : Qp) (c : mvcc.CovArg) : IProp GF :=
  iprop(monoListAuthOwn c.γw.evs q c.evsw ∗ dghostVar c.γw.live (DFrac.own q) true)

theorem mvcc.memberRes_lend (γ : mvcc.WsNames) (q : Qp) (σ : mvcc.WsState) (st : mvcc.WatcherSt)
    (c : mvcc.CovArg) (hl : σ.live c.w) (hm : σ.M !! c.w = some c.γw)
    (he : σ.E !! c.w = some (c.evsw, c.d)) :
    mvcc.memberRes (GF := GF) γ q σ c.w st ⊢
      mvcc.covLent q.half c ∗ (mvcc.covLent q.half c -∗ mvcc.memberRes γ q σ c.w st) := by
  iintro H
  iunfold mvcc.memberRes at H
  icases H with ⟨%γw, %r, %fcs, %HMw, #Hm, #Hf, H⟩
  rw [hm] at HMw; cases HMw
  rw [if_pos hl]
  icases H with ⟨#Hc, #Hfo, %Hsr, %evsw, %d, %HE, Ha, Hlv, #Hpop⟩
  rw [he] at HE; cases HE
  iunfold mvcc.covLent
  iframe Ha Hlv
  iintro ⟨Ha, Hlv⟩
  iunfold mvcc.memberRes
  iexists c.γw, r, fcs
  iframe Hm Hf
  isplitr
  · ipureintro; exact hm
  rw [if_pos hl]
  iframe Hc Hfo
  isplitr
  · ipureintro; exact Hsr
  iexists c.evsw, c.d
  iframe Ha Hlv Hpop
  ipureintro; exact he

/-- **The covered watchers' shares, lent** (K2e-4): `memberRes_lend` for each (distinct). -/
theorem mvcc.members_lend (γ : mvcc.WsNames) (q : Qp) (σ : mvcc.WsState) :
    ∀ (cs : List mvcc.CovArg) (ST : GMap Loc mvcc.WatcherSt), (cs.map mvcc.CovArg.w).Nodup →
    (∀ c ∈ cs, σ.live c.w ∧ σ.M !! c.w = some c.γw ∧ σ.E !! c.w = some (c.evsw, c.d) ∧
      (ST !! c.w).isSome) →
    ([∗map] w ↦ st ∈ ST, mvcc.memberRes (GF := GF) γ q σ w st) ⊢
      ([∗list] c ∈ cs, mvcc.covLent q.half c) ∗
        (([∗list] c ∈ cs, mvcc.covLent q.half c) -∗ [∗map] w ↦ st ∈ ST, mvcc.memberRes γ q σ w st)
  | [], ST, _, _ => by
    iintro H
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iintro -; iexact H
  | c :: cs, ST, hnd, hf => by
    obtain ⟨hl, hm, he, hst⟩ := hf c List.mem_cons_self
    obtain ⟨st, hst'⟩ := Option.isSome_iff_exists.1 hst
    have hnd' := List.nodup_cons.1 hnd
    have hf' : ∀ c' ∈ cs, σ.live c'.w ∧ σ.M !! c'.w = some c'.γw ∧
        σ.E !! c'.w = some (c'.evsw, c'.d) ∧ ((Std.delete ST c.w) !! c'.w).isSome := by
      intro c' hc'
      obtain ⟨h1, h2, h3, h4⟩ := hf c' (List.mem_cons_of_mem _ hc')
      refine ⟨h1, h2, h3, ?_⟩
      have hne : c.w ≠ c'.w := by
        intro h; apply hnd'.1; rw [h]; exact List.mem_map.2 ⟨c', hc', rfl⟩
      show (GMap.delete c.w ST !! c'.w).isSome
      rw [GMap.lookup_delete_ne _ hne]; exact h4
    iintro H
    icases (BigSepM.bigSepM_delete hst').1 $$ H with ⟨Hc, H⟩
    icases mvcc.memberRes_lend γ q σ st c hl hm he $$ Hc with ⟨Lc, Hcb⟩
    icases mvcc.members_lend γ q σ cs (Std.delete ST c.w) hnd'.2 hf' $$ H with ⟨Ls, Hb⟩
    isplitl [Lc Ls]
    · iapply BigSepL.bigSepL_cons.2; iframe Lc Ls
    iintro HL
    icases BigSepL.bigSepL_cons.1 $$ HL with ⟨Lc, Ls⟩
    iapply (BigSepM.bigSepM_delete hst').2
    isplitl [Hcb Lc]
    · iapply Hcb $$ Lc
    iapply Hb $$ Ls

theorem mvcc.watchableStore.progressIfSync.wp_proof
    (hrev : mvcc.watchableStore.rev.spec (GF := GF) (hG := hG))
    (hsend : mvcc.watcher.send.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.progressIfSync.spec (GF := GF) (hG := hG) := by
  have hrev := mvcc.watchableStore.rev.spec_frozen hrev
  intro s st γ m dq M rid γc CS
  wp_start as ⟨#Hws, Hm, #HM, HCS, #Hcw, HR⟩
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hrd, Hslot⟩
  ihave #Hws0 := Hws
  iunfold mvcc.isWatchableStore at Hws0
  iNamedSuffix Hws0 "W"
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hslot] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  -- `s.rev()`, lent the lock body's fraction of the committed log: the notified log (unit W-K)
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP, Hrel, Hwsf, %HsetR⟩
  obtain ⟨Hset, Hsrb⟩ := HsetR
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  iunfold mvcc.wlogQ at Hwlog
  icases Hwlog with ⟨Hwl, Hla⟩
  wp_apply (hrev s st γ (some (sync.rfrac.half.half, σ.Lmu))) $$ [$Hws $Hrd Hla]
    as %r ⟨Hrd, Hla, %Clog, #HcertR, %HCr⟩
  · unfold mvcc.logLent; iexact Hla
  have hClm : Clog = σ.Lmu := HCr.2.2.2.2 _ _ rfl
  ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
      [Hσ Hwl Hla Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody; iunfold mvcc.wlogQ; simp only [named]
    unfold mvcc.logLent at *
    iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
  (try wp_auto)
  ihave Hdx : (defer ↦ func.mk BAnon BAnon
      (Seq (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"RUnlock" #(mvcc.wsMuAddr s)))
        (Val #())) (App (Val #(func.mk BAnon BAnon (Val #()))) (Val #()))) : IProp GF) $$ [defer]
  · iexact defer
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ wv : Loc,
      "w" ∷ w_ptr ↦ wv ∗ "s" ∷ s_ptr ↦ s ∗ "responseWatchID" ∷ responseWatchID_ptr ↦ rid ∗
      "watchers" ∷ watchers_ptr ↦ m ∗ "Hrl" ∷ sync.ownRWMutexRLocked (mvcc.wsMuAddr s) (mvcc.watchStoreInv s γ) ∗
      "Hdx" ∷ (defer ↦ func.mk BAnon BAnon
        (Seq (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"RUnlock" #(mvcc.wsMuAddr s)))
          (Val #())) (App (Val #(func.mk BAnon BAnon (Val #()))) (Val #()))) : IProp GF) ∗
      "HP" ∷ mvcc.watchStoreBody s γ sync.rfrac σ ∗
      "Hrel" ∷ monoNatAuthOwn γ.rel sync.rfrac σ.Lmu.length ∗
      "Hwsf" ∷ mvcc.wsFields s γ sync.rfrac ∗
      "Hrd" ∷ mvcc.storeReader st γ.st ∗ "rev" ∷ rev_ptr ↦ r ∗
      "HΦ" ∷ (∀ b : Bool, m ↦${dq} M ∗ CS ∗ mvcc.watchReader s st γ -∗ Φ #b) ∗ "HCS" ∷ CS ∗
      "%Hi" ∷ ⌜0 ≤ i ∧ ∀ (j : Nat) (id : w64) (w : Loc), j < i.toNat → keys[j]? = some id →
        M !! id = some w → (σ.Ws !! w).isSome⌝)) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [w s responseWatchID watchers Hrl Hdx HP Hrel Hwsf Hrd rev HΦ HCS]
  · iexists _
    simp only [named]
    iframe
    ipureintro
    exact ⟨Int.le_refl _, fun j _ _ hj => by simp at hj⟩
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP'
    iNamed HP'
    wp_auto
    iunfold mvcc.watchStoreBody at HP
    iNamed HP
    icases mvcc.ownWatcherGroup_watchers_frac _ _ _ $$ Hsynced with ⟨%gv, Hwg, Hwset, Hgback⟩
    iunfold mvcc.ownWatcherSet at Hwset
    ihave %Hgnn := typedPointsto_not_null _ _ _ $$ Hwg
    icases typedPointsto_split _ _ _ $$ Hwg with Hwg
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hwg
    wp_auto
    wp_apply wp_map_lookup2 $$ [$Hwset] as Hwset
    ihave Hwg : typedPointsto (mvcc.syncedAddr s) gv (DFrac.own sync.rfrac) $$ [keyWatchers ranges watchers]
    · iapply typedPointsto_combine _ _ _ Hgnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hwset : mvcc.ownWatcherSet gv.watchers' (domSet σ.Ws) sync.rfrac $$ [Hwset]
    · iunfold mvcc.ownWatcherSet; iexact Hwset
    ihave Hsynced := Hgback $$ Hwg Hwset
    ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
        [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem]
    · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
    cases hsy : (σ.Ws !! u).isSome
    · simp only [Option.isSome_map, hsy]
      wp_auto
      unfold forMapPostcondition
      iright; iright; iright
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hm
      wp_auto
      wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP Hrel Hwsf] as Hslot
      · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iframe HP Hrel Hwsf; ipureintro; exact ⟨Hset, Hsrb⟩
      wp_auto
      iapply HΦ
      iframe Hm HCS
      iunfold mvcc.watchReader
      iframe
    · simp only [Option.isSome_map, hsy]
      ihave #Hiw := HM $$ %key %u %Hu
      simp only [mvcc.storeWatchParams]
      icases Hiw with ⟨⟨%γw, %rr, %fcs, #Hmeta, #Hfix, %Hsr⟩, -⟩
      ihave #Hfix' := Hfix
      iunfold mvcc.watcherFixed at Hfix'
      icases Hfix' with ⟨%Hnn, %ks, %es, -, -, -, -, #HsR, -, -⟩
      wp_auto
      wp_if_destruct
      · (try wp_auto)
        unfold forMapPostcondition
        iright; iright; iright
        iexists _
        isplitr
        · ipureintro; rfl
        iintro Hm
        wp_auto
        wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP Hrel Hwsf] as Hslot
        · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iframe HP Hrel Hwsf; ipureintro; exact ⟨Hset, Hsrb⟩
        wp_auto
        iapply HΦ
        iframe Hm HCS
        iunfold mvcc.watchReader
        iframe
      · (try wp_auto)
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        simp only [named]
        iframe
        ipureintro
        refine ⟨by omega, fun j id w hj hk hm => ?_⟩
        by_cases hji : j < i.toNat
        · exact Hi.2 j id w hji hk hm
        · have : j = i.toNat := by omega
          subst this
          rw [Hkey] at hk; cases hk
          rw [Hu] at hm; cases hm
          exact hsy
  iintro HP' Hm
  iNamed HP'
  have hall : ∀ id w, M !! id = some w → (σ.Ws !! w).isSome := by
    intro id w hw
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ((Hkset id).2 (by rw [hw]; rfl))
    have hjl : j < keys.length := (List.getElem?_eq_some_iff.1 hj).1
    exact Hi.2 j id w (by omega) hj hw
  -- what the response covers (K1b): every watcher of the map, all synced
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  icases (persistent_entails_right (mvcc.wlogQ_cert_prefix (GF := GF) γ sync.rfrac σ.Lmu Clog))
    $$ [$Hwlog $HcertR] with ⟨%HCp, ⟨Hwlog, -⟩⟩
  icases (BigSepM.bigSepM_mono (fun {_ _} _ =>
      persistent_entails_right (mvcc.memberFacts_of (GF := GF) γ sync.rfrac σ _ _))) $$ Hmem with Hmem
  rw [BigSepM.bigSepM_sep_eq] at *
  icases Hmem with ⟨#HF, Hmem⟩
  have hr1 : 1 ≤ sint.Z r := by
    obtain ⟨-, rfl, h2, h3⟩ := HCr
    word
  have hrevC : sint.Z r + 1 ≤ (Clog.length : Int) := by
    obtain ⟨hne, rfl, -, -⟩ := HCr
    have : 0 < Clog.length := List.length_pos_iff.2 hne
    word
  have hrevE : (σ.Lmu.length : Int) ≤ sint.Z r + 1 := by
    rw [← hClm]
    obtain ⟨hne, rfl, h2, h3⟩ := HCr
    word
  icases mvcc.cov_entries γ σ r Clog γc Hok HCp.length_le hrevC Hset.1 hrevE Hsrb
      (mvcc.dedupL (keys.filterMap (M !! ·)))
      (fun w hw => by
        obtain ⟨id, -, hid⟩ := List.mem_filterMap.1 (mvcc.mem_dedupL.1 hw)
        exact hall id w hid) $$ [] with ⟨%cs, #Hcs, %Hcsw0⟩
  · isplit
    · iexact HF
    iintro !> %w %hw
    obtain ⟨id, -, hid⟩ := List.mem_filterMap.1 (mvcc.mem_dedupL.1 hw)
    icases HM $$ %id %w %hid with ⟨-, %γw2, %rr2, %fcs2, #Hm2, %Hwc2, -⟩
    iexists γw2
    iframe Hm2
    ipureintro; exact Hwc2
  obtain ⟨Hcsw, Hcsf⟩ := Hcsw0
  have hcsl : ∀ c ∈ cs, σ.live c.w ∧ σ.M !! c.w = some c.γw ∧ σ.E !! c.w = some (c.evsw, c.d) ∧
      (σ.ST !! c.w).isSome := by
    intro c hc
    have hw : c.w ∈ mvcc.dedupL (keys.filterMap (M !! ·)) := by
      rw [← Hcsw]; exact List.mem_map.2 ⟨c, hc, rfl⟩
    obtain ⟨id, -, hid⟩ := List.mem_filterMap.1 (mvcc.mem_dedupL.1 hw)
    have hl : σ.live c.w := Or.inl (hall id c.w hid)
    exact ⟨hl, (Hcsf c hc).1, (Hcsf c hc).2, Hok.live_st _ hl⟩
  have hcsnd : (cs.map mvcc.CovArg.w).Nodup := by rw [Hcsw]; exact mvcc.nodup_dedupL _
  ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
      [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem]
  · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ wv : Loc,
      "w" ∷ w_ptr ↦ wv ∗ "responseWatchID" ∷ responseWatchID_ptr ↦ rid ∗
      "Hrl" ∷ sync.ownRWMutexRLocked (mvcc.wsMuAddr s) (mvcc.watchStoreInv s γ) ∗
      "Hdx" ∷ (defer ↦ func.mk BAnon BAnon
        (Seq (App (Val #(methods (go.GoType.PointerType sync.RWMutex.ty) go!"RUnlock" #(mvcc.wsMuAddr s)))
          (Val #())) (App (Val #(func.mk BAnon BAnon (Val #()))) (Val #()))) : IProp GF) ∗
      "HP" ∷ mvcc.watchStoreBody s γ sync.rfrac σ ∗
      "Hrel" ∷ monoNatAuthOwn γ.rel sync.rfrac σ.Lmu.length ∗
      "Hwsf" ∷ mvcc.wsFields s γ sync.rfrac ∗
      "Hrd" ∷ mvcc.storeReader st γ.st ∗ "rev" ∷ rev_ptr ↦ r ∗
      "HΦ" ∷ (∀ b : Bool, m ↦${dq} M ∗ CS ∗ mvcc.watchReader s st γ -∗ Φ #b) ∗ "HCS" ∷ CS)) $$ Hm
  iintro %keys2 -
  isplitl [w responseWatchID Hrl Hdx HP Hrel Hwsf Hrd rev HΦ HCS]
  · iexists _
    simp only [named]
    iframe
  isplitr
  · imodintro
    iintro %i %key %u ⟨%Hkey, %Hu⟩ HP'
    iNamed HP'
    wp_auto
    have hsy := hall key u Hu
    iunfold mvcc.watchStoreBody at HP
    iNamed HP
    have hlive : σ.live u := Or.inl hsy
    obtain ⟨st0, hst0⟩ := Option.isSome_iff_exists.1 (Hok.live_st u hlive)
    icases (BigSepM.bigSepM_lookup_acc hst0).1 $$ Hst with ⟨Hwu, Hst⟩
    -- the lock's fraction of the notified log, lent to the send (K2e-5)
    iunfold mvcc.wlogQ at Hwlog
    icases Hwlog with ⟨Hwl, Hla⟩
    ihave Hwl : mvcc.notifiedLent γ (some (sync.rfrac.half, σ.Lmu)) $$ [Hwl]
    · iunfold mvcc.notifiedLent; iexact Hwl
    ihave #Hfu := BigSepM.bigSepM_lookup hst0 $$ HF
    iunfold mvcc.memberFacts at Hfu
    icases Hfu with ⟨%γw, %rr, %fcs, %HMw, #HmetaW, #HfixW, Hfu⟩
    icases Hfu with (%hn | ⟨-, #Hchan, #Hfok, %evsw, %d, %HE, -, -⟩)
    · exact absurd hlive hn
    -- the covered watchers' shares, lent to the send (K2e-4); `u`'s live fraction among them
    icases mvcc.members_lend γ sync.rfrac σ cs σ.ST hcsnd hcsl $$ Hmem with ⟨Hlent, Hmemb⟩
    iunfold mvcc.covLent at Hlent
    icases (BigSepL.bigSepL_sep_eqv (Φ := fun _ c => monoListAuthOwn (GF := GF) c.γw.evs sync.rfrac.half c.evsw)
      (Ψ := fun _ c => dghostVar (GF := GF) c.γw.live (DFrac.own sync.rfrac.half) true) (l := cs)).1 $$ Hlent
      with ⟨Hca, Hlvs⟩
    obtain ⟨cu, hcu, hcuw⟩ : ∃ cu ∈ cs, cu.w = u := by
      have hu : u ∈ mvcc.dedupL (keys.filterMap (M !! ·)) :=
        mvcc.mem_dedupL.2 (List.mem_filterMap.2 ⟨key, (Hkset key).2 (by rw [Hu]; rfl), Hu⟩)
      rw [← Hcsw] at hu
      obtain ⟨cu, hcu, h⟩ := List.mem_map.1 hu
      exact ⟨cu, hcu, h⟩
    have hγu : cu.γw = γw := by
      have h := (Hcsf cu hcu).1
      rw [hcuw, HMw] at h; cases h; rfl
    icases BigSepL.bigSepL_mem_acc hcu $$ Hlvs with ⟨Hlv, Hlvb⟩
    irevert Hlv; rw [hγu]; iintro Hlv
    ihave Hca : mvcc.covAuth sync.rfrac.half cs $$ [Hca]
    · iunfold mvcc.covAuth; iexact Hca
    iunfold mvcc.watcherOwn at Hwu
    icases Hwu with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
    ihave #Hnil := ownSlice_nil (V := Loc) (GF := GF) DFrac.discard
    -- the response's id: the watcher's own, or its channel's progress fact (unit W-M2)
    icases HM $$ %key %u %Hu with ⟨-, %γw2, %rr2, %fcs2, #Hm2, %Hwc2, #Hf2, #Hrid⟩
    subst Hwc2
    ihave %Hag1 := mvcc.watcherMeta_agree γ u γw γw2 $$ HmetaW Hm2
    ihave %Hag2 := mvcc.watcherFixed_agree u rr rr2 fcs fcs2 $$ [$HfixW $Hf2]
    obtain ⟨rfl, rfl⟩ := Hag2
    subst Hag1
    -- the response's id, and (K1b) for `-1`, the registered watchers: the map's, or cancelled
    ihave #Hidc : iprop(⌜rid = rr.id⌝ ∨ ⌜rid = W64 (-1)⌝ ∗
        mvcc.complW γw sync.rfrac.half CS (cs.map mvcc.CovArg.w) rid r []) $$ []
    · icases Hrid with (%h | ⟨%hm1, #Hp⟩)
      · ileft; ipureintro; exact h
      icases Hcw with (%hne | #Hcw')
      · exact absurd hm1 hne
      iright
      isplitr
      · ipureintro; exact hm1
      iunfold mvcc.complW
      iintro !> %L %hm HCS Hregl Hlv
      iunfold mvcc.complWS at Hcw'
      have hex : ∃ id : w64, M !! id = some u := ⟨key, Hu⟩
      icases Hcw' $$ %L %u %γw %sync.rfrac.half %hex HmetaW HCS Hregl Hlv
        with ⟨HCS, Hregl, Hlv, #Hcm⟩
      iframe HCS Hregl Hlv Hp
      isplitl
      rotate_left
      · ipureintro; exact ⟨hr1, rfl⟩
      iintro !> %w0 %hw0
      icases Hcm $$ %w0 %hw0 with (⟨%id0, %hid0⟩ | #Hr)
      · ileft; ipureintro
        rw [Hcsw]
        exact mvcc.mem_dedupL.2 (List.mem_filterMap.2 ⟨id0, (Hkset id0).2 (by rw [hid0]; rfl), hid0⟩)
      · iright; iexact Hr
    wp_apply (hsend γ u γw rr fcs st0.ch sync.rfrac sync.rfrac.half [] d _ [] [] DFrac.discard cs
        sync.rfrac.half (some (sync.rfrac.half, σ.Lmu)) CS)
      $$ [$Hch $Hlv $HCS $Hca $Hwl] as %b ⟨Hch, Hlv, -, -, Hca, Hwl, HCS⟩
    · iframe #
      simp only [↓reduceIte, List.zip_nil_left]
      isplitr
      · itrivial
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      isplitr
      · ipureintro; intro _
        exact ⟨_, _, rfl, by have := hrevE; rw [← hClm] at this ⊢; omega⟩
      isplitr
      · ipureintro; intro _
        rw [Hcsw]
        exact mvcc.mem_dedupL.2 (List.mem_filterMap.2 ⟨key, (Hkset key).2 (by rw [Hu]; rfl), Hu⟩)
      ipureintro
      simp
    iunfold mvcc.notifiedLent at Hwl
    ihave Hwlog : mvcc.wlogQ γ sync.rfrac σ.Lmu $$ [Hwl Hla]
    · iunfold mvcc.wlogQ; iframe Hwl Hla
    irevert Hlv; rw [← hγu]; iintro Hlv
    ihave Hlvs := Hlvb $$ Hlv
    iunfold mvcc.covAuth at Hca
    ihave Hlent := (BigSepL.bigSepL_sep_eqv (Φ := fun _ c => monoListAuthOwn (GF := GF) c.γw.evs sync.rfrac.half c.evsw)
      (Ψ := fun _ c => dghostVar (GF := GF) c.γw.live (DFrac.own sync.rfrac.half) true) (l := cs)).2 $$ [Hca Hlvs]
    · iframe Hca Hlvs
    ihave Hmem := Hmemb $$ [Hlent]
    · iunfold mvcc.covLent; iexact Hlent
    ihave Hst := Hst $$ [Hmin Hvic Hcomp Hres Hch]
    · iunfold mvcc.watcherOwn; iframe
    ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
        [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hwt Hmem]
    · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
    (try wp_auto)
    unfold forMapPostcondition
    iright; iright; iright
    iexists _
    isplitr
    · ipureintro; rfl
    iintro Hm
    wp_auto
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP Hrel Hwsf] as Hslot
    · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iframe HP Hrel Hwsf; ipureintro; exact ⟨Hset, Hsrb⟩
    wp_auto
    iapply HΦ
    iframe Hm HCS
    iunfold mvcc.watchReader
    iframe
  iintro HP' Hm
  iNamed HP'
  wp_auto
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP Hrel Hwsf] as Hslot
  · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iframe HP Hrel Hwsf; ipureintro; exact ⟨Hset, Hsrb⟩
  wp_auto
  iapply HΦ
  iframe Hm HCS
  iunfold mvcc.watchReader
  iframe

end proof

end EtcdGrove
end Perennial
