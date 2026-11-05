/-
The watch check's lock (`watchCheck.mu`, `examples/mvccrand/mvccrand.go`): what it guards, and the
watch check's handles. Lean-first (no Rocq counterpart).

**The lock's invariant** (`cmuInv`): the watchers' map (`c.watchers`, the map `wm`) at the
registry's pointers, half of the registry `γ.reg` (id to the `*watcher` and its registration,
`RegInfo`; the tester's invariant holds the other half, `regOk` tying it to the stream's state),
half of the receiver's checked responses `γ.rcv` at `rs` (the receiver holds the other half, with
`wsRecv` at `rs` or one more), a lower bound `Hl` of the history, and each watcher's struct: its
range's slices (read-only), its position after the events `rs` carried for it (`wPosOk`: `posOk`
at `Hl`, or still at its start), and every response with events for a registered watcher
(`rcvKnown`: so a watcher registered later has received nothing, `recvEvs_fresh`). A position stays
valid as the history grows (`wPosOk_prefix`).

**The handles** (`wcCtx`, persistent given `persistent.law`): the packages, `c.h` and `c.watchers` (written once), the
lock, the tester's and the history's invariants, the store's and the stream's handles.

**Registration** (`register`): `Watch`'s update at the invariant, for a range not empty
(`register_au`: the registrar's half of `γ.cl` shows the stream open, the watcher enters both
halves of the registry, `regOk_register`) and for an empty one (`register_au_empty`: no resource,
since `Watch` gives that update back; were it committed, a watcher of an empty range is allowed
outside the registry, `regOk_register_empty`, `covers_empty`); a tick is a small revision
(`tick_bound`). **The receiver's facts** (`recv_facts`, `recv_exp`, `recv_prog`,
`recvEvs_uncovered`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WatchModel

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

/-- A registration's range test (the tester's `inRange` of its key and end). -/
def regInR (ri : RegInfo) : GoString → Bool := inRangeM ri.2.2.1 ri.1 ri.2.1

/-- A registration's first revision. -/
def regLo (ri : RegInfo) : Nat := sint.nat ri.2.2.2

/-- **A watcher's position after `n` events** against the history `Hl`: `posOk`, with its revision a
revision of `Hl`, or still its start (nothing received). -/
def wPosOk (Hl : List HRev) (ri : RegInfo) (rev index : w64) (n : Nat) : Prop :=
  0 ≤ sint.Z rev ∧ 0 ≤ sint.Z index ∧
  posOk Hl (regInR ri) (regLo ri) (sint.nat rev) (sint.nat index) n ∧
  (sint.nat rev < Hl.length ∨ (rev = ri.2.2.2 ∧ index = W64 0 ∧ n = 0))

theorem wPosOk_prefix {Hl Hl' : List HRev} (hp : Hl <+: Hl') (ri : RegInfo) (rev index : w64)
    (n : Nat) (h : wPosOk Hl ri rev index n) : wPosOk Hl' ri rev index n := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, ?_⟩
  · rcases h4 with h4 | ⟨rfl, rfl, rfl⟩
    · exact (posOk_prefix hp _ h4).1 h3
    · exact posOk_start _ _ _
  · rcases h4 with h4 | h4
    · exact Or.inl (Nat.lt_of_lt_of_le h4 hp.length_le)
    · exact Or.inr h4

/-- The events the responses carried for `id`, one more response. -/
theorem recvEvs_snoc (rs : List WResp) (r : WResp) (id : w64) :
    recvEvs (rs ++ [r]) id = recvEvs rs id ++ (if r.id = id then r.evs else []) := by
  unfold recvEvs
  rw [List.filter_append]
  by_cases h : r.id = id <;> simp [h]

/-- With no compaction, `onceUpTo` holds vacuously. -/
theorem onceUpTo_neg (L : Log) (lo : Nat) : onceUpTo L lo (-1) := by
  intro r _ hr; omega

/-- A registered watcher's range is its registration's (`regOk`'s form, `watchRangeOf`'s). -/
theorem rg_eq (kk e : GoString) (endk : GoSlice) (en : Bool) (st id : w64)
    (hen : en = decide (endk = slice.nil)) :
    (⟨kk, if en then none else some e, st, id⟩ : WatchRange) = watchRangeOf kk e endk st id := by
  subst hen; unfold watchRangeOf; by_cases h : endk = slice.nil <;> simp [h]

/-- **What a registered watcher has received** (`wsRecvOk`'s second part, no compaction): its
expected changes of the history from its start, up to some revision of the notified log. -/
theorem recv_exp (σ : MvccState) (S : StreamState) (rs : List WResp) (Hl : List HRev)
    (hok : wsRecvOk σ S rs) (hh : histOkM σ Hl) (hc : σ.crev = -1)
    (hwf : LogWf' σ.notifiedLog) (hlen : σ.notifiedLog.length < 2 ^ 63)
    (id : w64) (wi : WInfo) (hS : S.ws !! id = some wi) (kk e : GoString) (endk : GoSlice)
    (st : w64) (hrg : wi.rg = watchRangeOf kk e endk st id) (hfs : wi.fs = [])
    (hlo : wi.lo = sint.nat st) (hkk : kk ≠ []) (hst : 1 ≤ sint.Z st) :
    ∃ hi, hi ≤ σ.notifiedLog.length ∧
      recvEvs rs id = (expChs Hl (inRangeM (decide (endk = slice.nil)) kk e) (sint.nat st) hi).map
        fun p => chEv p.1 p.2 := by
  obtain ⟨hi, hhi, heq⟩ := hok.2.1 id wi hS (by rw [hc]; exact onceUpTo_neg _ _)
  refine ⟨hi, hhi, ?_⟩
  rw [heq, hfs, filtered_nil, hrg, hlo]
  exact watchEvents_eq_expChs σ Hl hh hwf hlen kk e endk st id hkk _ hi
    (by have : sint.nat st = (sint.Z st).toNat := rfl; omega) hhi

/-- **A watcher's progress response** at its revision (`wsRecvOk`'s third part, no compaction):
what it has received is its expected changes up to the response's revision. -/
theorem recv_prog (σ : MvccState) (S : StreamState) (rs : List WResp) (Hl : List HRev)
    (hok : wsRecvOk σ S rs) (hh : histOkM σ Hl) (hc : σ.crev = -1)
    (hwf : LogWf' σ.notifiedLog) (hlen : σ.notifiedLog.length < 2 ^ 63)
    (j : Nat) (r : WResp) (hj : rs[j]? = some r) (hev : r.evs = []) (hcr : r.compactRev = W64 0)
    (wi : WInfo) (hS : S.ws !! r.id = some wi) (kk e : GoString) (endk : GoSlice)
    (st : w64) (hrg : wi.rg = watchRangeOf kk e endk st r.id) (hfs : wi.fs = [])
    (hlo : wi.lo = sint.nat st) (hkk : kk ≠ []) (hst : 1 ≤ sint.Z st) :
    recvEvs (rs.take (j + 1)) r.id =
      (expChs Hl (inRangeM (decide (endk = slice.nil)) kk e) (sint.nat st)
        (sint.nat r.rev + 1)).map fun p => chEv p.1 p.2 := by
  have h1 := (hok.1 r (List.mem_of_getElem? hj)).2.2.1 hcr
  rw [hok.2.2 j r r.id wi hj hev hcr hS (by rw [hc]; exact onceUpTo_neg _ _) (Or.inl rfl), hfs,
    filtered_nil, hrg, hlo]
  exact watchEvents_eq_expChs σ Hl hh hwf hlen kk e endk st r.id hkk _ _
    (by have : sint.nat st = (sint.Z st).toNat := rfl; omega) (by omega)

/-! ### Registration (`register`) -/

/-- **An empty range covers no key** (`Watch`'s first arm: a non-empty end at or below the key). -/
theorem covers_empty (kk e : GoString) (endk : GoSlice) (s id : w64) (he : e ≠ [])
    (hle : ¬ go.GoStringLt kk e) (hn : endk ≠ slice.nil) (k : GoString) :
    (watchRangeOf kk e endk s id).covers k = false := by
  unfold watchRangeOf WatchRange.covers
  simp only [hn, ↓reduceIte, decide_eq_false_iff_not, not_and]
  intro h1 h2
  rw [adt.affCmp_nonneg_iff] at h1
  rw [adt.affCmp_neg_iff, adt.affLt_iff_of_ne k e he] at h2
  apply h1
  obtain ⟨hk, hke⟩ := h2
  refine ⟨hk, Or.inr ?_⟩
  by_cases hek : go.GoStringLt e kk
  · exact go.goStringLt_trans hke hek
  · have := go.goStringLt_eq_of_not_lt hle hek
    rw [this]; exact hke

/-- **Registering a watcher of the registry** keeps the registry the stream's. -/
theorem regOk_register (S : StreamState) (W : GMap w64 (Loc × RegInfo)) (h : regOk S W)
    (id : w64) (hid : S.ws !! id = none) (wp : Loc) (kk e : GoString) (en : Bool) (st : w64)
    (wi : WInfo) (hrg : wi.rg = ⟨kk, if en then none else some e, st, id⟩) (hfs : wi.fs = [])
    (hlo : wi.lo = sint.nat st) (hlive : wi.live = true) :
    W !! id = none ∧ regOk (S.register id wi) (<[id := (wp, (kk, e, en, st))]> W) := by
  have hW : W !! id = none := by
    have := h id
    cases hw : W !! id with
    | none => rfl
    | some x =>
      obtain ⟨wp', kk', e', en', st'⟩ := x
      rw [hw] at this
      obtain ⟨wi', hwi', -⟩ := this
      rw [hid] at hwi'; cases hwi'
  refine ⟨hW, fun id' => ?_⟩
  unfold StreamState.register
  by_cases he : id' = id
  · subst he
    rw [GMap.lookup_insert]
    simp only
    exact ⟨wi, by rw [GMap.lookup_insert], hrg, hfs, hlo, hlive⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]
    have := h id'
    cases hw : W !! id' with
    | none =>
      rw [hw] at this
      intro wi' hwi'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hwi'
      exact this wi' hwi'
    | some x =>
      obtain ⟨wp', kk', e', en', st'⟩ := x
      rw [hw] at this
      simp only at this ⊢
      rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]
      exact this

/-- **Registering a watcher of an empty range** (outside the registry) keeps the registry the
stream's. -/
theorem regOk_register_empty (S : StreamState) (W : GMap w64 (Loc × RegInfo)) (h : regOk S W)
    (id : w64) (hid : S.ws !! id = none) (wi : WInfo) (hcov : ∀ k, wi.rg.covers k = false) :
    regOk (S.register id wi) W := by
  intro id'
  unfold StreamState.register
  have := h id'
  by_cases he : id' = id
  · subst he
    cases hw : W !! id' with
    | none =>
      simp only
      intro wi' hwi'
      rw [GMap.lookup_insert] at hwi'
      cases hwi'; exact hcov
    | some x =>
      obtain ⟨wp', kk', e', en', st'⟩ := x
      rw [hw] at this
      obtain ⟨wi', hwi', -⟩ := this
      rw [hid] at hwi'; cases hwi'
  · cases hw : W !! id' with
    | none =>
      rw [hw] at this
      simp only
      intro wi' hwi'
      rw [GMap.lookup_insert_ne _ _ (Ne.symm he)] at hwi'
      exact this wi' hwi'
    | some x =>
      obtain ⟨wp', kk', e', en', st'⟩ := x
      rw [hw] at this
      simp only at this ⊢
      rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]
      exact this

/-- **A watcher of an empty range has received nothing** (`wsRecvOk`'s second part). -/
theorem recvEvs_uncovered (σ : MvccState) (S : StreamState) (rs : List WResp)
    (hok : wsRecvOk σ S rs) (hc : σ.crev = -1) (id : w64) (wi : WInfo) (hS : S.ws !! id = some wi)
    (hcov : ∀ k, wi.rg.covers k = false) : recvEvs rs id = [] := by
  obtain ⟨hi, -, heq⟩ := hok.2.1 id wi hS (by rw [hc]; exact onceUpTo_neg _ _)
  rw [heq]
  unfold filtered watchEvents
  simp [hcov]

/-- A longer lower bound of the history still covers the notified history. -/
theorem histOkM_prefix {σ : MvccState} {Hl Hm : List HRev} (hh : histOkM σ Hl) (hp : Hl <+: Hm) :
    histOkM σ Hm := by
  refine ⟨Nat.le_trans hh.1 hp.length_le, fun r hr => ?_⟩
  obtain ⟨e, he, hok⟩ := hh.2 r hr
  refine ⟨e, prefix_getElem? hp he, hok.1, fun h1 => ?_⟩
  obtain ⟨e', he', heq⟩ := hok.2 h1
  exact ⟨e', prefix_getElem? hp he', heq⟩

/-- **The `k`-th event of a response** for its watcher, whose received events are its expected
changes `E` made events: the expected change after those received before it and its `k` first. -/
theorem recv_ev_get {rs : List WResp} {r : WResp} {E : List (Nat × change)} {k : Nat} {ev : EvM}
    (hE : recvEvs (rs ++ [r]) r.id = E.map fun p => chEv p.1 p.2) (hk : r.evs[k]? = some ev) :
    ∃ p, E[(recvEvs rs r.id).length + k]? = some p ∧ ev = chEv p.1 p.2 := by
  rw [recvEvs_snoc] at hE
  simp only [↓reduceIte] at hE
  have h : (recvEvs rs r.id ++ r.evs)[(recvEvs rs r.id).length + k]? = some ev := by
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hk
  rw [hE, List.getElem?_map] at h
  cases hp : E[(recvEvs rs r.id).length + k]? with
  | none => rw [hp] at h; cases h
  | some p => rw [hp] at h; exact ⟨p, rfl, (Option.some.inj h).symm⟩

/-- A response's events are all for its watcher: the others' received events do not change. -/
theorem recvEvs_snoc_ne (rs : List WResp) (r : WResp) (id : w64) (h : r.id ≠ id ∨ r.evs = []) :
    recvEvs (rs ++ [r]) id = recvEvs rs id := by
  rw [recvEvs_snoc]
  rcases h with h | h
  · simp [h]
  · simp [h]

theorem advW_key (wv : watcher) (r : w64) : (advW wv r).key' = wv.key' := by
  unfold advW; split <;> rfl

theorem advW_end (wv : watcher) (r : w64) : (advW wv r).end' = wv.end' := by
  unfold advW; split <;> rfl

/-- **A watcher's position after `advance`** past `expect`'s change at revision `p.1`, a revision of
the history. -/
theorem wPosOk_adv (Hl : List HRev) (ri : RegInfo) (wv : watcher) (n : Nat) (p : Nat × change)
    (h : wPosOk Hl ri wv.rev' wv.index' n)
    (hn : expNext Hl (regInR ri) (sint.nat wv.rev') (sint.nat wv.index') (p.1 : Int) = some p)
    (hr : p.1 < Hl.length) (hr2 : p.1 < 2 ^ 63)
    (hlen : (rangeChs Hl (regInR ri) p.1).length < 2 ^ 63) :
    wPosOk Hl ri (advW wv (W64 (p.1 : Int))).rev' (advW wv (W64 (p.1 : Int))).index' (n + 1) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  have ha := posOk_advW Hl (regInR ri) (regLo ri) n (p.1 : Int) wv p.1 p.2 h1 h2 h3 hn hr2 hlen
  refine ⟨ha.1, ha.2.1, ha.2.2, Or.inl ?_⟩
  have hle := (expNext_some hn).1
  have hrN : sint.nat (W64 (p.1 : Int)) = p.1 := by word
  unfold advW
  split
  · simp only; rw [hrN]; exact hr
  · simp only; omega

/-- **Every response with events was for a registered watcher** (`receive` checks it under
`c.mu`): so a watcher registered later has received nothing before (`recvEvs_fresh`). -/
def rcvKnown (rs : List WResp) (W : GMap w64 (Loc × RegInfo)) : Prop :=
  ∀ r ∈ rs, r.evs ≠ [] → (W !! r.id).isSome

theorem recvEvs_fresh {rs : List WResp} {W : GMap w64 (Loc × RegInfo)} (h : rcvKnown rs W)
    {id : w64} (hid : W !! id = none) : recvEvs rs id = [] := by
  unfold recvEvs
  rw [List.flatten_eq_nil_iff]
  intro l hl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hl
  obtain ⟨hr, hri⟩ := List.mem_filter.1 hr
  simp only [decide_eq_true_eq] at hri
  by_cases hne : r.evs = []
  · exact hne
  · have := h r hr hne
    rw [hri, hid] at this
    cases this


theorem rcvKnown_insert {rs : List WResp} {W : GMap w64 (Loc × RegInfo)} (h : rcvKnown rs W)
    (id : w64) (x : Loc × RegInfo) : rcvKnown rs (<[id := x]> W) := by
  intro r hr hne
  by_cases he : r.id = id
  · rw [he, GMap.lookup_insert]; rfl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]; exact h r hr hne

end model

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A field of the watch check's struct. -/
abbrev cF (f : GoString) (c : Loc) : Loc := structFieldRef watchCheck f c

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A registered watcher under `c.mu`** (see the file header), after the responses `rs`. -/
def watcherOwn (Hl : List HRev) (rs : List WResp) (id : w64) (wp : Loc) (ri : RegInfo) : IProp GF :=
  iprop(∃ wv : watcher, wp ↦ wv ∗ wv.key' ↦*□ ri.1 ∗ wv.end' ↦*□ ri.2.1 ∗
    ⌜ri.2.2.1 = decide (wv.end' = slice.nil) ∧ ri.1 ≠ [] ∧ 1 ≤ sint.Z ri.2.2.2 ∧
      sint.Z ri.2.2.2 < 2 ^ 63 - 1 ∧ wPosOk Hl ri wv.rev' wv.index' (recvEvs rs id).length⌝)

/-- **`c.mu`'s invariant** (see the file header). -/
def cmuInv (wm : GoMap) (γ : RandNames) : IProp GF :=
  iprop(∃ (rs : List WResp) (W : GMap w64 (Loc × RegInfo)) (Hl : List HRev),
    wm ↦$ W.fmap Prod.fst ∗ ghostMapAuth γ.reg (1 : Qp).half W ∗ ghostVar γ.rcv (1 : Qp).half rs ∗
    monoListLbOwn γ.h.l Hl ∗ ⌜rcvKnown rs W⌝ ∗ [∗map] id ↦ x ∈ W, watcherOwn Hl rs id x.1 x.2)

/-- **The watch check's handles** (persistent; see the file header). -/
def wcCtx (c : Loc) (γ : RandNames) (h : Loc) (wm : GoMap) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
    cF go!"h" c ↦□ h ∗ cF go!"watchers" c ↦□ wm ∗
    sync.isMutex (GF := GF) (cF go!"mu" c) (cmuInv wm γ) ∗
    inv worldN (worldInv h γ) ∗ isHistory h γ.h ∗
    ∃ (ws kv : GoInterface), isMvccWatchStream ws γ.kv γ.ws ∗ isMvcc kv γ.kv)

/-- **The receiver's facts at the tester's invariant**: at its state, mvcc's watch guarantee of the
responses received (`wsRecv_ok.law`), the history covering the notified log, no compaction, the
registry (`regOk`), the notified log well-formed and small. -/
theorem recv_facts (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hrok : mvcc.api.wsRecv_ok.law (GF := GF) (hG := hG))
    (h : Loc) (γ : RandNames) (ws kv : GoInterface) (rs : List WResp)
    (W : GMap w64 (Loc × RegInfo)) :
    inv worldN (worldInv h γ) ∗ isMvccWatchStream ws γ.kv γ.ws ∗ isMvcc kv γ.kv ∗
        wsRecv γ.ws rs ∗ ghostMapAuth γ.reg (1 : Qp).half W ⊢
      |={⊤}=> wsRecv γ.ws rs ∗ ghostMapAuth γ.reg (1 : Qp).half W ∗
        ∃ (σ : MvccState) (S : StreamState) (Hlw : List HRev), monoListLbOwn γ.h.l Hlw ∗
          ⌜wsRecvOk σ S rs ∧ histOkM σ Hlw ∧ σ.crev = -1 ∧ regOk S W ∧
            LogWf' σ.notifiedLog ∧ σ.notifiedLog.length < 2 ^ 63⌝ := by
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
  haveI := hpers.1 kv γ.kv
  haveI := hpers.2.1 ws γ.kv γ.ws
  haveI : Timeless (worldInv (GF := GF) h γ) := by unfold worldInv; infer_instance
  iintro ⟨#Hinv, #Hws, #Hkv, Hrcv, Hreg⟩
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p, %Hl, %W', Hσ, Hgσ, HS, Hreg', Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  ihave %HW := ghostMapAuth_agree γ.reg _ _ _ _ $$ Hreg' Hreg
  subst HW
  icases HS with ⟨HS, HScl⟩
  ihave %Hro := hrok ws γ.kv γ.ws rs S σ $$ [$Hws $Hrcv $HS $Hσ]
  ihave %Hr := hreach kv γ.kv σ $$ [$Hkv $Hσ]
  have hwf := (reach_logWf.law_holds σ Hr.1).2
  have hnl : σ.notifiedLog.length < 2 ^ 63 := by
    have := Hr.2
    unfold MvccState.notifiedLog; split <;> simp <;> omega
  imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
  · inext; iunfold worldInv; iexists σ, S, p, Hl, W'; iframe; iframe #; ipureintro; exact Hok
  imodintro
  iframe Hrcv Hreg
  iexists σ, S, Hl
  iframe Hlb
  ipureintro
  exact ⟨Hro, Hok.2.2.2.1, Hok.1, Hok.2.2.2.2, hwf, hnl⟩

theorem register_closed (S : StreamState) (id : w64) (w : WInfo) :
    (S.register id w).closed = S.closed := rfl

theorem worldN_mask_wl : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN := by
  unfold worldN mvccN
  intro p hp
  rw [Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide : "mvccrand" ≠ "mvcc") p
    ⟨nclose_subseteq _ _ p hp, h'⟩⟩

/-- **What `register`'s update gives back** at a registration of `wp`: the stream open, the
registrar's half of `γ.cl`, and the lock's half of the registry with the new watcher (a fresh id). -/
def regQ (γ : RandNames) (W : GMap w64 (Loc × RegInfo)) (wp : Loc) (kk e : GoString)
    (endk : GoSlice) (st : w64) (_ : MvccState) (S : StreamState) (id : w64) : IProp GF :=
  iprop(⌜S.closed = false ∧ W !! id = none⌝ ∗ ghostVar γ.cl (1 : Qp).half false ∗
    ghostMapAuth γ.reg (1 : Qp).half (<[id := (wp, (kk, e, decide (endk = slice.nil), st))]> W))

/-- **`register`'s update for a range not empty**: at the invariant, the stream open (the
registrar's half of `γ.cl`), the new watcher in the registry (both halves, `regOk_register`). -/
theorem register_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (h : Loc)
    (γ : RandNames) (W : GMap w64 (Loc × RegInfo)) (wp : Loc) (kk e : GoString) (endk : GoSlice)
    (st : w64) (hst : 1 ≤ sint.Z st) :
    inv worldN (worldInv h γ) ∗ ghostMapAuth γ.reg (1 : Qp).half W ∗
        ghostVar γ.cl (1 : Qp).half false ⊢
      AU <{ ∃∃ (σ : MvccState) (S : StreamState), mvccState γ.kv σ ∗ wsState γ.ws S }>
        @ ⊤ \ ↑mvccN, ∅
      <{ ∀∀ (id : w64) (k : Nat), mvccState γ.kv σ ∗
          (if S.closed then ⌜id = W64 (-1)⌝ ∗ wsState γ.ws S
           else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ wsSentLb γ.ws k ∗
             wsState γ.ws (S.register id
               ⟨watchRangeOf kk e endk st id, [], watchLo σ st, k, true⟩)),
        COMM regQ γ W wp kk e endk st σ S id }> := by
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  have Hm := worldN_mask_wl
  iintro ⟨#Hinv, Hreg, Hcl⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p, %Hl, %W', Hσ, Hgσ, ⟨HS, HScl⟩, Hreg', Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  ihave %HW := ghostMapAuth_agree γ.reg _ _ _ _ $$ Hreg' Hreg
  subst HW
  ihave %Hc := ghostVar_agree γ.cl _ _ _ _ $$ HScl Hcl
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ, S
  iframe Hσ HS
  isplit
  · iintro ⟨Hσ, HS⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W'; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iframe
  · iintro %id %k ⟨Hσ, HS⟩
    rw [Hc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases HS with ⟨%Hfresh, -, HS⟩
    have hlo : watchLo σ st = sint.nat st := by
      unfold watchLo
      have : st ≠ W64 0 := by intro h0; rw [h0] at hst; simp at hst
      rw [if_neg this]
    obtain ⟨hW, hreg'⟩ := regOk_register S W' Hok.2.2.2.2 id Hfresh.1 wp kk e
      (decide (endk = slice.nil)) st ⟨watchRangeOf kk e endk st id, [], watchLo σ st, k, true⟩
      (rg_eq kk e endk _ st id rfl).symm rfl hlo rfl
    ihave Hfull := (ghostMapAuth_halves γ.reg W').2 $$ [$Hreg' $Hreg]
    imod ghost_map_insert id (wp, (kk, e, decide (endk = slice.nil), st)) hW $$ Hfull
      with ⟨Hfull, -⟩
    icases (ghostMapAuth_halves γ.reg _).1 $$ Hfull with ⟨Hreg', Hreg⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
    · inext; iunfold worldInv
      iexists σ, S.register id ⟨watchRangeOf kk e endk st id, [], watchLo σ st, k, true⟩, p, Hl,
        <[id := (wp, (kk, e, decide (endk = slice.nil), st))]> W'
      iframe; iframe #
      rw [register_closed, Hc]
      iframe
      ipureintro
      exact ⟨Hok.1, Hok.2.1, Hok.2.2.1, Hok.2.2.2.1, hreg'⟩
    imodintro
    iunfold regQ
    iframe
    ipureintro; exact ⟨Hc, hW⟩

/-- **`register`'s update for an empty range** (which `Watch` never commits, but whose update is
given): no resource; a registration of the range keeps the registry the stream's
(`regOk_register_empty`). -/
theorem register_au_empty (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (h : Loc)
    (γ : RandNames) (kk e : GoString) (endk : GoSlice) (st : w64)
    (hcov : ∀ id k, (watchRangeOf kk e endk st id).covers k = false) :
    (inv worldN (worldInv (GF := GF) h γ) : IProp GF) ⊢
      AU <{ ∃∃ (σ : MvccState) (S : StreamState), mvccState γ.kv σ ∗ wsState γ.ws S }>
        @ ⊤ \ ↑mvccN, ∅
      <{ ∀∀ (id : w64) (k : Nat), mvccState γ.kv σ ∗
          (if S.closed then ⌜id = W64 (-1)⌝ ∗ wsState γ.ws S
           else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ wsSentLb γ.ws k ∗
             wsState γ.ws (S.register id
               ⟨watchRangeOf kk e endk st id, [], watchLo σ st, k, true⟩)),
        COMM (fun _ _ _ => iprop(True)) σ S id }> := by
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  have Hm := worldN_mask_wl
  iintro #Hinv
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p, %Hl, %W', Hσ, Hgσ, ⟨HS, HScl⟩, Hreg', Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ, S
  iframe Hσ HS
  isplit
  · iintro ⟨Hσ, HS⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W'; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iempintro
  · iintro %id %k ⟨Hσ, HS⟩
    by_cases hcl : S.closed = true
    rotate_left
    · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
      icases HS with ⟨%Hfresh, -, HS⟩
      have hreg' := regOk_register_empty S W' Hok.2.2.2.2 id Hfresh.1
        ⟨watchRangeOf kk e endk st id, [], watchLo σ st, k, true⟩ (hcov id)
      imod Hclose2 with -
      imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
      · inext; iunfold worldInv
        iexists σ, S.register id ⟨watchRangeOf kk e endk st id, [], watchLo σ st, k, true⟩, p,
          Hl, W'
        iframe; iframe #
        rw [register_closed]
        simp only [hcl]
        iframe
        ipureintro
        exact ⟨Hok.1, Hok.2.1, Hok.2.2.1, Hok.2.2.2.1, hreg'⟩
      imodintro
      itrivial
    · simp only [hcl, ↓reduceIte]
      icases HS with ⟨-, HS⟩
      imod Hclose2 with -
      imod Hclose $$ [Hσ Hgσ HS HScl Hreg' Hpub Hpv Hpm] with -
      · inext; iunfold worldInv; iexists σ, S, p, Hl, W'; simp only [hcl]; iframe; iframe #
        ipureintro; exact Hok
      imodintro
      itrivial

/-- **A tick is a small revision**: at most the store's revision, which the reachable store keeps
below `2 ^ 63 - 3`. -/
theorem tick_bound (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (kv : GoInterface) (h : Loc) (γ : RandNames) (n : Nat) :
    inv worldN (worldInv h γ) ∗ isMvcc kv γ.kv ∗ monoNatLbOwn γ.pub n ⊢ |={⊤}=> ⌜n + 4 ≤ 2 ^ 63⌝ := by
  haveI := hpers.1 kv γ.kv
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  iintro ⟨#Hinv, #Hkv, #Hn⟩
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p, %Hl, %W', Hσ, Hgσ, HS, Hreg', Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  ihave %Hle := monoNatLbOwn_valid γ.pub 1 (sint.nat p) n $$ Hpm Hn
  icases (persistent_entails_right (hreach kv γ.kv σ)) $$ [$Hkv $Hσ] with ⟨%Hr, -, Hσ⟩
  imod Hclose $$ [Hσ Hgσ HS Hreg' Hpub Hpv Hpm] with -
  · inext; iunfold worldInv; iexists σ, S, p, Hl, W'; iframe; iframe #; ipureintro; exact Hok
  imodintro
  ipureintro
  have h1 := Hok.2.2.1
  have h2 := Hr.2
  unfold MvccState.rev at h1
  omega

/-- A watcher's ownership at a longer lower bound and responses that carried nothing for it. -/
theorem watcherOwn_frame {Hl Hm : List HRev} (hp : Hl <+: Hm) {rs rs' : List WResp} {id : w64}
    (hs : recvEvs rs' id = recvEvs rs id) (wp : Loc) (ri : RegInfo) :
    watcherOwn (GF := GF) Hl rs id wp ri ⊢ watcherOwn Hm rs' id wp ri := by
  unfold watcherOwn
  iintro ⟨%wv, Hw, #Hk, #He, %H⟩
  iexists wv
  iframe
  iframe #
  ipureintro
  rw [hs]
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, wPosOk_prefix hp _ _ _ _ H.2.2.2.2⟩

/-- Every watcher, when the responses carried nothing for any. -/
theorem wats_frame {Hl Hm : List HRev} (hp : Hl <+: Hm) {rs rs' : List WResp}
    (W : GMap w64 (Loc × RegInfo)) (hs : ∀ id, recvEvs rs' id = recvEvs rs id) :
    ([∗map] id ↦ x ∈ W, watcherOwn (GF := GF) Hl rs id x.1 x.2) ⊢
      [∗map] id ↦ x ∈ W, watcherOwn (GF := GF) Hm rs' id x.1 x.2 :=
  BigSepM.bigSepM_mono_of_forall fun {id x} => watcherOwn_frame hp (hs id) x.1 x.2

/-- One watcher out of the lock's map, the others framed to the longer bound and responses. -/
theorem wats_take {Hl Hm : List HRev} (hp : Hl <+: Hm) {rs rs' : List WResp}
    (W : GMap w64 (Loc × RegInfo)) (i : w64) (x : Loc × RegInfo) (hW : W !! i = some x)
    (hs : ∀ id, id ≠ i → recvEvs rs' id = recvEvs rs id) :
    ([∗map] id ↦ x ∈ W, watcherOwn (GF := GF) Hl rs id x.1 x.2) ⊢
      watcherOwn Hl rs i x.1 x.2 ∗
        (watcherOwn Hm rs' i x.1 x.2 -∗ [∗map] id ↦ x ∈ W, watcherOwn (GF := GF) Hm rs' id x.1 x.2) := by
  iintro H
  icases (BigSepM.bigSepM_lookup_acc_impl
    (Φ := fun (id : w64) (x : Loc × RegInfo) => watcherOwn (GF := GF) Hl rs id x.1 x.2) (m := W)
    hW) $$ H with ⟨Hi, Hrest⟩
  iframe Hi
  iintro Hi'
  iapply Hrest $$ %(fun (id : w64) (x : Loc × RegInfo) => watcherOwn (GF := GF) Hm rs' id x.1 x.2) [] Hi'
  imodintro
  iintro %k %v %_ %hk Hk
  iapply watcherOwn_frame hp (hs k hk) $$ Hk

end defs

end mvccrand
end EtcdGrove
end Perennial
