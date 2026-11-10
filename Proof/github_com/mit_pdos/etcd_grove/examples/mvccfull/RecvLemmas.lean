/-
The receiver's lemmas (`stream.receive`, `Streams.lean`'s vocabulary). Lean-first (no Rocq
counterpart); mvccrand's `WatchLock.lean` (`recvEvs_snoc`, `rg_eq`, `recv_exp`, `recv_prog`,
`recv_ev_get`, `wats_take`), with the watchers' filters, the floating window and compaction.

- The events received (`recvEvs_snoc`, `recvEvs_snoc_ne`, `recv_ev_get`).
- What a registered watcher has received (`recv_exp'`, `wsRecvOk`'s clause 2) and its progress
  (`recv_prog'`, clause 3, the watcher's own or the stream's `-1`): its expected changes
  (`expChs` at its `Reg.mt`), made events.
- The position (`wPosOk'`): moved to a longer bound of the history (`wPosOk'_prefix`); nothing more
  expected after a progress (`covered_none`); a floating watcher anchored at its first event
  (`float_anchor`).
- `watcherOk` and `watcherOwn'` at one more response that carried nothing for the watcher
  (`watcherOk_frame`, `wats_frame'`, `wats_take'`).
- `recv_facts'`: `Streams.lean`'s `recv_facts`, proved (`memberInv_live`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StreamLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- The events the responses carried for `id`, one more response. -/
theorem recvEvs_snoc (rs : List WResp) (r : WResp) (id : w64) :
    recvEvs (rs ++ [r]) id = recvEvs rs id ++ (if r.id = id then r.evs else []) := by
  unfold recvEvs
  rw [List.filter_append]
  by_cases h : r.id = id <;> simp [h]

/-- A response for another watcher, or without events, carries nothing for `id`. -/
theorem recvEvs_snoc_ne (rs : List WResp) (r : WResp) (id : w64) (h : r.id ≠ id ∨ r.evs = []) :
    recvEvs (rs ++ [r]) id = recvEvs rs id := by
  rw [recvEvs_snoc]
  rcases h with h | h
  · simp [h]
  · simp [h]

/-- A registered watcher's range is its registration's (`regOk'`'s form, `watchRangeOf`'s). -/
theorem rg_eq (kk e : GoString) (endk : GoSlice) (en : Bool) (st id : w64)
    (hen : en = decide (endk = slice.nil)) :
    (⟨kk, if en then none else some e, st, id⟩ : WatchRange) = watchRangeOf kk e endk st id := by
  subst hen; unfold watchRangeOf; by_cases h : endk = slice.nil <;> simp [h]

/-- The expected changes of a registration at its watcher's end slice. -/
theorem Reg.mt_eq (x : Reg) (endk : GoSlice) (hen : x.endNil = decide (endk = slice.nil)) :
    x.mt = matchesM x.filter (decide (endk = slice.nil)) x.key x.e := by
  unfold Reg.mt; rw [hen]

/-- **What a registered watcher has received** (`wsRecvOk`'s clause 2, `onceUpTo` from
`onceUpToAll`): its expected changes from its first revision, up to some revision of the notified
log. -/
theorem recv_exp' (ks : List GoString) (σ : MvccState) (S : StreamState) (rs : List WResp)
    (Hl : List HRev) (hok : wsRecvOk σ S rs) (hh : histOkM ks σ Hl)
    (honce : ∀ lo, onceUpTo σ.notifiedLog lo σ.crev)
    (hwf : LogWf' σ.notifiedLog) (hlen : σ.notifiedLog.length < 2 ^ 63)
    (id : w64) (x : Reg) (wi : WInfo) (hS : S.ws !! id = some wi)
    (hrg : wi.rg = ⟨x.key, if x.endNil then none else some x.e, x.start, id⟩)
    (hfs : wi.fs = filterFs x.filter) (hlo : wi.lo = x.lo) (endk : GoSlice)
    (hen : x.endNil = decide (endk = slice.nil)) (hkk : x.key ≠ []) (hlo1 : 1 ≤ x.lo) :
    ∃ hi, hi ≤ σ.notifiedLog.length ∧
      recvEvs rs id = (expChs Hl x.mt x.lo hi).map fun p => chEv p.1 p.2 := by
  obtain ⟨hi, hhi, heq⟩ := hok.2.1 id wi hS (honce _)
  refine ⟨hi, hhi, ?_⟩
  rw [heq, hfs, hrg, hlo, rg_eq x.key x.e endk x.endNil x.start id hen, Reg.mt_eq x endk hen]
  exact watchEvents_filtered_eq_expChs ks σ Hl hh hwf hlen x.filter x.key x.e endk x.start id hkk
    x.lo hi hlo1 hhi

/-- **A progress response for a registered watcher** (`wsRecvOk`'s clause 3: its own, or the
stream's `-1` when it is live and registered before): what it has received up to the response is
its expected changes up to the response's revision. -/
theorem recv_prog' (ks : List GoString) (σ : MvccState) (S : StreamState) (rs : List WResp)
    (Hl : List HRev) (hok : wsRecvOk σ S rs) (hh : histOkM ks σ Hl)
    (honce : ∀ lo, onceUpTo σ.notifiedLog lo σ.crev)
    (hwf : LogWf' σ.notifiedLog) (hlen : σ.notifiedLog.length < 2 ^ 63)
    (j : Nat) (r : WResp) (hj : rs[j]? = some r) (hev : r.evs = []) (hcr : r.compactRev = W64 0)
    (id : w64) (x : Reg) (wi : WInfo) (hS : S.ws !! id = some wi)
    (hrg : wi.rg = ⟨x.key, if x.endNil then none else some x.e, x.start, id⟩)
    (hfs : wi.fs = filterFs x.filter) (hlo : wi.lo = x.lo) (endk : GoSlice)
    (hen : x.endNil = decide (endk = slice.nil)) (hkk : x.key ≠ []) (hlo1 : 1 ≤ x.lo)
    (hwho : r.id = id ∨ (r.id = W64 (-1) ∧ wi.live = true ∧ wi.k ≤ j)) :
    recvEvs (rs.take (j + 1)) id =
      (expChs Hl x.mt x.lo (sint.nat r.rev + 1)).map fun p => chEv p.1 p.2 := by
  have h1 := (hok.1 r (List.mem_of_getElem? hj)).2.2.1 hcr
  rw [hok.2.2.1 j r id wi hj hev hcr hS (honce _) hwho, hfs, hrg, hlo,
    rg_eq x.key x.e endk x.endNil x.start id hen, Reg.mt_eq x endk hen]
  exact watchEvents_filtered_eq_expChs ks σ Hl hh hwf hlen x.filter x.key x.e endk x.start id hkk
    x.lo _ hlo1 (by omega)

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

/-- The eventless revision, one more response. -/
theorem eventlessOk_snoc {rs : List WResp} {P : w64} (r : WResp) (h : eventlessOk rs P) :
    eventlessOk (rs ++ [r]) P := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with h0 | ⟨i, y, hy, h1, h2, h3⟩
  · exact Or.inl h0
  · have hi : i < rs.length := (List.getElem?_eq_some_iff.1 hy).1
    exact Or.inr ⟨i, y, by rw [List.getElem?_append_left hi]; exact hy, h1, h2, h3⟩

/-- A longer lower bound of the history still covers the notified history. -/
theorem histOkM_prefix {ks : List GoString} {σ : MvccState} {Hl Hm : List HRev}
    (hh : histOkM ks σ Hl) (hp : Hl <+: Hm) : histOkM ks σ Hm := by
  refine ⟨Nat.le_trans hh.1 hp.length_le, fun r hr => ?_⟩
  obtain ⟨e, he, hok⟩ := hh.2 r hr
  refine ⟨e, prefix_getElem? hp he, hok.1, fun h1 => ?_⟩
  obtain ⟨e', he', heq⟩ := hok.2 h1
  exact ⟨e', prefix_getElem? hp he', heq⟩

/-- A position stays valid at a longer lower bound of the history. -/
theorem wPosOk'_prefix {Hl Hm : List HRev} (hp : Hl <+: Hm) (mt : change → Bool) (lo : Nat)
    (wv : watcher) (n : Nat) (h : wPosOk' Hl mt lo wv n) : wPosOk' Hm mt lo wv n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  split
  · rename_i hf; simp only [hf, ↓reduceIte] at h5; exact h5
  · rename_i hf
    simp only [hf, ↓reduceIte] at h5
    obtain ⟨h6, h7⟩ := h5
    refine ⟨?_, ?_⟩
    · rcases h7 with h7 | ⟨h7, h8, h9⟩
      · exact (posOk_prefix hp _ h7).1 h6
      · rw [h7, h8, h9]; exact posOk_start _ _ _
    · rcases h7 with h7 | h7
      · exact Or.inl (Nat.lt_of_lt_of_le h7 hp.length_le)
      · exact Or.inr h7

/-- **A watcher's registration at one more response** that carried nothing for it, at a longer
lower bound of the history. -/
theorem watcherOk_frame {Hl Hm : List HRev} (hp : Hl <+: Hm) (rs : List WResp) (r : WResp)
    (id : w64) (x : Reg) (wv : watcher) (hs : recvEvs (rs ++ [r]) id = recvEvs rs id)
    (h : watcherOk Hl rs id x wv) : watcherOk Hm (rs ++ [r]) id x wv := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, ?_, ?_⟩
  · intro hs'; have := h12 hs'; simp; omega
  · intro hc; obtain ⟨y, hy, hy2⟩ := h13 hc; exact ⟨y, List.mem_append_left _ hy, hy2⟩
  · rw [hs]; exact wPosOk'_prefix hp _ _ _ _ h14

/-- **A floating watcher expects nothing up to `upto`** when no expected change is in `[lo, upto]`:
`expect` from any revision at least `lo`, at index `0`. -/
theorem expNext_float_none (Hl : List HRev) (mt : change → Bool) (lo rev : Nat) (upto : Int)
    (hlo : 1 ≤ lo) (hle : lo ≤ rev) (he : expChs Hl mt lo (upto.toNat + 1) = []) :
    expNext Hl mt rev 0 upto = none := by
  by_cases hu : upto < rev
  · unfold expNext; simp [hu]
  · have hp : posOk Hl mt lo rev 0 0 := by
      refine ⟨hle, Nat.zero_le _, ?_⟩
      have := expChs_append Hl mt hle (show rev ≤ upto.toNat + 1 by omega)
      rw [he] at this
      have h2 := congrArg List.length this
      simp only [List.length_nil, List.length_append] at h2
      omega
    exact expNext_none_of_length Hl mt lo rev 0 0 upto hlo hp (by rw [he]; simp)

/-- **Nothing more expected after a progress** (`covered`'s premise): when the expected changes up to
`p` are at most the `n` received, `expect` from the watcher's position returns none (floating or
not). -/
theorem covered_none (Hl : List HRev) (mt : change → Bool) (lo : Nat) (wv : watcher) (n : Nat)
    (p : Int) (hlo : 1 ≤ lo) (h : wPosOk' Hl mt lo wv n)
    (hn : (expChs Hl mt lo (p.toNat + 1)).length ≤ n) :
    expNext Hl mt (sint.nat wv.rev') (sint.nat wv.index') p = none := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  split at h5
  · obtain ⟨rfl, hi, -, hle⟩ := h5
    rw [hi]
    have hi0 : sint.nat (W64 0) = 0 := rfl
    rw [hi0]
    refine expNext_float_none Hl mt lo _ p hlo ?_ ?_
    · have : sint.nat wv.rev' = (sint.Z wv.rev').toNat := rfl; omega
    · exact List.eq_nil_of_length_eq_zero (by omega)
  · exact expNext_none_of_length Hl mt lo _ _ n p hlo h5.1 hn

/-- **A floating watcher anchored at its first event** `p` (the first expected change, at a
revision at least `lo`): `receive` moves its revision down to `p`'s when below it, at index `0`
(`floatLo` cleared); from there `expect` at `p`'s revision returns `p`. -/
theorem float_anchor (Hl : List HRev) (mt : change → Bool) (lo hi rev : Nat) (p : Nat × change)
    (hlo : 1 ≤ lo) (hle : lo ≤ rev) (hp : (expChs Hl mt lo hi)[0]? = some p) :
    posOk Hl mt lo (if p.1 < rev then p.1 else rev) 0 0 ∧
      expNext Hl mt (if p.1 < rev then p.1 else rev) 0 (p.1 : Int) = some p := by
  have hm := mem_expChs (List.mem_of_getElem? hp)
  have hpos : posOk Hl mt lo (if p.1 < rev then p.1 else rev) 0 0 := by
    refine ⟨by split <;> omega, Nat.zero_le _, ?_⟩
    have hr : (if p.1 < rev then p.1 else rev) ≤ p.1 := by split <;> omega
    have hsplit := expChs_append Hl mt (show lo ≤ (if p.1 < rev then p.1 else rev) by split <;> omega)
      (show (if p.1 < rev then p.1 else rev) ≤ hi by omega)
    cases hc : expChs Hl mt lo (if p.1 < rev then p.1 else rev) with
    | nil => rfl
    | cons q qs =>
      exfalso
      rw [hsplit, hc] at hp
      simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hp
      have hq := mem_expChs (show q ∈ expChs Hl mt lo (if p.1 < rev then p.1 else rev) by
        rw [hc]; simp)
      rw [hp] at hq
      omega
  refine ⟨hpos, ?_⟩
  obtain ⟨r, ch⟩ := p
  exact expNext_of_get Hl mt lo _ 0 0 hi r ch hlo hpos hp

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A watcher's ownership at one more response that carried nothing for it, and a longer bound. -/
theorem watcherOwn'_frame {Hl Hm : List HRev} (hp : Hl <+: Hm) (rs : List WResp) (r : WResp)
    (ws : WsName) (id : w64) (x : Reg) (hs : recvEvs (rs ++ [r]) id = recvEvs rs id) :
    watcherOwn' (GF := GF) Hl rs ws id x ⊢ watcherOwn' Hm (rs ++ [r]) ws id x := by
  unfold watcherOwn'
  iintro ⟨%wv, Hw, #Hk, #He, Hlb, %H⟩
  iexists wv
  iframe
  iframe #
  ipureintro
  exact watcherOk_frame hp rs r id x wv hs H

/-- Every watcher, when the response carried nothing for any. -/
theorem wats_frame' {Hl Hm : List HRev} (hp : Hl <+: Hm) (rs : List WResp) (r : WResp)
    (ws : WsName) (W : GMap w64 Reg) (hs : ∀ id, recvEvs (rs ++ [r]) id = recvEvs rs id) :
    ([∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hl rs ws id x) ⊢
      [∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hm (rs ++ [r]) ws id x :=
  BigSepM.bigSepM_mono_of_forall fun {id x} => watcherOwn'_frame hp rs r ws id x (hs id)

/-- One watcher out of the lock's map, the others framed to the longer bound and one more
response. -/
theorem wats_take' {Hl Hm : List HRev} (hp : Hl <+: Hm) (rs : List WResp) (r : WResp)
    (ws : WsName) (W : GMap w64 Reg) (i : w64) (x : Reg) (hW : W !! i = some x)
    (hs : ∀ id, id ≠ i → recvEvs (rs ++ [r]) id = recvEvs rs id) :
    ([∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hl rs ws id x) ⊢
      watcherOwn' Hl rs ws i x ∗
        (watcherOwn' Hm (rs ++ [r]) ws i x -∗
          [∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hm (rs ++ [r]) ws id x) := by
  iintro H
  icases (BigSepM.bigSepM_lookup_acc_impl
    (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs ws id x) (m := W)
    hW) $$ H with ⟨Hi, Hrest⟩
  iframe Hi
  iintro Hi'
  iapply Hrest $$ %(fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hm (rs ++ [r]) ws id x)
    [] Hi'
  imodintro
  iintro %k %v %_ %hk Hk
  iapply watcherOwn'_frame hp rs r ws k v (hs k hk) $$ Hk

/-- **The registrations' pure facts**, out of the lock's watchers: each registration's key is not
empty, and its first revision positive and small. -/
theorem wats_regs (Hl : List HRev) (rs : List WResp) (ws : WsName) (W : GMap w64 Reg) :
    ([∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hl rs ws id x) ⊢
      ([∗map] id ↦ x ∈ W, watcherOwn' (GF := GF) Hl rs ws id x) ∗
        ⌜∀ id x, W !! id = some x → x.key ≠ [] ∧ 1 ≤ x.lo ∧ x.lo < 2 ^ 63 - 1⌝ := by
  iintro H
  ihave H := (BigSepM.bigSepM_mono (Φ := fun id x => watcherOwn' (GF := GF) Hl rs ws id x)
    (Ψ := fun id (x : Reg) => iprop(watcherOwn' (GF := GF) Hl rs ws id x ∗
      ⌜x.key ≠ [] ∧ 1 ≤ x.lo ∧ x.lo < 2 ^ 63 - 1⌝)) (m := W) (fun {id x} _ => by
        unfold watcherOwn'
        iintro ⟨%wv, Hw, Hk, He, Hlb, %H⟩
        isplitl
        · iexists wv; iframe; ipureintro; exact H
        · ipureintro; exact ⟨H.2.1, H.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.1⟩)) $$ H
  rw [BigSepM.bigSepM_sep_eq]
  icases H with ⟨H, Hp⟩
  ihave %Hp := BigSepM.bigSepM_pure_intro $$ Hp
  iframe H
  ipureintro
  exact fun id x hx => Hp id x hx

/-- An authority keeps itself and gives its lower bound. -/
theorem monoNat_auth_lb (γ : GName) (q : Qp) (n : Nat) :
    monoNatAuthOwn (GF := GF) γ q n ⊢ monoNatLbOwn γ n ∗ monoNatAuthOwn γ q n :=
  persistent_entails_right (by iintro H; iapply (monoNatLbOwn_get γ q n) $$ H)

/-- The streams' invariants are apart from the members'. -/
theorem streamN_memberN (i : Nat) : (↑streamN : CoPset) ⊆ ⊤ \ ↑(memberN i) := by
  unfold streamN memberN
  intro p hp
  rw [Std.LawfulSet.mem_diff]
  have h1 := nclose_subseteq ((nroot .@ "mvccfull") .@ "member") (toString i)
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  exact ndot_ne_disjoint (nroot .@ "mvccfull") (by decide : "stream" ≠ "member") p
    ⟨hp, h1 p h'⟩

/-- **`recv_facts`** (`Streams.lean`), proved: the incarnation's invariant opened with the live
share (`memberInv_live`), then the stream's. -/
theorem recv_facts' (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hrok : mvcc.api.wsRecv_ok.law (GF := GF) (hG := hG))
    (T : Strm) (q : Qp) (rs : List WResp) (W : GMap w64 Reg) :
    epLive T.ep q ∗ inv streamN (streamInv T.σs) ∗ isMvccWatchStream T.ws T.ep.ι.kv T.σs.ws ∗
        wsRecv T.σs.ws rs ∗ ghostMapAuth T.σs.reg (1 : Qp).half W ⊢
      |={⊤}=> epLive T.ep q ∗ wsRecv T.σs.ws rs ∗ ghostMapAuth T.σs.reg (1 : Qp).half W ∗
        ∃ (σ : MvccState) (S : StreamState) (C : List w64), readQ T.ep.ks T.ep.γh T.ep.m σ ∗
          ⌜wsRecvOk σ S rs ∧ (∀ lo, onceUpTo σ.notifiedLog lo σ.crev) ∧ regOk' S W C ∧
            LogWf' σ.notifiedLog ∧ σ.notifiedLog.length < 2 ^ 63⌝ := by
  haveI := fun σ => hpers.2.2.2.2.2.1 T.ep.ι.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 T.σs.ws S
  haveI := hpers.1 T.ep.kv T.ep.ι.kv
  haveI := hpers.2.1 T.ws T.ep.ι.kv T.σs.ws
  haveI : Timeless (streamInv (GF := GF) T.σs) := by unfold streamInv; infer_instance
  haveI : Timeless (memberInv (GF := GF) T.ep.ks T.ep.γh T.ep.mp T.ep.m T.ep.ι) := by
    unfold memberInv memberState; infer_instance
  have hm := streamN_memberN T.ep.i
  iintro ⟨Hlive, #Hsinv, #Hws, Hrcv, Hreg⟩
  iunfold epLive at Hlive
  iunfold incLive at Hlive
  iunfold isInc at Hlive
  icases Hlive with ⟨⟨#Hminv, #Hkv⟩, Hret⟩
  iinv Hminv with >Hmi Hmclose
  icases memberInv_live T.ep.ks T.ep.γh T.ep.mp T.ep.m T.ep.ι q $$ [$Hret $Hmi] with ⟨Hret, Hms⟩
  iunfold memberState at Hms
  icases Hms with ⟨%σ, %b, %Hl, Hσ, Hgσ, Ha1, Ha2, Ha3, Ha4, Hbnd, Hmr, Hmc, Hmn, #Hlb, %Hok⟩
  iinv Hsinv with >Hsi Hsclose
  iunfold streamInv at Hsi
  icases Hsi with ⟨%S, %W', %C, HS, Hcl, Hreg', Hcn, %HregOk⟩
  ihave %HW := ghostMapAuth_agree T.σs.reg _ _ _ _ $$ Hreg' Hreg
  subst HW
  ihave %Hro := hrok T.ws T.ep.ι.kv T.σs.ws rs S σ $$ [$Hws $Hrcv $HS $Hσ]
  ihave %Hr := hreach T.ep.kv T.ep.ι.kv σ $$ [$Hkv $Hσ]
  have hwf := (reach_logWf.law_holds σ Hr.1).2
  have hnl : σ.notifiedLog.length < 2 ^ 63 := by
    have := Hr.2
    unfold MvccState.notifiedLog; split <;> simp <;> omega
  icases monoNat_auth_lb _ _ _ $$ Hmr with ⟨#L1, Hmr⟩
  icases monoNat_auth_lb _ _ _ $$ Hmc with ⟨#L2, Hmc⟩
  icases monoNat_auth_lb _ _ _ $$ Hmn with ⟨#L3, Hmn⟩
  ihave #Hq : readQ T.ep.ks T.ep.γh T.ep.m σ $$ []
  · iunfold readQ
    iexists Hl
    iframe #
    ipureintro; exact ⟨Hok.2.2.2.2.2.2.2.2.1, Hr.1, Hr.2⟩
  imod Hsclose $$ [HS Hcl Hreg' Hcn] with -
  · inext; iunfold streamInv; iexists S, W', C; iframe; ipureintro; exact HregOk
  imod Hmclose $$ [Hσ Hgσ Ha1 Ha2 Ha3 Ha4 Hbnd Hmr Hmc Hmn] with -
  · inext; iunfold memberInv; ileft; iunfold memberState
    iexists σ, b, Hl; iframe; iframe #; ipureintro; exact Hok
  imodintro
  iframe Hrcv Hreg
  isplitl [Hret]
  · iunfold epLive; iunfold incLive; iunfold isInc; iframe; iframe #
  iexists σ, S, C
  iframe Hq
  ipureintro
  exact ⟨Hro, fun lo => onceUpTo_of_all Hok.2.2.2.2.2.2.2.2.2 lo σ.crev, HregOk, hwf, hnl⟩

end defs

end mvccfull
end EtcdGrove
end Perennial
