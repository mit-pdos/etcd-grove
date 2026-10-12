/-
Proof of `Spec/demux__Broadcast.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__Broadcast
public import Spec.go_etcd_io.etcd.cache.v3.validateRevisions
public import Spec.go_etcd_io.etcd.cache.v3.demux__updateStoreLocked
public import Spec.go_etcd_io.etcd.cache.v3.demux__broadcastLocked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## The model: `appendAll` -/

theorem demuxBC_ringAppend_eq {V : Type} (cap : Nat) (hc : 0 < cap) (h : List V) (v : V)
    (hh : h.length ≤ cap) :
    ringAppend cap h v = (h ++ [v]).drop (h.length + 1 - cap) := by
  unfold ringAppend
  split
  · rw [show h.length + 1 - cap = 0 by omega]; rfl
  · rw [show h.length + 1 - cap = 1 by omega]
    cases h with
    | nil => simp at *; omega
    | cons x xs => rfl

theorem demuxBC_appendAll_eq (cap : Nat) (hc : 0 < cap) :
    ∀ (h bs : List Batch), h.length ≤ cap →
      appendAll cap h bs = (h ++ bs).drop (h.length + bs.length - cap) := by
  intro h bs
  induction bs generalizing h with
  | nil =>
    intro hh
    rw [show h.length + ([] : List Batch).length - cap = 0 by simp; omega]
    simp [appendAll]
  | cons b bs ih =>
    intro hh
    have e1 : appendAll cap h (b :: bs) = appendAll cap (ringAppend cap h b) bs := rfl
    rw [e1, demuxBC_ringAppend_eq cap hc h b hh]
    have hlen : ((h ++ [b]).drop (h.length + 1 - cap)).length = h.length + 1 - (h.length + 1 - cap) := by
      simp
    have hl : ((h ++ [b]).drop (h.length + 1 - cap)).length ≤ cap := by
      rw [hlen]; omega
    rw [ih _ hl, hlen, ← List.drop_append_of_le_length (by simp), List.drop_drop]
    rw [List.append_assoc, List.singleton_append, List.length_cons]
    congr 1
    omega

theorem demuxBC_mem_split {evs : List EvModel} {b : Batch} (hb : b ∈ splitBatches evs) :
    ∃ e ∈ evs, batchRev b = e.rev := by
  obtain ⟨hne, -⟩ := splitBatches_ok evs b hb
  cases b with
  | nil => exact absurd rfl hne
  | cons e es =>
    refine ⟨e, ?_, rfl⟩
    rw [← splitBatches_flatten evs]
    exact List.mem_flatten.2 ⟨_, hb, List.mem_cons_self ..⟩

theorem demuxBC_last_max {evs : List EvModel} (hs : EvRevSorted evs) {l : EvModel}
    (hl : evs.getLast? = some l) : ∀ e ∈ evs, sint.Z e.rev ≤ sint.Z l.rev := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact (List.pairwise_append.1 hs).2.2 e h l (List.mem_singleton_self _)
  · rw [List.mem_singleton.1 h]; exact Int.le_refl _

/-- The events case of `updResp`. -/
theorem demuxBC_updCore (cap : Nat) (c : DemuxCore) (evs : List EvModel)
    (hinv : DemuxInv cap c) (hmin : c.minRev ≠ W64 0) (hne : evs ≠ [])
    (habove : ∀ e ∈ evs, sint.Z c.maxRev < sint.Z e.rev) (hs : EvRevSorted evs)
    (hbd : ∀ e ∈ evs, sint.Z e.rev < 2 ^ 63 - 1)
    (hbase : ∀ b ∈ splitBatches evs, c.base < sint.Z (batchRev b)) :
    DemuxInv cap (updCore cap c evs) ∧ StreamExt c (updCore cap c evs) := by
  obtain ⟨l, hl⟩ : ∃ l, evs.getLast? = some l := by
    cases h : evs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some l => exact ⟨l, rfl⟩
  have hlmem : l ∈ evs := List.mem_of_getLast? hl
  have hlmax := demuxBC_last_max hs hl
  have hcap := hinv.cap_pos
  generalize hbsdef : splitBatches evs = bs
  have hbase' : ∀ b ∈ bs, c.base < sint.Z (batchRev b) := by rw [← hbsdef]; exact hbase
  have hbsne : bs ≠ [] := by
    rw [← hbsdef]; exact fun h => hne ((splitBatches_eq_nil_iff evs).1 h)
  have hbok : ∀ b ∈ bs, BatchOk b := by rw [← hbsdef]; exact splitBatches_ok evs
  have hbsorted : RevSorted batchRev bs := by rw [← hbsdef]; exact splitBatches_sorted evs hs
  have hbrev : ∀ b ∈ bs, sint.Z c.maxRev < sint.Z (batchRev b) ∧
      sint.Z (batchRev b) ≤ sint.Z l.rev ∧ sint.Z (batchRev b) < 2 ^ 63 - 1 := by
    intro b hb
    rw [← hbsdef] at hb
    obtain ⟨e, he, hre⟩ := demuxBC_mem_split hb
    rw [hre]
    exact ⟨habove e he, hlmax e he, hbd e he⟩
  have hmax0 := hinv.maxRev_nonneg
  have hSt : StreamOk (c.stream ++ bs) := by
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_append.1 hb with h | h
      · exact hinv.stream_ok.batches b h
      · exact hbok b h
    · unfold RevSorted
      rw [List.pairwise_append]
      refine ⟨hinv.stream_ok.sorted, hbsorted, fun a ha b hb => ?_⟩
      have := hinv.stream_le a ha
      have := (hbrev b hb).1
      omega
    · intro b hb
      rcases List.mem_append.1 hb with h | h
      · exact hinv.stream_ok.pos b h
      · have := (hbrev b h).1; omega
  have hle' : ∀ b ∈ c.stream ++ bs, sint.Z (batchRev b) ≤ sint.Z l.rev := by
    intro b hb
    rcases List.mem_append.1 hb with h | h
    · have := hinv.stream_le b h; have := habove l hlmem; omega
    · exact (hbrev b h).2.1
  -- the history
  obtain ⟨P, hP⟩ := hinv.hist_suffix
  have hlbex : ∃ lb, bs = bs.dropLast ++ [lb] :=
    ⟨bs.getLast hbsne, (List.dropLast_concat_getLast hbsne).symm⟩
  obtain ⟨lb, hlb⟩ := hlbex
  generalize hdldef : bs.dropLast = dl at hlb
  have hHlen := hinv.hist_len
  have hall : appendAll cap c.history bs = ringAppend cap (appendAll cap c.history dl) lb := by
    rw [show appendAll cap c.history bs = appendAll cap c.history (dl ++ [lb]) from
      congrArg _ hlb]
    simp [appendAll, List.foldl_append]
  have hbeq := demuxBC_appendAll_eq cap hcap c.history dl hHlen
  generalize hhb : appendAll cap c.history dl = hb at hall hbeq
  have hblen : hb.length = c.history.length + dl.length -
      (c.history.length + dl.length - cap) := by rw [hbeq]; simp
  have hupd : updCore cap c evs =
      { minRev := if hb.length = cap then oldestRev batchRev hb + W64 1 else c.minRev
        maxRev := l.rev
        history := ringAppend cap hb lb
        stream := c.stream ++ bs
        base := c.base } := by
    simp only [updCore, hbsdef, hdldef, hhb, hl, ← hall]
  rw [hupd]
  have hbaseAll : ∀ b ∈ c.stream ++ bs, c.base < sint.Z (batchRev b) := by
    intro b hb
    rcases List.mem_append.1 hb with h | h
    · exact hinv.base_stream b h
    · exact hbase' b h
  have hbaseMax : c.base ≤ sint.Z l.rev := by
    have hlbm : lb ∈ bs := by rw [hlb]; simp
    have := hbase' lb hlbm
    have := (hbrev lb hlbm).2.1
    omega
  have hstream_eq : c.stream ++ bs = P ++ (c.history ++ dl) ++ [lb] := by
    rw [← hP, hlb]; simp
  refine ⟨?_, ⟨bs, rfl, by have := habove l hlmem; simp only; omega,
    fun b hb => (hbrev b hb).1, hSt, hle'⟩⟩
  by_cases hfull : hb.length = cap
  · -- the last append evicts: `minRev` is one above the evicted batch
    obtain ⟨o, t, rfl⟩ : ∃ o t, hb = o :: t := by
      cases hb with
      | nil => simp at hfull; omega
      | cons o t => exact ⟨o, t, rfl⟩
    have hra : ringAppend cap (o :: t) lb = t ++ [lb] := by
      unfold ringAppend; split
      · rename_i h; simp at h hfull; omega
      · rfl
    have hold : oldestRev batchRev (o :: t) = batchRev o := rfl
    simp only [hfull, ↓reduceIte, hra, hold]
    -- the stream around `o`
    have hsplit : c.stream ++ bs =
        (P ++ (c.history ++ dl).take (c.history.length + dl.length - cap)) ++
          (o :: (t ++ [lb])) := by
      rw [hstream_eq, ← List.take_append_drop (c.history.length + dl.length - cap)
        (c.history ++ dl), ← hbeq]
      simp
    have hsorted := hSt.sorted
    unfold RevSorted at hsorted
    rw [hsplit, List.pairwise_append, List.pairwise_cons] at hsorted
    obtain ⟨-, ⟨hot, -⟩, hAo⟩ := hsorted
    have homem : o ∈ c.stream ++ bs := by rw [hsplit]; simp
    have ho1 := hSt.pos o homem
    have ho2 := hle' o homem
    have ho3 := hbd l hlmem
    have hoZ : sint.Z (batchRev o + W64 1) = sint.Z (batchRev o) + 1 := by word
    exact {
      cap_pos := hinv.cap_pos, cap_le := hinv.cap_le, stream_ok := hSt, stream_le := hle'
      maxRev_nonneg := by show 0 ≤ sint.Z l.rev; have := habove l hlmem; omega
      maxRev_lt := hbd l hlmem
      hist_suffix := by rw [hsplit]; exact List.suffix_append_of_suffix (List.suffix_cons _ _)
      hist_len := by simp at hfull ⊢; omega
      hist_complete := fun b hb hge => by
        simp only at hb hge ⊢
        rw [hsplit] at hb
        rcases List.mem_append.1 hb with h | h
        · have := hAo b h o (List.mem_cons_self ..); omega
        · rcases List.mem_cons.1 h with h | h
          · subst h; omega
          · exact h
      uninit := fun h => by
        simp only at h
        have : sint.Z (batchRev o + W64 1) = sint.Z (W64 0) := by rw [h]
        rw [hoZ] at this
        simp at this; omega
      base_stream := by intro b hb; simp only at hb ⊢; exact hbaseAll b hb
      base_minRev := fun _ => by
        simp only
        rw [hoZ]
        have := hbaseAll o homem
        omega
      base_maxRev := fun _ => by simp only; exact hbaseMax }
  · -- no eviction: the history is the old one with the batches appended
    have hlt : c.history.length + dl.length < cap := by
      have : hb.length ≤ cap := by rw [hblen]; omega
      omega
    have hbH : hb = c.history ++ dl := by
      rw [hbeq, show c.history.length + dl.length - cap = 0 by omega]; rfl
    have hra : ringAppend cap hb lb = c.history ++ bs := by
      unfold ringAppend
      split
      · rw [hbH, hlb]; simp
      · rename_i h; rw [hbH] at h; simp at h; omega
    simp only [hfull, ↓reduceIte, hra]
    exact {
      cap_pos := hinv.cap_pos, cap_le := hinv.cap_le, stream_ok := hSt, stream_le := hle'
      maxRev_nonneg := by show 0 ≤ sint.Z l.rev; have := habove l hlmem; omega
      maxRev_lt := hbd l hlmem
      hist_suffix := by rw [← hP, List.append_assoc]; exact List.suffix_append _ _
      hist_len := by
        have : bs.length = dl.length + 1 := by rw [hlb]; simp
        simp; omega
      hist_complete := fun b hb hge => by
        simp only at hb hge ⊢
        rcases List.mem_append.1 hb with h | h
        · exact List.mem_append_left _ (hinv.hist_complete b h hge)
        · exact List.mem_append_right _ h
      uninit := fun h => absurd h hmin
      base_stream := by intro b hb; simp only at hb ⊢; exact hbaseAll b hb
      base_minRev := fun h => hinv.base_minRev h
      base_maxRev := fun _ => by simp only; exact hbaseMax }

theorem demuxBC_updResp (cap : Nat) (c : DemuxCore) (r : RespModel) (hinv : DemuxInv cap c)
    (hmin : c.minRev ≠ W64 0) (hv : validRevisions r c.maxRev = true)
    (hs : EvRevSorted r.events) (hbd : RespRevsBounded r)
    (hpb : r.isProgressNotify = true → c.base ≤ sint.Z r.hdrRev)
    (heb : r.isProgressNotify = false → ∀ b ∈ splitBatches r.events, c.base < sint.Z (batchRev b)) :
    DemuxInv cap (updResp cap c r) ∧ StreamExt c (updResp cap c r) ∧
      BroadcastPre (updResp cap c r) c.stream.length r := by
  unfold updResp
  by_cases hpn : r.isProgressNotify = true
  · simp only [hpn, ↓reduceIte]
    have hle : sint.Z c.maxRev ≤ sint.Z r.hdrRev := by
      simp only [validRevisions, hpn, ↓reduceIte, Bool.not_eq_true',
        decide_eq_false_iff_not] at hv
      omega
    have h0 := hinv.maxRev_nonneg
    refine ⟨{ hinv with
      stream_le := fun b hb => by have := hinv.stream_le b hb; simp only; omega
      maxRev_nonneg := by simp only; omega
      maxRev_lt := hbd.1
      uninit := fun h => absurd h hmin
      base_maxRev := fun _ => by simp only; exact hpb hpn }, ⟨[], by simp, hle, by simp, hinv.stream_ok,
        fun b hb => by have := hinv.stream_le b hb; simp only; omega⟩, ?_⟩
    simp [BroadcastPre, hpn]
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte]
    by_cases he : r.events = []
    · simp only [he, ↓reduceIte]
      refine ⟨hinv, ⟨[], by simp, Int.le_refl _, by simp, hinv.stream_ok, hinv.stream_le⟩, ?_⟩
      simp [BroadcastPre, hpn, he]
    · simp only [he, ↓reduceIte]
      have habove : ∀ e ∈ r.events, sint.Z c.maxRev < sint.Z e.rev := by
        simp only [validRevisions, hpn, Bool.false_eq_true, ↓reduceIte, List.all_eq_true,
          decide_eq_true_eq] at hv
        exact hv
      obtain ⟨h1, h2⟩ := demuxBC_updCore cap c r.events hinv hmin he habove hs hbd.2
        (heb (by simpa using hpn))
      refine ⟨h1, h2, ?_⟩
      simp only [BroadcastPre, hpn, he, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hs, ?_⟩
      show c.stream ++ splitBatches r.events =
        (c.stream ++ splitBatches r.events).take c.stream.length ++ splitBatches r.events
      simp

/-- The new state's `minRev` stays non-zero. -/
theorem demuxBC_minRev (cap : Nat) (c : DemuxCore) (r : RespModel)
    (hinv' : DemuxInv cap (updResp cap c r)) (hmin : c.minRev ≠ W64 0) :
    (updResp cap c r).minRev ≠ W64 0 := by
  intro h
  have hst := (hinv'.uninit h).1
  revert h hst
  unfold updResp
  split
  · intro h; exact absurd h hmin
  · split
    · intro h; exact absurd h hmin
    · rename_i he
      intro _ hst
      simp only [updCore, List.append_eq_nil_iff] at hst
      exact he ((splitBatches_eq_nil_iff _).1 hst.2)

theorem demuxBC_base (cap : Nat) (c : DemuxCore) (r : RespModel) :
    (updResp cap c r).base = c.base := by
  unfold updResp updCore; split
  · rfl
  · split <;> rfl

theorem demuxBC_lastRev_ge (cap : Nat) (c : DemuxCore) (hinv : DemuxInv cap c) :
    c.base ≤ c.lastRev := by
  unfold DemuxCore.lastRev
  cases h : c.stream.getLast? with
  | none => exact Int.le_refl _
  | some b =>
    have := hinv.base_stream b (List.mem_of_getLast? h)
    simp only; omega

theorem demuxBC_chainEnd (c : DemuxCore) : chainEnd c.base c.stream = c.lastRev := by
  unfold chainEnd DemuxCore.lastRev; rfl

section iris
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The batches of a chain from `last` are above `last`. -/
theorem demuxBC_certChain_above (C : DemuxCert GF) (last : Int) (bs : List Batch) :
    certChain C last bs ⊢ ⌜∀ b ∈ bs, last < sint.Z (batchRev b)⌝ := by
  induction bs generalizing last with
  | nil => iintro _; ipureintro; intro b hb; cases hb
  | cons b bs ih =>
    rw [certChain_cons]
    iintro ⟨⟨%p, %Hp, -⟩, H⟩
    ihave %Hih := ih (sint.Z (batchRev b)) $$ H
    ipureintro
    intro b' hb'
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact Hp.2
    · have := Hih b' hb'; omega

/-- The accepted case of `Broadcast`: the new state, its certificate chain and its `maxRev`'s
certificate. -/
theorem demuxBC_cert (C : DemuxCert GF) (cap : Nat) (c : DemuxCore) (r : RespModel)
    (hinv : DemuxInv cap c) (hmin : c.minRev ≠ W64 0) (hv : validRevisions r c.maxRev = true)
    (hs : EvRevSorted r.events) (hbd : RespRevsBounded r) :
    certChain C c.base c.stream ∗ □ C.prog c.maxRev ∗ respCert C c r ⊢
      ⌜DemuxInv cap (updResp cap c r) ∧ StreamExt c (updResp cap c r) ∧
        BroadcastPre (updResp cap c r) c.stream.length r⌝ ∗
      certChain C (updResp cap c r).base (updResp cap c r).stream ∗
      □ C.prog (updResp cap c r).maxRev := by
  rw [demuxBC_base]
  by_cases hpn : r.isProgressNotify = true
  · have hst : (updResp cap c r).stream = c.stream := by simp [updResp, hpn]
    have hmx : (updResp cap c r).maxRev = r.hdrRev := by simp [updResp, hpn]
    rw [hst, hmx]
    unfold respCert; rw [ite_eq_left hpn]
    iintro ⟨#Hc, -, %Hle, #Hp⟩
    isplitr
    · ipureintro
      exact demuxBC_updResp cap c r hinv hmin hv hs hbd (fun _ => Hle)
        (fun h => by rw [hpn] at h; cases h)
    iframe Hc Hp
  · have hpn' : r.isProgressNotify = false := by simpa using hpn
    by_cases he : r.events = []
    · have hst : (updResp cap c r).stream = c.stream := by simp [updResp, hpn', he]
      have hmx : (updResp cap c r).maxRev = c.maxRev := by simp [updResp, hpn', he]
      rw [hst, hmx]
      unfold respCert; rw [ite_eq_right hpn, ite_eq_left he]
      iintro ⟨#Hc, #Hp, -⟩
      isplitr
      · ipureintro
        exact demuxBC_updResp cap c r hinv hmin hv hs hbd (fun h => absurd h hpn)
          (fun _ b hb => by rw [he] at hb; simp [splitBatches] at hb)
      iframe Hc Hp
    · have hst : (updResp cap c r).stream = c.stream ++ splitBatches r.events := by
        simp [updResp, hpn', he, updCore]
      obtain ⟨e, he'⟩ : ∃ e, r.events.getLast? = some e := by
        cases h : r.events.getLast? with
        | none => simp [List.getLast?_eq_none_iff] at h; exact absurd h he
        | some e => exact ⟨e, rfl⟩
      have hmx : (updResp cap c r).maxRev = e.rev := by simp [updResp, hpn', he, updCore, he']
      obtain ⟨b, hb, hbr⟩ := splitBatches_last_rev r.events e he'
      rw [hst, hmx]
      unfold respCert; rw [ite_eq_right hpn, ite_eq_right he]
      iintro ⟨#Hc, -, #Hr⟩
      ihave %Habove := demuxBC_certChain_above C c.lastRev _ $$ Hr
      ihave #Hps := certChain_prog (C := C) c.lastRev _ $$ Hr
      have hlb := demuxBC_lastRev_ge cap c hinv
      isplitr
      · ipureintro
        exact demuxBC_updResp cap c r hinv hmin hv hs hbd (fun h => absurd h hpn)
          (fun _ b hb => by have := Habove b hb; omega)
      isplitl
      · iapply (certChain_append c.base c.stream (splitBatches r.events)).2
        iframe Hc
        rw [demuxBC_chainEnd]
        iexact Hr
      rw [← hbr]
      imodintro
      iapply Hps
      ipureintro; exact List.mem_of_getLast? hb

end iris

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.Broadcast.wp_proof
    (wp_validateRevisions : validateRevisions.spec (GF := GF) (hG := hG))
    (wp_updateStoreLocked : demux.updateStoreLocked.spec (GF := GF) (hG := hG))
    (wp_broadcastLocked : demux.broadcastLocked.spec (GF := GF) (hG := hG)) :
    demux.Broadcast.spec (GF := GF) (hG := hG) := by
  intro d γd cap C c resp r
  wp_start as ⟨#Hisd, Hw, #Hresp, % ⟨Hsorted, Hbd⟩, Hcert⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxWriter
  icases Hw with ⟨Hcw, Hh, %Hinv⟩
  unfold demuxHandle
  wp_apply (lc := 2) sync.RWMutex.wp_Lock $$ [$Hh] as ⟨Hlocked, HP⟩
  ihave Hlc : £ 2 $$ [Hlc1 Hlc2]
  · iapply (lc_split (n := 1) (m := 1)).2; iframe
  imod demux_lock_acquire d γd cap $$ [HP Hlc] with ⟨%c0, %regs, %views, Hcore, HL, %Hinv0⟩
  · iframe; iframe #
  icombine Hcore Hcw gives % ⟨_, Heq⟩
  subst Heq
  iNamed HL
  wp_auto
  wp_if_destruct
  · -- not initialized
    wp_apply (lc := 1) errors.wp_New as %e -
    imod demux_lock_release d γd cap c0 regs views $$ [Hcore HminRev HmaxRev HactF HlagF Hact
      Hlag Hhist Hres Hregs Hviews Hlc1] with HP
    · isplitr
      · iexact Hisd
      iframe Hcore Hlc1
      isplitl
      · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
      ipureintro; exact Hinv
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked HP] as Hh
    · inext; iexact HP
    have Hbc : broadcastCore cap c0 r = none := by simp [broadcastCore, Hif]
    iapply HΦ
    rw [Hbc]
    dsimp only
    iframe
    ipureintro; exact ⟨Hinv, e, rfl⟩
  · wp_apply wp_validateRevisions resp r c0.maxRev $$ [] as %verr %Hval
    · iexact Hresp
    cases hv : validRevisions r c0.maxRev
    · simp only [hv, Bool.false_eq_true, ↓reduceIte] at Hval
      obtain ⟨e, rfl⟩ := Hval
      wp_auto_lc 1
      imod demux_lock_release d γd cap c0 regs views $$ [Hcore HminRev HmaxRev HactF HlagF Hact
        Hlag Hhist Hres Hregs Hviews Hlc1] with HP
      · isplitr
        · iexact Hisd
        iframe Hcore Hlc1
        isplitl
        · unfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
        ipureintro; exact Hinv
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked HP] as Hh
      · inext; iexact HP
      have Hbc : broadcastCore cap c0 r = none := by simp [broadcastCore, hv]
      iapply HΦ
      rw [Hbc]
      dsimp only
      iframe
      ipureintro; exact ⟨Hinv, e, rfl⟩
    · simp only [hv, ↓reduceIte] at Hval
      subst Hval
      wp_auto
      wp_apply wp_updateStoreLocked d cap c0 resp r $$ [HminRev HmaxRev Hhist]
        as ⟨HminRev, HmaxRev, Hhist⟩
      · iframe; iframe #; ipureintro; exact ⟨Hinv, Hif, hv, Hsorted, Hbd⟩
      ihave #HrC := Hcert $$ []
      · ipureintro; exact ⟨Hif, rfl⟩
      ihave ⟨%Hnew, #Hcerts', #Hprog'⟩ := demuxBC_cert C cap c0 r Hinv Hif hv Hsorted Hbd
        $$ [Hcerts Hprog HrC]
      · iframe #
      obtain ⟨Hinv', Hext, Hpre⟩ := Hnew
      imod ghostVar_update_halves (updResp cap c0 r) γd.core c0 c0 $$ Hcore Hcw with ⟨Hcore, Hcw⟩
      ihave Hrf := regRes_refresh (hG := hG) γd regs views c0 (updResp cap c0 r) Hok.dom
        Hok.mapped Hext $$ [Hviews Hres]
      · iframe
      imod Hrf with ⟨Hviews, Hres⟩
      wp_apply (lc := 1) wp_broadcastLocked d γd cap C (updResp cap c0 r) c0.stream.length regs
        (views.fmap (refreshView (updResp cap c0 r))) resp r
        $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres] as ⟨%views', HL⟩
      · isplitl
        · unfold demuxLocked; iexists actP, lagP; simp only [named]
          rw [actOf_refresh, lagOf_refresh]
          iframe; iframe Hcerts' Hprog'; ipureintro
          exact ⟨Hok.refresh (Nat.le_refl _) Hext,
            Hstart.refresh (fun _ => demuxBC_minRev cap c0 r Hinv' Hif) (demuxBC_base cap c0 r)⟩
        iframe #; ipureintro; exact ⟨Hinv', Hpre⟩
      imod demux_lock_release d γd cap (updResp cap c0 r) regs views' $$ [Hcore HL Hlc1] with HP
      · iframe; iframe #; ipureintro; exact Hinv'
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlocked HP] as Hh
      · inext; iexact HP
      have Hbc : broadcastCore cap c0 r = some (updResp cap c0 r) := by
        unfold broadcastCore; split
        · contradiction
        · simp [hv]
      iapply HΦ
      rw [Hbc]
      dsimp only
      iframe
      ipureintro; exact ⟨Hinv', rfl⟩

end proof

end EtcdGrove
end Perennial
