/-
**A substream's resume revision** (D25, `notes/decisions.md`): the request's `rev` field that
`serveSubstream` keeps (`ws.initReq.rev = nextRev` after each response) and from which `run`
re-creates the watch after a reconnect (`resumeOk`, `InvWatch.lean`): how it moves with each
response (`resumeOk_created`, `resumeOk_step`, the fork's F3: it moves only forward,
`issues/etcd-watch-resume-below-start-revision.md`). Lean-first, no Rocq counterpart.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3
open go_etcd_io.etcd.cache.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- A create without start-read needs nothing. -/
theorem startOk_false (V : WEnv GF) (rev : w64) : ⊢ startOk V false rev := by
  unfold startOk
  ileft; ipureintro; rfl

/-- What a promised completeness says of the watch's start revision. -/
theorem cplCond_rev {sr : Bool} {o : OpFull} {rev : w64} (h : cplCond sr o rev = true) :
    sr = true ∧ rev ≠ W64 0 := by
  unfold cplCond at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.2.2.2⟩

/-- **The resume revision at the substream's start**: the watch's start revision. -/
theorem resumeOk_init (V : WEnv GF) (P : WsPrm GF) (hok : wsReqOk V.pfx P)
    (hc : P.γ.cpl = cplOf P) :
    startOk V P.sr P.rev ⊢ resumeOk V P P.rev (P.rev - W64 1) (P.rev - W64 1) := by
  iintro #Hs
  unfold resumeOk
  have h0 : 0 ≤ sint.Z P.rev := hok.2.2.1
  isplitr
  · ipureintro
    refine ⟨Or.inr (Int.le_refl _), Or.inl (by word), fun _ => rfl⟩
  cases hcp : cplOf P
  · iapply startOk_false
  · obtain ⟨hsr, -⟩ := cplCond_rev hcp
    rw [← hsr]; iexact Hs

/-- **The resume revision after the first created response** (`if ws.initReq.rev == 0 {nextRev =
wr.Header.Revision}`): `rv` is the start revision, or the created response's revision `H` for a
watch from "now". -/
theorem resumeOk_created (V : WEnv GF) (P : WsPrm GF) (H rv hl c2 : w64) (hc : P.γ.cpl = cplOf P)
    (hrv : rv = P.rev ∨ (P.rev = W64 0 ∧ rv = H)) (hl0 : rv = P.rev ∨ sint.Z hl < 0) :
    resumeOk V P P.rev hl c2 ⊢ resumeOk V P rv hl c2 := by
  rcases hrv with rfl | ⟨h0, rfl⟩
  · iintro H; iexact H
  unfold resumeOk
  iintro ⟨%Hro, -⟩
  have hcpl : P.γ.cpl = false := by
    rw [hc]
    cases hcp : cplOf P
    · rfl
    · exact absurd h0 (cplCond_rev hcp).2
  isplitr
  · ipureintro
    refine ⟨Or.inl h0, ?_, fun h => by rw [hcpl] at h; cases h⟩
    rcases hl0 with he | hl
    · rw [he]; exact Hro.2.1
    · exact Or.inr hl
  have : cplOf P = false := by rw [← hc]; exact hcpl
  rw [this]; iapply startOk_false

/-- **The second cursor around the `k`th response** (`recvCmpl`), from its position before: its
position after and, when the watch promises completeness, the cache's contract between them. -/
theorem recvCmpl_at (V : WEnv GF) (P : WsPrm GF) (k : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (r : RespModel) (c2 : w64) :
    recvCmpl V P k v r ∗ (⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 k.toNat c2) ⊢
      ∃ h2A : w64, (⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 (k.toNat + 1) h2A) ∗
        (⌜P.γ.cpl = false⌝ ∨ watchRespOk (EM := V.EM) P.o.key c2 h2A v r) := by
  unfold recvCmpl
  iintro ⟨#Hc, #Hp⟩
  icases Hc with (%H | ⟨%h2B, %h2A, #HB, #HA, #Hok⟩)
  · iexists c2
    isplitl
    · ileft; ipureintro; exact H
    · ileft; ipureintro; exact H
  icases Hp with (%H | #Hp)
  · iexists c2
    isplitl
    · ileft; ipureintro; exact H
    · ileft; ipureintro; exact H
  ihave %Hb := mono_list_idx_agree P.γh2 _ _ _ $$ HB Hp
  subst Hb
  iexists h2A
  isplitl
  · iright; iexact HA
  · iright; iexact Hok

/-- **The resume revision after a response that is not a created one** (F3: `nextRev` moves to
the header's revision + 1 only forward, then past the last event): at the dispatch cursor's new
position `hiA` and the second cursor's `h2A`. -/
theorem resumeOk_step (V : WEnv GF) (P : WsPrm GF) (rv hl c2 hiA h2A nr0 nr' : w64)
    (r : RespModel) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (hok : wsReqOk V.pfx P) (hc : P.γ.cpl = cplOf P)
    (hfl : r.created = false ∧ r.canceled = false ∧ r.compactRev = W64 0)
    (hv : v.closeErr' = GoInterface.nil ∧ v.CompactRevision' = r.compactRev ∧
      v.Canceled' = r.canceled)
    (h0 : (sint.Z rv < sint.Z (r.hdrRev + W64 1) ∧ nr0 = r.hdrRev + W64 1) ∨
      (¬ sint.Z rv < sint.Z (r.hdrRev + W64 1) ∧ nr0 = rv))
    (h1 : (r.events = [] ∧ nr' = nr0) ∨ (∃ e, r.events.getLast? = some e ∧ nr' = e.rev + W64 1)) :
    resumeOk V P rv hl c2 ∗ rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hl hiA r ∗
      (⌜P.γ.cpl = false⌝ ∨ watchRespOk (EM := V.EM) P.o.key c2 h2A v r) ∗ resumeF V P r ⊢
      resumeOk V P nr' hiA h2A := by
  iintro ⟨Hro, Hrw, #Hw, #Hf⟩
  iunfold resumeOk at Hro
  icases Hro with ⟨%Hro, #Hs⟩
  iunfold rangeWatchRespOk at Hrw
  icases Hrw with ⟨%Hrw, #Hevs⟩
  obtain ⟨Hr1, Hr2, Hr3⟩ := Hro
  obtain ⟨-, Hgt, HhiA⟩ := Hrw
  have hrev0 : 0 ≤ sint.Z P.rev := hok.2.2.1
  have hnoerr : ¬ watchErr v := by
    unfold watchErr; rw [hv.1, hv.2.1, hv.2.2, hfl.2.2, hfl.2.1]; simp
  rcases h1 with ⟨hne, hnr⟩ | ⟨e, hlast, hnr⟩
  · -- no events: the header's revision, forward only
    have hhiA : hiA = hl := by rw [HhiA, hne]; rfl
    subst hhiA
    have hnr0 : (sint.Z rv < sint.Z nr0) ∨ nr0 = rv := by
      rcases h0 with ⟨hlt, he⟩ | ⟨-, he⟩
      · left; rw [he]; exact hlt
      · right; exact he
    -- the second cursor
    ihave %Hc2 : ⌜P.γ.cpl = true → h2A = nr0 - W64 1⌝ $$ []
    · icases Hw with (%Hcf | Hw)
      · ipureintro; intro h; rw [Hcf] at h; cases h
      iunfold watchRespOk at Hw
      icases Hw with (⟨%H, -⟩ | %H | ⟨%H, -, -⟩ | ⟨%H, -⟩)
      · exact absurd H.1 hnoerr
      · -- not a progress notification: its revision is 0
        ipureintro; intro hcp
        have hc2 := Hr3 hcp
        have hpos : 1 ≤ sint.Z P.rev := by
          have hcp' : cplOf P = true := by rw [← hc]; exact hcp
          have := (cplCond_rev hcp').2
          have : sint.Z P.rev ≠ 0 := fun h => this (by word)
          omega
        have hh0 : r.hdrRev = W64 0 := by
          refine Classical.byContradiction fun hn => ?_
          have hp := H.2.2.1
          simp [RespModel.isProgressNotify, hne, hfl.1, hfl.2.1, hfl.2.2] at hp
          exact hn hp
        have hrv : sint.Z P.rev ≤ sint.Z rv :=
          Hr1.resolve_left (by intro h; rw [h] at hpos; simp at hpos)
        rcases h0 with ⟨hlt, -⟩ | ⟨-, he⟩
        · rw [hh0] at hlt; exfalso
          have : sint.Z (W64 0 + W64 1) = 1 := by word
          omega
        · rw [he, H.2.2.2, hc2]
      · -- a progress notification: at its revision
        ipureintro; intro hcp
        have hc2 := Hr3 hcp
        obtain ⟨-, -, Hle, Heq, Hlt⟩ := H
        rw [Heq]
        rcases h0 with ⟨-, he⟩ | ⟨hnl, he⟩
        · rw [he]; word
        · rw [he]
          rw [hc2] at Hle
          have : sint.Z (r.hdrRev + W64 1) = sint.Z r.hdrRev + 1 := by word
          have : sint.Z (rv - W64 1) = sint.Z rv - 1 := by word
          word
      · exact absurd H.2.1 (by rw [hne]; simp)
    unfold resumeOk
    rw [hnr]
    isplitr
    · ipureintro
      rcases hnr0 with hlt | he
      · refine ⟨?_, ?_, Hc2⟩
        · rcases Hr1 with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        · rcases Hr2 with h | h
          · exact Or.inl (by omega)
          · exact Or.inr h
      · rw [he]; rw [he] at Hc2; exact ⟨Hr1, Hr2, Hc2⟩
    rcases h0 with ⟨-, he⟩ | ⟨-, he⟩
    · rw [he]
      cases hcp : cplOf P
      · iapply startOk_false
      · iunfold resumeF at Hf
        icases Hf with (%Hcf | #Hf2)
        · rw [hc, hcp] at Hcf; cases Hcf
        rw [show r.hdrRev = resumePos r by simp [resumePos, hne]]
        iexact Hf2
    · rw [he]; iexact Hs
  · -- events: just past the last
    have hmem : e ∈ r.events := List.mem_of_getLast? hlast
    have hhiA : hiA = e.rev := by rw [HhiA, hlast]; rfl
    subst hhiA
    ihave %He : ⌜sint.Z P.rev ≤ sint.Z e.rev ∧ sint.Z e.rev < 2 ^ 63 - 1⌝ $$ []
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      ihave #Hok := Hevs $$ %i %e %hi
      iunfold rangeWatchEvOk at Hok
      icases Hok with ⟨%H, -⟩
      ipureintro; exact ⟨H.2.1, H.2.2.1⟩
    ihave %Hc2 : ⌜P.γ.cpl = true → h2A = e.rev + W64 1 - W64 1⌝ $$ []
    · icases Hw with (%Hcf | Hw)
      · ipureintro; intro h; rw [Hcf] at h; cases h
      iunfold watchRespOk at Hw
      icases Hw with (⟨%H, -⟩ | %H | ⟨%H, -, -⟩ | ⟨%H, -⟩)
      · exact absurd H.1 hnoerr
      · exact absurd H.2.1 (by intro h; rw [h] at hmem; cases hmem)
      · exfalso
        have hp := H.2.1
        have : r.events.isEmpty = false := by
          cases hr : r.events with
          | nil => rw [hr] at hmem; cases hmem
          | cons _ _ => rfl
        simp [RespModel.isProgressNotify, this] at hp
      · ipureintro; intro _
        have h2 := H.2.2.2.2
        rw [hlast] at h2
        simp only [Option.map_some, Option.some.injEq] at h2
        rw [← h2]; word
    unfold resumeOk
    rw [hnr]
    isplitr
    · ipureintro
      refine ⟨?_, ?_, Hc2⟩
      · have : sint.Z (e.rev + W64 1) = sint.Z e.rev + 1 := by word
        exact Or.inr (by omega)
      · have : sint.Z (e.rev + W64 1) = sint.Z e.rev + 1 := by word
        exact Or.inl (by omega)
    cases hcp : cplOf P
    · iapply startOk_false
    · iunfold resumeF at Hf
      icases Hf with (%Hcf | #Hf2)
      · rw [hc, hcp] at Hcf; cases Hcf
      rw [show e.rev = resumePos r by simp [resumePos, hlast]]
      iexact Hf2

/-- **`recvc`'s positions from `n` on are free** (D25): the authority of the substream's position
statuses (`WsPrm.γps`), none at or past `n` (`run` marks the next position it sends a response to,
not a created one, `notStart`). -/
def psAt (P : WsPrm GF) (n : Nat) : IProp GF :=
  iprop(∃ M : GMap Nat Bool, ghostMapAuth P.γps 1 M ∗ ⌜∀ j, n ≤ j → M !! j = none⌝)

/-- **The positions' statuses of a substream not yet created**: its goroutine starts at `0`
(`lifeStart`), no other position is marked. -/
def psQ (P : WsPrm GF) : IProp GF :=
  iprop(∃ M : GMap Nat Bool, ghostMapAuth P.γps 1 M ∗ ⌜M !! 0 = some true ∧ ∀ j, 1 ≤ j → M !! j = none⌝)

/-- **Marking `recvc`'s next position** `n` as not a goroutine's start (D25): `run` before a
response that is not a created one. -/
theorem psAt_mark (P : WsPrm GF) (n : Nat) :
    psAt (GF := GF) P n ⊢ |={⊤}=> psAt P (n + 1) ∗ notStart P n := by
  unfold psAt notStart
  iintro ⟨%M, Ha, %HM⟩
  imod ghost_map_insert_persist n false (HM n (Nat.le_refl _)) $$ Ha with ⟨Ha, #He⟩
  imodintro
  iframe He
  iexists _
  iframe Ha
  ipureintro
  intro j hj
  rw [GMap.lookup_insert_ne _ _ (by omega)]
  exact HM j (by omega)

/-- **The positions' statuses of a queued substream** (D25), its current lifetime started at
`recvc`'s position `n` (`lifeStart`), no later position marked (a fresh one's: `psQ`, `n = 0`). -/
def psSt (P : WsPrm GF) (n : Nat) : IProp GF :=
  iprop(∃ M : GMap Nat Bool, ghostMapAuth P.γps 1 M ∗
    ⌜M !! n = some true ∧ ∀ j, n + 1 ≤ j → M !! j = none⌝)

theorem psQ_psSt (P : WsPrm GF) : psQ (GF := GF) P ⊢ psSt P 0 := by
  unfold psQ psSt
  iintro ⟨%M, Ha, %HM⟩
  iexists M
  iframe Ha
  ipureintro; exact HM

theorem psSt_psAt (P : WsPrm GF) (n : Nat) : psSt (GF := GF) P n ⊢ psAt P (n + 1) := by
  unfold psSt psAt
  iintro ⟨%M, Ha, %HM⟩
  iexists M
  iframe Ha
  ipureintro; exact HM.2

/-- A position's cursors, unchanged to itself. -/
theorem chainE_refl (P : WsPrm GF) (a : Nat) (hi : w64) :
    monoListIdxOwn (GF := GF) P.γhi a hi ∗
      (⌜P.γ.cpl = false⌝ ∨ ∃ c : w64, monoListIdxOwn P.γh2 a c) ⊢ chainE P a a := by
  iintro ⟨#Hhi, #Hh2⟩
  unfold chainE
  isplitr
  · ipureintro; exact Nat.le_refl a
  isplitr
  · iexists hi; iframe Hhi
  icases Hh2 with (%H | ⟨%c, #Hc⟩)
  · ileft; ipureintro; exact H
  · iright; iexists c; iframe Hc

/-- **A first lifetime's start** (`run`'s, at a `Watch`): nothing received, the cursors at the
watch's start `rev - 1`, the caller's resources. -/
theorem wsRun_init (V : WEnv GF) (P : WsPrm GF) (b0 : GoSlice) (t0 : _root_.Perennial.time.Time) :
    wsIs (GF := GF) V P ∗ sspscConsumer P.γr ([] : List Loc) ∗
      spscProducer P.γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListAuthOwn P.γ.cur 1 [P.rev - W64 1] ∗ monoListIdxOwn P.γhi 0 (P.rev - W64 1) ∗
      cur2Pos P 0 0 ∗ (⌜P.γ.cpl = false⌝ ∨ monoListIdxOwn P.γh2 0 (P.rev - W64 1)) ∗
      wsF P.ws go!"buf" ↦ b0 ∗ sliceOwn b0 [] ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∗ wsReqF P.ws go!"retc" ↦ P.retc ∗
      retcRes P ∗ wsF P.ws go!"bufWaitStartTime" ↦ t0 ⊢
    wsRun V P 0 P.rev [] P.rev := by
  iintro ⟨#HP, Hcons, Hprod, Hauth, #Hhi0, Hc2, #Hh20, Hbuf, Hb, Hrev, Hretc, Hres, Hbwt⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, -, -, -, %HPws, #Hsok⟩
  ihave #Hrs0 := resumeOk_init V P HPws.2.1 HPws.2.2 $$ Hsok
  unfold wsRun
  iexists [], [P.rev - W64 1], [], b0, P.retc, t0, (P.rev - W64 1), 0
  isplitl [Hcons]
  · iexact Hcons
  isplitr
  · ipureintro; exact Nat.le_refl 0
  isplitl [Hprod]
  · iexact Hprod
  isplitl [Hauth]
  · iexact Hauth
  isplitr
  · ipureintro; simp
  isplitr
  · iexact Hhi0
  isplitl [Hc2]
  · iexact Hc2
  isplitl [Hbuf]
  · iexact Hbuf
  isplitl [Hb]
  · simp only [List.map_nil]; iexact Hb
  isplitr
  · simp only [bufE, List.length_nil]
    iapply chainE_refl P 0 (P.rev - W64 1)
    iframe Hhi0
    icases Hh20 with (%H | #H)
    · ileft; ipureintro; exact H
    · iright; iexists _; iexact H
  isplitl [Hrev]
  · ileft; iframe Hrev; ipureintro; simp
  isplitr
  · iexists (P.rev - W64 1), (P.rev - W64 1)
    simp only [List.length_nil]
    iframe Hhi0 Hh20 Hrs0
  isplitl [Hretc]
  · iexact Hretc
  isplitl [Hres]
  · ileft; iframe Hres Hhi0; ipureintro; exact ⟨rfl, rfl, rfl⟩
  iexact Hbwt

end lemmas

end client
end EtcdGrove
end Perennial
