/-
**A substream across a reconnection** (D25; `newWatchClient`'s, the watch slice's unit W-C): what
`run` holds of a registered or queued substream (`wsRest`) and what its last goroutine left
(`resumeBody`, or `stopBody` once stopped for good), turned into the queued state of the new stream
(the substream re-created from its resume revision) and, for a live substream, the state its next
goroutine starts from. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchRun
public import Perennial.Golang.Theory.Chan.Idioms.SyncSpsc
public import Proof.go_etcd_io.etcd.client.v3.MapSplit

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

namespace client
section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A resume revision is a registration's base** (pure): the resume revision `rv` (`resumeOk`'s
facts) with the dispatch cursor's position `hl` then. -/
theorem resumeB_ok (pfx : GoString) (P : WsPrm GF) (rv hl c2 : w64) (hok : wsReqOk pfx P)
    (hc : P.γ.cpl = cplOf P)
    (h : (P.rev = W64 0 ∨ sint.Z P.rev ≤ sint.Z rv) ∧ (sint.Z hl < sint.Z rv ∨ sint.Z hl < 0) ∧
      (P.γ.cpl = true → c2 = rv - W64 1)) :
    regBOk P ⟨rv, cplOf P, hl⟩ := by
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨h1, h2, fun hcpl => ?_⟩
  rw [hc] at hcpl
  refine ⟨hcpl, ?_⟩
  obtain ⟨-, hr0⟩ := cplCond_rev hcpl
  have h0 : 0 ≤ sint.Z P.rev := hok.2.2.1
  have hne : sint.Z P.rev ≠ 0 := fun e => hr0 (by word)
  rcases h1 with e | e
  · exact absurd e hr0
  · show 1 ≤ sint.Z rv
    omega

/-- Two points-to of a `w64` field: their fractions add up to at most `1`. -/
theorem ptsto_w64_valid (l : Loc) (v1 v2 : w64) (dq1 dq2 : DFrac) :
    typedPointsto (GF := GF) l v1 dq1 ∗ typedPointsto (GF := GF) l v2 dq2 ⊢ ⌜✓ (dq1 • dq2)⌝ := by
  iintro ⟨H1, H2⟩
  icases typedPointsto_split _ _ _ $$ H1 with H1
  icases typedPointsto_split _ _ _ $$ H2 with H2
  rw [typedPointstoDef_heap, typedPointstoDef_heap]
  icombine H1 H2 gives %Hc
  ipureintro; exact Hc.1

/-- A half and a whole `w64` field: impossible. -/
theorem ptsto_w64_half_whole (l : Loc) (v1 v2 : w64) :
    typedPointsto (GF := GF) l v1 (DFrac.own (1 : Qp).half) ∗ typedPointsto (GF := GF) l v2 (DFrac.own 1) ⊢
      False := by
  iintro H
  ihave %Hv := ptsto_w64_valid l v1 v2 _ _ $$ H
  exfalso
  revert Hv
  simp only [CMRA.Valid, DFrac.op_own]
  intro h
  have : (1 / 2 : Rat) + 1 ≤ 1 := h
  grind

/-- A `w64` field in two halves. -/
theorem ptsto_w64_halves (l : Loc) (v : w64) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) := by
  have h := typedPointsto_frac_add (GF := GF) l v (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

/-- Two halves of a `Loc` field: the same value, the whole field. -/
theorem ptsto_loc_combine (l v1 v2 : Loc) :
    typedPointsto (GF := GF) l v1 (DFrac.own (1 : Qp).half) ∗
      typedPointsto (GF := GF) l v2 (DFrac.own (1 : Qp).half) ⊢
      ⌜v1 = v2⌝ ∗ typedPointsto (GF := GF) l v1 (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Heq
  subst Heq
  isplitr
  · ipureintro; rfl
  have h := typedPointsto_frac_add (GF := GF) l v1 (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iapply h.2
  iframe

/-- **A live substream across a reconnection** (its goroutine resumed: its state `wsRun`, its flag
`γx` still `false`): `run`'s state of the new stream, queued (a queued substream's as it was; a
registered one's from its resume revision, the registration's base the resume revision and the
cursor then), and the state the next goroutine starts from (half the request's `rev` field at the
resume revision, its lifetime starting at `recvc`'s position, `lifeStart`). -/
theorem recon_alive (V : WEnv GF) (γs γs' : StreamNames) (Dm Dm' : List v3rpc.WatchRespM)
    (P : WsPrm GF) (ph : WPh) (hph : (∃ X, ph = .reg X) ∨ (∃ si, ph = .queued si)) (k0 : Nat)
    (rv0 : w64) (rcv : List Loc) (nr : w64) :
    wsIs V P ∗ £ 1 ∗ wsRest V γs Dm P ph ∗ wsRun V P k0 rv0 rcv nr ∗ lifeStart P k0 ∗
      dghostVar P.γx (DFrac.own 1) false ⊢
    |={⊤}=> ∃ (k : Nat) (rv : w64) (rcv' : List Loc), wsRest V γs' Dm' P (.queued none) ∗
      wsRun V P k rv rcv' rv ∗ ⌜rcv'.length = k⌝ ∗ lifeStart P k ∗
      dghostVar P.γx (DFrac.own 1) false := by
  iintro ⟨#HP, Hlc, Hrest, Hrun, #Hls, Hgx⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, #Hrsp, -, -, %HPok, -⟩
  iunfold wsRun at Hrun
  icases Hrun with ⟨%osent, %oC, %bq, %b, %rcf, %t, %cl, %p0, Hcons, %Hk, Hoprod, Hoauth, %HoC,
    #Hcur, Hc2p, Hbuf, Hb, Hbe, Hrev, #Hrsm, Hretc, Hrr, Hbwt⟩
  rcases hph with ⟨X, rfl⟩ | ⟨si, rfl⟩
  · -- registered: re-created from its resume revision
    simp only [wsRest]
    icases Hrest with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, %HB, #HsoB, -, Hprod, Hauth, Hst, Hc2⟩
    icases Hst with (#Hx | ⟨%HCl, -, Hps⟩)
    · ihave %Hv := dghostVar_agree _ _ _ _ _ $$ Hgx Hx
      cases Hv
    imod sspsc_sync P.γr P.recvc (recvElem V P) (fun _ => iprop(True)) sent rcv $$ Hrsp Hlc Hprod
      Hcons with ⟨%Hsr, Hprod, Hcons⟩
    subst Hsr
    iunfold psAt at Hps
    icases Hps with ⟨%M, Hpa, %HM⟩
    -- the goroutine received the created response: the whole `rev` field
    icases Hrev with (⟨%Hk0, Hrev⟩ | ⟨%Hk0, Hrev⟩)
    · iunfold lifeStart at Hls
      ihave %HMk := ghost_map_lookup $$ Hpa Hls
      exfalso
      rw [HM k0 (by omega)] at HMk
      cases HMk
    icases Hrsm with ⟨%hl, %c2, #Hhl, #Hc2i, #Hrs⟩
    ihave #Hrs' := Hrs
    iunfold resumeOk at Hrs'
    icases Hrs' with ⟨%Hrsp', #Hso'⟩
    ihave %HCh := mono_list_auth_idx_lookup _ _ _ _ _ $$ Hauth Hhl
    unfold cur2St
    icases Hc2 with ⟨%C2, Hauth2, Hc2st⟩
    ihave ⟨Hauth2, Hgx, %HC2⟩ : iprop(monoListAuthOwn P.γh2 1 C2 ∗ dghostVar P.γx (DFrac.own 1) false ∗
        ⌜P.γ.cpl = true → C2.length = sent.length + 1 ∧ C2.getLast? = some (nr - W64 1)⌝)
        $$ [Hauth2 Hc2st Hgx]
    · cases hcp : P.γ.cpl
      · iframe Hauth2 Hgx; ipureintro; intro h; cases h
      icases Hc2st with (%Hf | #Hx | ⟨%HC2l, %c2', %HC2h, -⟩)
      · cases Hf
      · ihave %Hv := dghostVar_agree _ _ _ _ _ $$ Hgx Hx
        cases Hv
      icases Hc2i with (%Hf | #Hc2i)
      · cases Hf
      ihave %HC2i := mono_list_auth_idx_lookup _ _ _ _ _ $$ Hauth2 Hc2i
      iframe Hauth2 Hgx
      ipureintro
      intro _
      refine ⟨HC2l, ?_⟩
      rw [List.getLast?_eq_getElem?, HC2l, Nat.add_sub_cancel, HC2i, Hrsp'.2.2 hcp]
    -- the next lifetime's start, at `recvc`'s position
    imod ghost_map_insert_persist sent.length true (HM sent.length (Nat.le_refl _)) $$ Hpa
      with ⟨Hpa, #Hls'⟩
    icases ptsto_w64_halves _ _ $$ Hrev with ⟨Hrev1, Hrev2⟩
    imodintro
    iexists sent.length, nr, sent
    iframe Hgx
    isplitl [Hprod Hauth Hauth2 Hrev1 Hpa]
    · (try simp only [wsRest])
      ileft
      iexists ⟨nr, cplOf P, hl⟩, sent, C, C2
      iframe Hprod Hauth Hauth2
      isplitr
      · ipureintro; exact resumeB_ok V.pfx P nr hl c2 HPok.2.1 HPok.2.2 Hrsp'
      iframe Hso'
      isplitr
      · ipureintro
        refine ⟨HCl.1, ?_, HC2⟩
        rw [List.getLast?_eq_getElem?, HCl.1, Nat.add_sub_cancel, HCh]
      iframe Hrev1
      isplitl [Hpa]
      · unfold psSt
        iexists _
        iframe Hpa
        ipureintro
        refine ⟨GMap.lookup_insert _ _ _, fun j hj => ?_⟩
        rw [GMap.lookup_insert_ne _ _ (by omega)]
        exact HM j (by omega)
      unfold upAtOpt; itrivial
    isplitl [Hcons Hoprod Hoauth Hc2p Hbuf Hb Hbe Hrev2 Hretc Hrr Hbwt]
    · unfold wsRun
      iexists osent, oC, bq, b, rcf, t, cl, p0
      iframe Hcons Hoprod Hoauth Hcur Hc2p Hbuf Hb Hbe Hretc Hrr Hbwt
      isplitr
      · ipureintro; exact Nat.le_refl _
      isplitr
      · ipureintro; exact HoC
      isplitl [Hrev2]
      · ileft; iframe Hrev2; ipureintro; exact ⟨rfl, rfl⟩
      iexists hl, c2
      iframe Hhl Hc2i Hrs
    isplitr
    · ipureintro; rfl
    unfold lifeStart; iexact Hls'
  · -- queued: as it was, its goroutine still at its lifetime's start
    simp only [wsRest]
    icases Hrest with (⟨%B, %sent, %C, %C2, %HB, #HsoB, Hprod, Ha, Ha2, %HC, Hrv, Hps, -⟩ |
      ⟨#Hx, -⟩)
    rotate_left
    · ihave %Hv := dghostVar_agree _ _ _ _ _ $$ Hgx Hx
      cases Hv
    icases Hrev with (⟨%Hk0, Hrev⟩ | ⟨%Hk0, Hrev⟩)
    rotate_left
    · iexfalso
      iapply ptsto_w64_half_whole
      iframe Hrv Hrev
    obtain ⟨Hk0, rfl⟩ := Hk0
    imod sspsc_sync P.γr P.recvc (recvElem V P) (fun _ => iprop(True)) sent rcv $$ Hrsp Hlc Hprod
      Hcons with ⟨%Hsr, Hprod, Hcons⟩
    subst Hsr
    imodintro
    iexists k0, nr, sent
    iframe Hgx Hls
    isplitl [Hprod Ha Ha2 Hrv Hps]
    · (try simp only [wsRest])
      ileft
      iexists B, sent, C, C2
      iframe
      iframe #
      isplitr
      · ipureintro; exact HB
      isplitr
      · ipureintro; exact HC
      unfold upAtOpt; itrivial
    isplitl [Hcons Hoprod Hoauth Hc2p Hbuf Hb Hbe Hrev Hretc Hrr Hbwt]
    · unfold wsRun
      iexists osent, oC, bq, b, rcf, t, cl, p0
      iframe Hcons Hoprod Hoauth Hcur Hc2p Hbuf Hb Hbe Hretc Hrr Hbwt Hrsm
      isplitr
      · ipureintro; exact Hk
      isplitr
      · ipureintro; exact HoC
      ileft; iframe Hrev; ipureintro; exact ⟨Hk0, rfl⟩
    ipureintro; exact Hk0

/-- A `w64` field at any fraction, in two halves of it. -/
theorem ptsto_w64_split (l : Loc) (v : w64) (q : Qp) :
    typedPointsto (GF := GF) l v (DFrac.own q) ⊢
      typedPointsto (GF := GF) l v (DFrac.own q.half) ∗ typedPointsto (GF := GF) l v (DFrac.own q.half) := by
  have h := typedPointsto_frac_add (GF := GF) l v q.half q.half
  rw [Qp.half_add_half] at h
  exact h.1

/-- **A substream stopped for good across a reconnection**: `run`'s state of the new stream, queued
(a queued substream's as it was; a registered one's, stopped, from the resume revision its
goroutine left, with part of the request's `rev` field), what its goroutine left kept. -/
theorem recon_dead (V : WEnv GF) (γs γs' : StreamNames) (Dm Dm' : List v3rpc.WatchRespM)
    (P : WsPrm GF) (ph : WPh) (hph : (∃ X, ph = .reg X) ∨ (∃ si, ph = .queued si)) :
    wsIs V P ∗ wsRest V γs Dm P ph ∗ wsStopped P ∗ stopBody V P ⊢
    wsRest V γs' Dm' P (.queued none) ∗ wsStopped P ∗ stopBody V P := by
  iintro ⟨#HP, Hrest, #Hstp, Hsb⟩
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, -, -, -, %HPok, -⟩
  ihave #Hstp' := Hstp
  iunfold wsStopped at Hstp'
  icases Hstp' with ⟨#Hx, -⟩
  iframe Hstp
  rcases hph with ⟨X, rfl⟩ | ⟨si, rfl⟩
  · simp only [wsRest]
    icases Hrest with ⟨%B, %w, %rg, %fcs, %lo, %sent, %C, %HB, #HsoB, -, Hprod, Hauth, -, Hc2⟩
    unfold cur2St
    icases Hc2 with ⟨%C2, Hauth2, -⟩
    iunfold stopBody at Hsb
    icases Hsb with ⟨%rc, %q, %nr, %dc, Hoc, Hrc, Hret, Hrev, #Hrs, Hdnf⟩
    icases Hrs with ⟨%hl, %c2, #Hrs⟩
    ihave #Hrs' := Hrs
    iunfold resumeOk at Hrs'
    icases Hrs' with ⟨%Hrsp', #Hso'⟩
    icases ptsto_w64_split _ _ _ $$ Hrev with ⟨Hrev1, Hrev2⟩
    isplitl [Hprod Hauth Hauth2 Hrev1]
    · iright
      iframe Hx
      iexists ⟨nr, cplOf P, hl⟩, sent, C, C2, q.half
      iframe Hprod Hauth Hauth2 Hrev1 Hso'
      isplitr
      · ipureintro; exact resumeB_ok V.pfx P nr hl c2 HPok.2.1 HPok.2.2 Hrsp'
      unfold upAtOpt; itrivial
    unfold stopBody
    iexists rc, q.half, nr, dc
    iframe Hoc Hrc Hret Hrev2 Hdnf
    iexists hl, c2; iexact Hrs
  · simp only [wsRest]
    iframe Hsb
    icases Hrest with (⟨%B, %sent, %C, %C2, %HB, #HsoB, Hprod, Ha, Ha2, %HC, Hrv, Hps, -⟩ |
      ⟨-, %B, %sent, %C, %C2, %q, %HB, #HsoB, Hprod, Ha, Ha2, Hrv, -⟩)
    · ileft
      iexists B, sent, C, C2
      iframe
      iframe #
      isplitr
      · ipureintro; exact HB
      isplitr
      · ipureintro; exact HC
      unfold upAtOpt; itrivial
    · iright
      iframe Hx
      iexists B, sent, C, C2, q
      iframe
      iframe #
      isplitr
      · ipureintro; exact HB
      unfold upAtOpt; itrivial

/-- **The substreams `newWatchClient` queues** (pure): `resuming`'s and `substreams`' values (`mv`, in
the order of the map's keys `keys`), without repetition, the nils dropped, all of `U`. -/
theorem mv_facts (S : RunSt) (U : GMap Loc Unit) (keys : List w64) (hg : gOk S U)
    (hk1 : ∀ k, k ∈ keys ↔ (S.M !! k).isSome) (hk3 : keys.Nodup)
    (hdisj : ∀ X ws, S.M !! X = some ws → ws ∉ S.l) :
    (∀ ws, ws ∈ keys.filterMap (S.M !! ·) ↔ ∃ X, S.M !! X = some ws) ∧
      (keys.filterMap (S.M !! ·)).Nodup ∧
      ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => decide (x ≠ null))).Nodup ∧
      (∀ x ∈ (S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => decide (x ≠ null)),
        U !! x = some ()) := by
  obtain ⟨g1, g2, g3, g4, -, g6, -⟩ := hg
  have hmem : ∀ ws, ws ∈ keys.filterMap (S.M !! ·) ↔ ∃ X, S.M !! X = some ws := by
    intro ws
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨X, -, hX⟩; exact ⟨X, hX⟩
    · rintro ⟨X, hX⟩; exact ⟨X, (hk1 X).2 (by simp [hX]), hX⟩
  have hnd : (keys.filterMap (S.M !! ·)).Nodup :=
    List.Pairwise.filterMap (R := (· ≠ ·)) (fun X => S.M !! X)
      (fun X Y hXY b hb b' hb' => fun (hbb : b = b') => hXY (g2 X Y b hb (hbb ▸ hb'))) hk3
  refine ⟨hmem, hnd, ?_, ?_⟩
  · rw [List.filter_append]
    refine List.nodup_append.2 ⟨g4, hnd.filter _, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨X, hX⟩ := (hmem a).1 (List.mem_filter.1 hb).1
    exact hdisj X a hX (List.mem_filter.1 ha).1
  · intro x hx
    obtain ⟨hx, hn⟩ := List.mem_filter.1 hx
    rcases List.mem_append.1 hx with h | h
    · exact g3 x h (by simpa using hn)
    · obtain ⟨X, hX⟩ := (hmem x).1 h; exact g1 X x hX

/-! ## `run`'s substreams through `newWatchClient` -/

/-- **A substream as `run` holds it, its lifetime fixed** (`a`: its values, phase and lifetime; `wsElem`
but its id field and `donec`). -/
def wsElemC (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt) (ws : Loc)
    (a : WsPrm GF × WPh × LifePrm) : IProp GF :=
  iprop(⌜a.1.ws = ws ∧ phOk S ws a.2.1⌝ ∗ wsIs V a.1 ∗ wsRest V γs S.Dm a.1 a.2.1 ∗
    noCancelOk S a.1 a.2.1 ∗ lifeInvIs V G a.1 a.2.2 ∗ lifeTk V a.1 a.2.2 ∗
    (⌜a.2.1.isOrphan = true⌝ ∨ genOk a.1 a.2.2 n))

/-- **A substream whose goroutine's deposit `run` took** (`wsElemC` with the deposit for the token). -/
def wsElemT (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (S : RunSt) (ws : Loc)
    (a : WsPrm GF × WPh × LifePrm) : IProp GF :=
  iprop(⌜a.1.ws = ws ∧ phOk S ws a.2.1⌝ ∗ wsIs V a.1 ∗ wsRest V γs S.Dm a.1 a.2.1 ∗
    lifeInvIs V G a.1 a.2.2 ∗ (resumeBody V G a.1 ∨ wsStopped a.1 ∗ stopBody V a.1))

theorem wsElem_choose (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt)
    (U : GMap Loc Unit) :
    ([∗map] ws ↦ _u ∈ U, wsElem V G n γs S ws) ⊢ ∃ f : Loc → WsPrm GF × WPh × LifePrm,
      [∗map] ws ↦ _u ∈ U, (wsElemC V G n γs S ws (f ws) ∗ wsF ws go!"id" ↦ (f ws).2.1.id) ∗
        donecAt ws (lifeDn V G (f ws).1 (f ws).2.2) := by
  iintro H
  iapply bigSepM_choice_keys (dummyWsPrm G G.γr, WPh.orphan, (⟨null, G.γreq, G.γws, G.γws, 0⟩ : LifePrm))
    (fun ws a => iprop((wsElemC V G n γs S ws a ∗ wsF ws go!"id" ↦ a.2.1.id) ∗
      donecAt ws (lifeDn V G a.1 a.2.2))) U
  iapply (BigSepM.bigSepM_mono (fun {ws _} _ => by
    unfold wsElem
    iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
    unfold wsLife
    icases Hlife with ⟨%L, Hdc, #Hli, Htk, Hg⟩
    iexists (P, ph, L)
    unfold wsElemC
    iframe HP Hid Hrest Hnc Hli Htk Hg
    subst HPws
    iframe Hdc
    ipureintro; exact ⟨rfl, Hph⟩)) $$ H

/-- **Pure facts of each conjunct of `U`'s conjunction, for all keys.** -/
theorem bigSepM_pure_of (Φ : Loc → IProp GF) (Q : Loc → Prop) (U : GMap Loc Unit)
    (h : ∀ ws, Φ ws ⊢ Φ ws ∗ ⌜Q ws⌝) :
    ([∗map] ws ↦ _u ∈ U, Φ ws) ⊢ ([∗map] ws ↦ _u ∈ U, Φ ws) ∗ ⌜∀ ws, U !! ws = some () → Q ws⌝ := by
  refine (BigSepM.bigSepM_mono (fun {k _} _ => h k)).trans ?_
  rw [BigSepM.bigSepM_sep_eq]
  refine BI.sep_mono_right ?_
  refine BigSepM.bigSepM_pure_intro.trans (BI.pure_mono ?_)
  intro hall ws hws
  exact hall ws () hws

/-- The pure facts of `wsElemC`. -/
theorem wsElemCs_pure (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt)
    (U : GMap Loc Unit) (f : Loc → WsPrm GF × WPh × LifePrm) :
    ([∗map] ws ↦ _u ∈ U, wsElemC V G n γs S ws (f ws)) ⊢
      ([∗map] ws ↦ _u ∈ U, wsElemC V G n γs S ws (f ws)) ∗
        ⌜∀ ws, U !! ws = some () → (f ws).1.ws = ws ∧ phOk S ws (f ws).2.1⌝ := by
  refine bigSepM_pure_of _ (fun ws => (f ws).1.ws = ws ∧ phOk S ws (f ws).2.1) U (fun ws => ?_)
  unfold wsElemC
  iintro ⟨%H, R⟩
  iframe R
  ipureintro; exact ⟨H, H⟩

/-- **Taking what a lifetime's goroutine left** (`newWatchClient`, after `joinSubstreams`: its
`donec` closed, `lifeQ`): resumed or stopped for good. -/
theorem take_dep (V : WEnv GF) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) :
    £ 1 ∗ lifeInvIs V G P L ∗ lifeQ V G P L ∗ lifeTk V P L ⊢
      |={⊤}=> resumeBody V G P ∨ wsStopped P ∗ stopBody V P := by
  iintro ⟨Hlc, #Hli, #HQ, Htk⟩
  unfold lifeTk
  icases Htk with (Htk | Hd)
  rotate_left
  · imodintro; iright; iexact Hd
  unfold lifeQ
  icases HQ with ⟨-, #Ht, -⟩
  iinv Hli with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑lifeN) $$ Hlc Hi with Hi
  iunfold lifeSt at Hi
  icases Hi with (⟨Hγt, -⟩ | ⟨-, (⟨#Hstp, (Hsb | Htk2)⟩ | ⟨#Hlb, (Hrb | Htk2)⟩)⟩)
  · ihave %H := dghostVar_agree _ _ _ _ _ $$ Hγt Ht
    cases H
  · imod Hclose $$ [Htk] with -
    · inext; iunfold lifeSt; iright; iframe Ht; ileft; iframe Hstp; iright; iexact Htk
    imodintro; iright; iframe Hstp Hsb
  · iexfalso; iapply ownTok_excl; iframe
  · imod Hclose $$ [Htk] with -
    · inext; iunfold lifeSt; iright; iframe Ht; iright; iframe Hlb; iright; iexact Htk
    imodintro; ileft; iexact Hrb
  · iexfalso; iapply ownTok_excl; iframe

/-- **A list of `U`'s keys taken out of its conjunction** (no repetition). -/
theorem bigSepM_take_list (Φ : Loc → IProp GF) (U : GMap Loc Unit) :
    ∀ l : List Loc, l.Nodup → (∀ x ∈ l, U !! x = some ()) →
    ([∗map] ws ↦ _u ∈ U, Φ ws) ⊢ ([∗list] ws ∈ l, Φ ws) ∗ ([∗map] ws ↦ _u ∈ U, ⌜ws ∈ l⌝ ∨ Φ ws) := by
  intro l
  induction l with
  | nil =>
    intro _ _
    iintro H
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by iintro H; iright; iexact H)) $$ H
  | cons x l ih =>
    intro hnd hU
    have hx : U !! x = some () := hU x (List.mem_cons_self ..)
    have hxl : x ∉ l := (List.nodup_cons.1 hnd).1
    iintro H
    icases ih (List.nodup_cons.1 hnd).2 (fun y hy => hU y (List.mem_cons_of_mem _ hy)) $$ H
      with ⟨Hl, HR⟩
    icases (BigSepM.bigSepM_delete hx).1 $$ HR with ⟨Hx, HR⟩
    icases Hx with (%Hc | Hx)
    · exact absurd Hc hxl
    isplitl [Hx Hl]
    · iapply BigSepL.bigSepL_cons.2
      iframe
    iapply (BigSepM.bigSepM_delete hx).2
    isplitr
    · ileft; ipureintro; exact List.mem_cons_self ..
    iapply (BigSepM.bigSepM_mono (fun {k _} _ => by
      iintro (%Hc | H)
      · ileft; ipureintro; exact List.mem_cons_of_mem _ Hc
      · iright; iexact H)) $$ HR

/-- **A list of `U`'s keys put back into its conjunction** (the reverse of `bigSepM_take_list`). -/
theorem bigSepM_give_list (Φ : Loc → IProp GF) (U : GMap Loc Unit) :
    ∀ l : List Loc, l.Nodup → (∀ x ∈ l, U !! x = some ()) →
    ([∗list] ws ∈ l, Φ ws) ∗ ([∗map] ws ↦ _u ∈ U, ⌜ws ∈ l⌝ ∨ Φ ws) ⊢ [∗map] ws ↦ _u ∈ U, Φ ws := by
  intro l
  induction l with
  | nil =>
    intro _ _
    iintro ⟨-, H⟩
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by
      iintro (%Hc | H)
      · simp at Hc
      · iexact H)) $$ H
  | cons x l ih =>
    intro hnd hU
    have hx : U !! x = some () := hU x (List.mem_cons_self ..)
    have hxl : x ∉ l := (List.nodup_cons.1 hnd).1
    iintro ⟨Hl, HR⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hx, Hl⟩
    iapply ih (List.nodup_cons.1 hnd).2 (fun y hy => hU y (List.mem_cons_of_mem _ hy))
    iframe Hl
    icases (BigSepM.bigSepM_delete hx).1 $$ HR with ⟨-, HR⟩
    iapply (BigSepM.bigSepM_delete hx).2
    isplitl [Hx]
    · iright; iexact Hx
    iapply (BigSepM.bigSepM_mono (fun {k _} hk => by
      iintro (%Hc | H)
      · ileft; ipureintro
        rcases List.mem_cons.1 Hc with e | h
        · subst e
          change (GMap.delete k U) !! k = _ at hk
          rw [GMap.lookup_delete] at hk; cases hk
        · exact h
      · iright; iexact H)) $$ HR

/-- **After a reconnection a substream's state names no stream** (no substream registered, none
answered or pending): any next stream's. -/
theorem wsElem_recon_any (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs γs' : StreamNames)
    (S : RunSt) (l' : List Loc) (ws : Loc) :
    wsElem V G n γs (S.reconnect l') ws ⊢ wsElem V G n γs' (S.reconnect l') ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  iexists P, ph
  iframe HP Hid Hnc Hlife
  isplitr
  · ipureintro; exact ⟨HPws, Hph⟩
  cases ph with
  | reg X => exfalso; simp [phOk, RunSt.reconnect, GMap.lookup_empty] at Hph
  | closedRun X => exfalso; simp [phOk, RunSt.reconnect, GMap.lookup_empty] at Hph
  | queued si =>
    cases si with
    | some i =>
      exfalso
      have := (Hph.2.2.2.1 i rfl).1
      simp [RunSt.reconnect] at this
    | none =>
      simp only [wsRest]
      icases Hrest with (⟨%B, %sent, %C, %C2, %HB, #HsoB, Hprod, Ha, Ha2, %HC, Hrv, Hps, -⟩ |
        ⟨#Hx, %B, %sent, %C, %C2, %q, %HB, #HsoB, Hprod, Ha, Ha2, Hrv, -⟩)
      · ileft
        iexists B, sent, C, C2
        iframe
        iframe #
        isplitr
        · ipureintro; exact HB
        isplitr
        · ipureintro; exact HC
        unfold upAtOpt; itrivial
      · iright
        iframe Hx
        iexists B, sent, C, C2, q
        iframe
        iframe #
        isplitr
        · ipureintro; exact HB
        unfold upAtOpt; itrivial
  | orphan => simp only [wsRest]; iexact Hrest
  | closed => simp only [wsRest]; iexact Hrest

/-! ### At another member (W3b) -/

set_option maxHeartbeats 1000000 in
/-- A substream's facts read no member. -/
theorem wsIs_atIdx (V : WEnv GF) (i : Nat) (P : WsPrm GF) : wsIs (V.atIdx i) P = wsIs V P := rfl

/-- A goroutine's buffer reads no member (by recursion: `rfl` does not see through it). -/
theorem bufE_atIdx (V : WEnv GF) (i : Nat) (P : WsPrm GF) :
    ∀ (a : Nat) (l : List (Nat × Loc)) (n : Nat), bufE (V.atIdx i) P a l n = bufE V P a l n
  | _, [], _ => rfl
  | a, x :: rest, n => by
    simp only [bufE]
    rw [bufE_atIdx V i P (x.1 + 1) rest n]
    rfl

theorem wsRun_atIdx (V : WEnv GF) (i : Nat) (P : WsPrm GF) (k0 : Nat) (rv0 : w64)
    (rcv : List Loc) (nr : w64) : wsRun (V.atIdx i) P k0 rv0 rcv nr = wsRun V P k0 rv0 rcv nr := by
  unfold wsRun
  simp only [bufE_atIdx]
  rfl

theorem resumeBody_atIdx (V : WEnv GF) (i : Nat) (G : WgsPrm GF) (P : WsPrm GF) :
    resumeBody (V.atIdx i) G P = resumeBody V G P := by
  unfold resumeBody
  simp only [wsRun_atIdx]

theorem lifeSt_atIdx (V : WEnv GF) (i : Nat) (G : WgsPrm GF) (P : WsPrm GF) (L : LifePrm) :
    lifeSt (V.atIdx i) G P L = lifeSt V G P L := by
  unfold lifeSt
  simp only [resumeBody_atIdx]
  rfl

/-- A substream's lifetime reads no member. -/
theorem wsLife_atIdx (V : WEnv GF) (i : Nat) (G : WgsPrm GF) (n : Nat) (P : WsPrm GF) (o : Bool) :
    wsLife (V.atIdx i) G n P o = wsLife V G n P o := by
  unfold wsLife lifeDn lifeQ lifeInvIs
  simp only [lifeSt_atIdx]
  rfl

set_option maxHeartbeats 1000000 in
/-- A queued, orphan or closed substream's state reads no member. -/
theorem wsRest_atIdx (V : WEnv GF) (i : Nat) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (P : WsPrm GF) (ph : WPh) (h : ∀ X, ph ≠ .reg X) :
    wsRest (V.atIdx i) γs Dm P ph = wsRest V γs Dm P ph := by
  cases ph with
  | reg X => exact absurd rfl (h X)
  | _ => rfl

/-- **A gRPC watch stream at another member** (W3b): its fields and channels read no member
(`reqP`, `closingP`, `respcE`: each epoch's responses at the epoch's member); the facts it rests on
are the member's (`watchConnFacts_atIdx`). -/
theorem isWGS_atIdx (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (i : Nat) (hi : i < V.nm) :
    isWGS V G callSl ⊢ isWGS (V.atIdx i) G callSl := by
  iintro #H
  have e1 : reqP (V.atIdx i) = reqP V := rfl
  have e2 : closingP (V.atIdx i) G = closingP V G := rfl
  have e3 : respcE (V.atIdx i) G.γep = respcE V G.γep := rfl
  unfold isWGS
  rw [e1, e2, e3]
  icases H with ⟨%H1, #H2, #Hsf, %H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11, #H12, #H13, #H14,
    #H15, #H16, #H17, #H18, #H19, #H20, #H21, #H22, #H23⟩
  iunfold watchSrvFacts at Hsf
  icases Hsf with ⟨#Hstub, #Hconn⟩
  ihave #Hconn' := watchConnFacts_atIdx V i hi $$ Hconn
  simp only [WEnv.atIdx]
  iframe #
  isplitr
  · ipureintro; exact H1
  isplitr
  · iunfold watchSrvFacts; iframe #
  ipureintro; exact H4

/-- **A reconnection's substream at any member** (W3b): every substream is queued, orphan or
closed (`RunSt.reconnect`), whose state reads no member. -/
theorem wsElem_recon_at (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames)
    (S : RunSt) (l' : List Loc) (ws : Loc) (i : Nat) :
    wsElem V G n γs (S.reconnect l') ws ⊢ wsElem (V.atIdx i) G n γs (S.reconnect l') ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest, #Hnc, Hlife⟩
  iexists P, ph
  rw [wsIs_atIdx, wsLife_atIdx]
  have hnr : ∀ X, ph ≠ .reg X := by
    intro X hX; subst hX
    simp [phOk, RunSt.reconnect, GMap.lookup_empty] at Hph
  rw [wsRest_atIdx V i γs _ P ph hnr]
  iframe HP Hid Hnc Hlife Hrest
  ipureintro; exact ⟨HPws, Hph⟩

/-- **A substream neither registered nor queued across a reconnection** (server-cancelled, refused,
or closed): its state of the next generation (`closedRun` becomes `closed`). -/
theorem recon_other (V : WEnv GF) (G : WgsPrm GF) (n : Nat) (γs : StreamNames) (S : RunSt)
    (l' : List Loc) (ws : Loc) (a : WsPrm GF × WPh × LifePrm)
    (hph : (∃ X, a.2.1 = .closedRun X) ∨ a.2.1 = .orphan ∨ a.2.1 = .closed)
    (hrec : phOk (S.reconnect l') ws a.2.1.recon) :
    wsElemC V G n γs S ws a ∗ wsF ws go!"id" ↦ W64 (-1) ∗ donecAt ws (lifeDn V G a.1 a.2.2) ⊢
      wsElem V G (n + 1) γs (S.reconnect l') ws := by
  iintro ⟨HC, Hid, Hdc⟩
  unfold wsElemC
  icases HC with ⟨⟨%HPws, -⟩, #HP, Hrest, -, #Hli, Htk, Hg⟩
  subst HPws
  unfold wsElem wsLife
  iexists a.1, a.2.1.recon
  isplitr
  · ipureintro; exact ⟨rfl, hrec⟩
  iframe HP
  rw [WPh.recon_id]
  iframe Hid
  rcases hph with ⟨X, hX⟩ | hX | hX
  · rw [hX]
    simp only [wsRest, WPh.recon, noCancelOk, WPh.isOrphan]
    iintuitionistic Hrest
    iframe Hrest
    isplitr
    · itrivial
    iexists a.2.2
    iframe Hdc Hli Htk
    iright; unfold genOk; iright; iexact Hrest
  · rw [hX]
    simp only [wsRest, WPh.recon, noCancelOk, WPh.isOrphan]
    isplitr
    · itrivial
    isplitr
    · itrivial
    iexists a.2.2
    iframe Hdc Hli Htk
    ileft; ipureintro; simp
  · rw [hX]
    simp only [wsRest, WPh.recon, noCancelOk, WPh.isOrphan]
    iintuitionistic Hrest
    iframe Hrest
    isplitr
    · itrivial
    iexists a.2.2
    iframe Hdc Hli Htk
    iright; unfold genOk; iright; iexact Hrest

end defs
end client

end EtcdGrove
end Perennial
