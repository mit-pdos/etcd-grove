/-
**A watch stream's handle and its client's updates** (stage 2 of the mvcc API proof, the stream's
contracts: `notes/mvcc-api-invariants.md`, "Hand-off: stage 2, the registration"; 2026-11-05).
Lean-first (no Rocq counterpart).

Over the sealed definitions of `Api.lean` (imported with `import all`), for the proofs of the
`WatchStream` contracts at `*watchStream`:
- `isMvccWatchStream_open`: what a stream's handle holds (its channel's invariant, the stream over
  the watchable store at that channel, the store's watch-token and readers' pools);
- `watch_regCb`: the store's registration callback (`regCb`) built from `Watch`'s update, the
  stream's half of the client's history and the stream's id map: at the registration it fires the
  update (the store's state agreeing with the client's: the committed log is `σ.log`, nothing
  pending), appends the registration to the stream's history at the exact sent count
  (`chanApiAt_reg`) and assigns the id;
- `stream_fire_plain`: `Watch`'s update on a closed stream (no event), from the stream's half of
  the client's history;
- `cancel_fire`, `close_fire`: `Cancel`'s and `Close`'s updates at the channel's invariant (the
  cancel's token for a registered watcher).

Its statements mix the sealed names with the internals' (a stream's name is its `WsAbs`), which
only a module that sees the sealed bodies can state: so they are private to this module, and the
contracts' proofs `import all` it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc sent

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **What a stream's handle holds** (`isMvccWatchStream` unsealed). -/
theorem isMvccWatchStream_open (w : Loc) (γ : MvccName) (ι : WsName) :
    isMvccWatchStream (GF := GF) (interface.mkOk (go.GoType.PointerType watchStream.ty) #w) γ ι ⊢
      ∃ (γw : WsNames) (γc : WatchChanNames) (s st : Loc) (γo : WsStreamNames) (γp : GName),
        ⌜(ι : WsAbs) = wsAbsOf γw (ι : WsAbs).ch γc ∧ γw.st = (γ : StoreNames)⌝ ∗
        inv watchN (watchChanInv γw (ι : WsAbs).ch γc) ∗
        isWatchStreamAt w (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s)
          (storeWatchParams s st γw) γo (ι : WsAbs).ch γc ∗
        watchTokPool γw ∗ threadPool.isThreadPool watchRdPoolN γp (watchReader s st γw) ∗
        progFact γc.prog := by
  unfold isMvccWatchStream isMvccWatchStreamRest
  iintro ⟨-, #⟨%γw, %γc, %w', %s, %st, %γo, %γp, %h, -, #Hinv, #Hws, #Ht, #Hp, #Hpf⟩⟩
  obtain ⟨hι, hγ, -, hw⟩ := h
  have hw' : w' = w := by
    rw [interface_mkOk_inj] at hw
    exact (go.intoVal_inj hw.2).symm
  subst hw'
  iexists γw, γc, s, st, γo, γp
  iframe Hinv Hws Ht Hp Hpf
  ipureintro; exact ⟨hι, hγ⟩

/-- `Watch`'s update (the contract's, as the stream's proof is handed it). -/
abbrev watchAu (γ : MvccName) (ι : WsName) (kk e : List w8) (endk : GoSlice) (startRev : w64)
    (fs : List (EvM → Bool)) (Q : MvccState → StreamState → w64 → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState) (S : StreamState), mvccState γ σ ∗ wsState ι S }>
      @ ⊤ \ ↑mvccN, ∅
    <{ ∀∀ (id : w64) (k : Nat), mvccState γ σ ∗
        (if S.closed then ⌜id = W64 (-1)⌝ ∗ wsState ι S
         else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ wsSentLb ι k ∗
           wsState ι (S.register id
             ⟨watchRangeOf kk e endk startRev id, fs, watchLo σ startRev, k, true⟩)),
      COMM Q σ S id }>)

/-- **What the registration callback gives the stream back** for the watcher `w` of id `id`: the
update's commit (an open stream's), the id map at the next id, and the stream's half of the
client's history at the registration (its replay the registration's). -/
def watchBack (Q : MvccState → StreamState → w64 → IProp GF) (γc : WatchChanNames)
    (γo : WsStreamNames) (lm : List SEv) (id : w64) (_w : Loc) : IProp GF :=
  iprop((∃ (σ : MvccState) (S : StreamState), Q σ S id ∗ ⌜S.closed = false⌝) ∗
    idsInv γo (id + W64 1) ∗
    ∃ lm' : List SEv, ghostVar γc.acl (1 : Qp).half lm' ∗
      ⌜∀ d, ∃ wi : WInfo, wi.live = true ∧ (replay d lm').S = (replay d lm).S.register id wi⌝)

theorem mvccN_watchN : (⊤ \ ↑mvccN : CoPset) ⊆ ⊤ \ ↑watchN := by
  intro p hp
  rw [CoPset.in_diff] at hp ⊢
  exact ⟨hp.1, fun h => hp.2 (nclose_subseteq mvccN "watch" p h)⟩

/-- **The registration callback from `Watch`'s update** (see the file header). -/
theorem watch_regCb (γw : WsNames) (ch : Loc) (γc : WatchChanNames) (γo : WsStreamNames)
    (kk e : List w8) (endk : GoSlice) (startRev id : w64) (fs : List (EvM → Bool))
    (Q : MvccState → StreamState → w64 → IProp GF) (nextID : w64) (CM : GMap w64 GoFunc)
    (CS : List w64) (lm : List SEv) (IDS : GMap w64 Loc) (hids : γo.ids = γc.ids)
    (hrel : ∀ d, wsRel nextID false CM CS (replay d lm).S)
    (hid0 : 0 ≤ sint.Z id) (hid1 : sint.Z nextID ≤ sint.Z id) (hidb : sint.Z id < 2 ^ 63 - 1)
    (hIDS : ∀ i, (IDS !! i).isSome → 0 ≤ sint.Z i ∧ sint.Z i < sint.Z id) :
    ghostVar (GF := GF) γc.acl (1 : Qp).half lm ∗ ghostMapAuth γo.ids 1 IDS ∗
      ghostMapAuth γo.fresh 1 IDS ∗
      watchAu (γw.st : MvccName) (wsAbsOf γw ch γc : WsName) kk e endk startRev fs Q ⊢
      regCb γw ch γc (watchRangeOf kk e endk startRev id) fs (watchBack Q γc γo lm id) := by
  iintro ⟨Hm, Hida, Hidf, Hau⟩
  iunfold regCb
  iintro %w %fg %lo %l %dec %recv %C %c %q %q2 %hwlo #Hsf Hapi HX Hpnd
  obtain ⟨hw, hlo⟩ := hwlo
  have hs1 : sint.Z (id + W64 1) = sint.Z id + 1 := by word
  imod idsInv_assign γo γc hids IDS (id + W64 1) id w ⟨hid0, by omega, hIDS⟩ $$ [$Hida $Hidf]
    with ⟨#Hida, Hids, -, -⟩
  -- the update, at the registration
  ihave Hau := atomic_update_mask_weaken mvccN_watchN $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %S, ⟨Hσ, HS⟩, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  -- the store's state agrees with the client's
  iunfold mvccState at Hσ
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach, #Hrcm⟩
  iunfold revMuAbs at HX
  icases HX with ⟨HXa, HXc⟩
  iunfold absPart at Ha HXa
  icombine Ha HXa gives %Hag
  iunfold pndPart at Hp Hpnd
  icombine Hp Hpnd gives %Hpg
  have hlog : σ.log = C := (Prod.mk.inj Hag.2).1
  have hpend : σ.pending = none := Hpg.2
  -- the client's stream state is the stream's
  iunfold wsState at HS
  icases wsStateI_cl _ S lm $$ [$HS $Hm] with ⟨HS, Hm, %Hd⟩
  obtain ⟨d0, hd0⟩ := Hd
  obtain ⟨hcl, hb, -, -, -⟩ := hrel d0
  rw [hd0] at hcl hb
  have hnone : S.ws !! id = none := by
    cases hS : S.ws !! id with
    | none => rfl
    | some w0 => have := hb id (by rw [hS]; rfl); omega
  have hneg : id ≠ W64 (-1) := by intro h; rw [h] at hid0; revert hid0; decide
  -- the registration, at the exact sent count
  let rg := watchRangeOf kk e endk startRev id
  imod chanApiAt_reg _ l dec recv S lm id rg fg fs lo hnone hneg $$ [$Hapi $HS $Hm $Hsf]
    with ⟨%dec', Hapi, HS, Hm, %Hrep, #Hslb⟩
  have hlo' : lo = watchLo σ startRev := by
    rw [hlo]; unfold watchLo; rw [hlog]
    show (if startRev = W64 0 then C.length else (sint.Z startRev).toNat) = _
    rfl
  imod Hcommit $$ %id %(sendsOf l).length [Ha Hp Hcr Hnl HS] with HQ
  · iunfold mvccState
    iunfold mvccStateI
    iunfold absPart
    iunfold pndPart
    isplitl [Ha Hp Hcr Hnl]
    · iframe Hrcm; iframe Ha Hp Hcr Hnl; ipureintro; exact Hreach
    rw [if_neg (by rw [hcl]; decide)]
    isplitr
    · ipureintro; exact ⟨hnone, hneg, hpend⟩
    isplitr
    · iunfold wsSentLb; iexact Hslb
    iunfold wsState
    rw [← hlo']
    iexact HS
  imodintro
  iexists dec'
  rw [show (watchRangeOf kk e endk startRev id).id = id from rfl]
  iframe Hida Hapi
  isplitl [HQ Hids Hm]
  · iunfold watchBack
    isplitl [HQ]
    · iexists σ, S; iframe HQ; ipureintro; exact hcl
    iframe Hids
    iexists _
    iframe Hm
    ipureintro
    intro d
    exact ⟨_, rfl, Hrep d⟩
  iunfold revMuAbs
  iunfold absPart
  iunfold pndPart
  iframe HXa HXc Hpnd

/-- **`Watch`'s update on a closed stream** (no event): the client's state is the stream's, closed. -/
theorem watch_fire_closed (γw : WsNames) (ch : Loc) (γc : WatchChanNames)
    (kk e : List w8) (endk : GoSlice) (startRev : w64) (fs : List (EvM → Bool))
    (Q : MvccState → StreamState → w64 → IProp GF) (nextID : w64) (CM : GMap w64 GoFunc)
    (CS : List w64) (lm : List SEv) (hrel : ∀ d, wsRel nextID true CM CS (replay d lm).S) :
    ghostVar (GF := GF) γc.acl (1 : Qp).half lm ∗
      watchAu (γw.st : MvccName) (wsAbsOf γw ch γc : WsName) kk e endk startRev fs Q ⊢
      |={⊤}=> ghostVar γc.acl (1 : Qp).half lm ∗
        ∃ (σ : MvccState) (S : StreamState), Q σ S (W64 (-1)) ∗ ⌜S.closed = true⌝ := by
  iintro ⟨Hm, Hau⟩
  ihave Hau := atomic_update_mask_weaken (Eo2 := ⊤) CoPset.subseteq_top $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, %S, ⟨Hσ, HS⟩, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  iunfold wsState at HS
  icases wsStateI_cl _ S lm $$ [$HS $Hm] with ⟨HS, Hm, %Hd⟩
  obtain ⟨d0, hd0⟩ := Hd
  obtain ⟨hcl, -⟩ := hrel d0
  rw [hd0] at hcl
  imod Hcommit $$ %(W64 (-1)) %0 [Hσ HS] with HQ
  · iframe Hσ
    rw [if_pos hcl]
    isplitr
    · ipureintro; rfl
    iunfold wsState; iexact HS
  imodintro
  iframe Hm
  iexists σ, S
  iframe HQ
  ipureintro; exact hcl

/-- **The channel invariant's API part, out and back** (the rest of the invariant framed). -/
theorem watchChanInv_api (γw : WsNames) (ch : Loc) (γc : WatchChanNames) :
    watchChanInv (GF := GF) γw ch γc ⊢ ∃ sent recv : List RespM, chanApi γw ch γc sent recv ∗
      (chanApi γw ch γc sent recv -∗ watchChanInv γw ch γc) := by
  iintro Hi
  iunfold watchChanInv at Hi
  icases Hi with ⟨%s0, %sent, %recv, %vs, %L, Hi⟩
  iNamed Hi
  iexists sent, recv
  iframe Hapi
  iintro Hapi
  iunfold watchChanInv
  iexists s0, sent, recv, vs, L
  simp only [named]
  iframe
  iframe #
  ipureintro; exact ⟨Hpre, Hinfl, Hnd⟩

/-- `Cancel`'s update (the contract's). -/
abbrev cancelAu (ι : WsName) (id : w64) (Q : StreamState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (S : StreamState), wsState ι S }> @ ⊤ \ ↑mvccN, ∅
        <{ wsState ι (S.cancel id), COMM Q S }>)

/-- **`Cancel`'s update at its first check** (the channel invariant open): the client's state
`S` the stream's (its relation to the stream's fields, `wsRel`), the cancel appended to the
history, the stream's half of the client's history with it, and for a watcher of `S` its
cancel's tokens (the history's, `chanCancelTok`, and the stream's, `idCancelled`). -/
theorem cancel_fire (γw : WsNames) (ch : Loc) (γc : WatchChanNames) (γo : WsStreamNames) (id : w64)
    (Q : StreamState → IProp GF) (nextID : w64) (closed : Bool) (CM : GMap w64 GoFunc)
    (CS : List w64) (lm : List SEv)
    (hrel : ∀ d, wsRel nextID closed CM CS (replay d lm).S) :
    watchChanInv (GF := GF) γw ch γc ∗ ghostVar γc.acl (1 : Qp).half lm ∗ monoListAuthOwn γo.cs 1 CS ∗
      cancelAu (wsAbsOf γw ch γc : WsName) id Q ⊢
      |={⊤ \ ↑watchN}=> watchChanInv γw ch γc ∗
        ∃ (lm' : List SEv) (CS' : List w64) (S : StreamState),
          ghostVar γc.acl (1 : Qp).half lm' ∗ monoListAuthOwn γo.cs 1 CS' ∗ Q S ∗
          ⌜wsRel nextID closed CM CS S ∧ ∀ d, wsRel nextID closed CM CS' (replay d lm').S⌝ ∗
          (⌜S.ws !! id = none⌝ ∨ (chanCancelTok γc id ∗ idCancelled γo id)) := by
  iintro ⟨Hi, Hm, Hcs, Hau⟩
  icases watchChanInv_api γw ch γc $$ Hi with ⟨%sent, %recv, Hapi, Hback⟩
  iunfold chanApi at Hapi
  icases Hapi with ⟨%l, %dec, Hapi, %Hsl, #Hwit⟩
  ihave Hau := atomic_update_mask_weaken mvccN_watchN $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%S, HS, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  iunfold wsState at HS
  icases wsStateI_cl _ S lm $$ [$HS $Hm] with ⟨HS, Hm, %Hd⟩
  obtain ⟨d0, hd0⟩ := Hd
  have hrelS : wsRel nextID closed CM CS S := hd0 ▸ hrel d0
  imod chanApiAt_cancel _ l dec _ S lm id $$ [$Hapi $HS $Hm] with ⟨Hapi, HS, Hm, %Hc⟩
  obtain ⟨hS, hrep⟩ := Hc
  imod Hcommit $$ [HS] with HQ
  · iunfold wsState; iexact HS
  -- the cancel's tokens, for a watcher of `S`
  have hdec : ∀ d, ((replay d lm).S.ws !! id).isSome = (S.ws !! id).isSome := fun d => by
    rw [← hd0]; exact replay_ws_isSome d d0 lm id
  cases hw : S.ws !! id with
  | none =>
    have hCS : ∀ d, wsRel nextID closed CM CS (replay d (l ++ [.cancel id])).S := fun d => by
      rw [hrep d]
      have := wsRel_cancel (hrel d) id
      rwa [hdec d, hw, Option.isSome_none, if_neg (by decide)] at this
    ihave Hi := Hback $$ [Hapi]
    · iunfold chanApi
      iexists l ++ [.cancel id], dec
      iframe Hapi
      isplitr
      · ipureintro; rw [sendsOf_append, Hsl]; simp [sendsOf]
      iapply regWit_app γc l _ (fun _ _ _ _ h => by cases h) $$ Hwit
    imodintro
    iframe Hi
    iexists l ++ [.cancel id], CS, S
    iframe Hm Hcs HQ
    isplitr
    · ipureintro; exact ⟨hrelS, hCS⟩
    ileft; ipureintro; exact hw
  | some w0 =>
    icases chanApiAt_cancel_tok _ l dec _ id w0 (by rw [hS]; exact hw) $$ Hapi with ⟨Hapi, #Htok⟩
    have hCS : ∀ d, wsRel nextID closed CM (CS ++ [id]) (replay d (l ++ [.cancel id])).S :=
      fun d => by
        rw [hrep d]
        have := wsRel_cancel (hrel d) id
        rwa [hdec d, hw, Option.isSome_some, if_pos rfl] at this
    ihave Hi := Hback $$ [Hapi]
    · iunfold chanApi
      iexists l ++ [.cancel id], dec
      iframe Hapi
      isplitr
      · ipureintro; rw [sendsOf_append, Hsl]; simp [sendsOf]
      iapply regWit_app γc l _ (fun _ _ _ _ h => by cases h) $$ Hwit
    imod monoListAuthOwn_update_app [id] $$ Hcs with ⟨Hcs, #Hlb⟩
    imodintro
    iframe Hi
    iexists l ++ [.cancel id], CS ++ [id], S
    iframe Hm Hcs HQ
    isplitr
    · ipureintro; exact ⟨hrelS, hCS⟩
    iright
    isplitr
    · iunfold cancelTok at Htok
      iunfold chanCancelTok
      iexact Htok
    iunfold idCancelled
    iexists CS ++ [id]
    iframe Hlb
    ipureintro; simp

/-- `Close`'s update (the contract's). -/
abbrev closeAu (ι : WsName) (Q : StreamState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (S : StreamState), wsState ι S ∗ ⌜S.closed = false⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ wsState ι S.close, COMM Q S }>)

/-- **`Close`'s update** (the channel invariant open): the stream was open (the client's state is
the stream's), the close appended to the history, the stream's half of the client's history with
it. -/
theorem close_fire (γw : WsNames) (ch : Loc) (γc : WatchChanNames) (Q : StreamState → IProp GF)
    (nextID : w64) (closed : Bool) (CM : GMap w64 GoFunc) (CS : List w64) (lm : List SEv)
    (hrel : ∀ d, wsRel nextID closed CM CS (replay d lm).S) :
    watchChanInv (GF := GF) γw ch γc ∗ ghostVar γc.acl (1 : Qp).half lm ∗
      closeAu (wsAbsOf γw ch γc : WsName) Q ⊢
      |={⊤ \ ↑watchN}=> watchChanInv γw ch γc ∗
        ∃ (lm' : List SEv) (S : StreamState), ghostVar γc.acl (1 : Qp).half lm' ∗ Q S ∗
          ⌜closed = false ∧ ∀ d, wsRel nextID true CM CS (replay d lm').S⌝ := by
  iintro ⟨Hi, Hm, Hau⟩
  icases watchChanInv_api γw ch γc $$ Hi with ⟨%sent, %recv, Hapi, Hback⟩
  iunfold chanApi at Hapi
  icases Hapi with ⟨%l, %dec, Hapi, %Hsl, #Hwit⟩
  ihave Hau := atomic_update_mask_weaken mvccN_watchN $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%S, ⟨HS, %HSo⟩, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  iunfold wsState at HS
  icases wsStateI_cl _ S lm $$ [$HS $Hm] with ⟨HS, Hm, %Hd⟩
  obtain ⟨d0, hd0⟩ := Hd
  have hcl : closed = false := by
    have := (hrel d0).1; rw [hd0, HSo] at this; exact this.symm
  subst hcl
  imod chanApiAt_close _ l dec _ S lm $$ [$Hapi $HS $Hm] with ⟨Hapi, HS, Hm, %Hc⟩
  obtain ⟨-, hrep⟩ := Hc
  imod Hcommit $$ [HS] with HQ
  · iunfold wsState; iexact HS
  ihave Hi := Hback $$ [Hapi]
  · iunfold chanApi
    iexists l ++ [.close], dec
    iframe Hapi
    isplitr
    · ipureintro; rw [sendsOf_append, Hsl]; simp [sendsOf]
    iapply regWit_app γc l _ (fun _ _ _ _ h => by cases h) $$ Hwit
  imodintro
  iframe Hi
  iexists l ++ [.close], S
  iframe Hm HQ
  ipureintro
  refine ⟨rfl, fun d => ?_⟩
  rw [hrep d]
  exact wsRel_close (hrel d)

/-- **`Rev`'s update at the store's read** (`readCb`, run by `store.Read` under `s.revMu`): the
client's state agrees with the slot's committed log `L` (unchanged), the update's commit `Q σ`
returned with `σ.log = L`. -/
theorem rev_readCb (γ : MvccName) (Q : MvccState → IProp GF) :
    iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }>) ⊢
      readCb (γ : StoreNames) (fun L => iprop(∃ σ : MvccState, Q σ ∗ ⌜σ.log = L⌝)) := by
  iintro Hau
  iunfold readCb
  iintro %q %L %c HX
  ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤)
    (fun _ _ => CoPset.mem_full) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, Hσ, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  iunfold mvccState at Hσ
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach, #Hrcm⟩
  iunfold slotX at HX
  iunfold revMuAbs at HX
  icases HX with ⟨HXa, HXc⟩
  iunfold absPart at Ha HXa
  icombine Ha HXa gives %Hag
  have hlog : σ.log = L := (Prod.mk.inj Hag.2).1
  imod Hcommit $$ [Ha Hp Hcr Hnl] with HQ
  · iunfold mvccState
    iunfold mvccStateI
    iunfold absPart
    iframe Hrcm; iframe Ha Hp Hcr Hnl; ipureintro; exact Hreach
  imodintro
  isplitl [HXa HXc]
  · iunfold slotX; iunfold revMuAbs; iunfold absPart; iframe HXa HXc
  iexists σ; iframe HQ; ipureintro; exact hlog

end handle

end api
end mvcc
end EtcdGrove
end Perennial
