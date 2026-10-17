/-
Proof of `Spec/Cache__attachPrevKV.lean` (etcd-io/etcd#21600). Lean-first (no Rocq counterpart).

The loop builds a fresh slice `events` of the response's events: for a create event
(`isCreateEvent`) the delivered event itself, else a fresh `*mvccpb.Event` with the delivered one's
`Type` and `Kv` and, once the store has reached `ModRevision - 1` (`store.waitForRev`), the
store's key-value of the key at that revision as `PrevKv` (`store.Get`). The loop invariant
keeps, for the events done, `eventAt` (the new event has the delivered one's fields) and
`prevKvOk`.

Unfinished (`sorry`): the error paths after the store lookup, which need the `errors.Is`
of the store's error against `rpctypes.ErrCompacted` (`errors_Is_snapErr`) and `fmt.Errorf`'s
arguments (`prevKV_errorf_argsOk`: a `[]byte` key, which `fmt.argOk` does not cover, and the
store's error, whose `Error()` is not known for `ErrNotReady` and the invalid-revision error).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__attachPrevKV
public import Spec.go_etcd_io.etcd.cache.v3.isCreateEvent
public import Spec.go_etcd_io.etcd.cache.v3.store__waitForRev
public import Spec.go_etcd_io.etcd.cache.v3.store__Get
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **Unfinished** (`sorry`): `errors.Is(err, rpctypes.ErrCompacted)` for the error `store.Get`
returned (`snapErr res err`: `nil`, the values of `ErrNotReady`, `ErrFutureRev`, `ErrCompacted`,
or `fmt.Errorf`'s invalid-revision error) returns. Go's `errors.Is` compares `err == target` (the
target, an `rpctypes.EtcdError` struct value, is comparable) and calls `err`'s `Is`/`Unwrap`
methods, none of which these errors have. Not provable from the current vocabulary: Perennial's
`errors.wp_Is` needs a pointer target, the trust boundary's `errors.IsStatusErr`
(`Spec/errors/IsStatusErr.lean`) needs `statusErrOk err` and an `EtcdError`-typed target, and the
package facts (`rpctypesInit`, `cacheInit`) give neither the type of `ErrCompacted`'s value nor the
method sets of `ErrNotReady`'s and the invalid-revision error. -/
theorem errors_Is_snapErr (res : SnapResult) (err target : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ snapErr (GF := GF) res err ∗
        globalAddr v3rpc.rpctypes.ErrCompacted ↦□ target }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b; True }} := by
  sorry

set_option hygiene false in
/-- The end of an iteration for a non-create event, once the switch has set the fresh event's
`PrevKv` to some `p` with `HpOk` (`nil`, or certified): `events[i] = clone`, and the loop
invariant at `n + 1`. -/
local macro "prevkv_tail" : tactic => `(tactic| (
  ihave Hrd : cacheReader cf $$ [Hrd]
  · iunfold cacheReader; iexact Hrd
  iStructNamed «$r0»
  ipersist Type'
  ipersist Kv
  ipersist PrevKv
  (try wp_auto)
  rw [ite_eq_left Hbnd2]
  wp_apply wp_store_slice_index esl (sint.Z n) zs «$r0_ptr» $$ [Hesl] as Hesl
  · iframe Hesl; ipureintro; rw [Hn.2.2]; word
  (try wp_auto)
  wp_for_post
  iframe
  iexists n + W64 1, l, n, zs.set (sint.nat n) «$r0_ptr»
  simp only [named]
  iframe
  isplitr
  · ipureintro; refine ⟨by word, by word, by simp [Hn.2.2]⟩
  imodintro
  iintro %j %z %e' %Hj %Hz %He'
  rw [hn1] at Hj
  by_cases hjn : j = sint.nat n
  · subst hjn
    rw [List.getElem?_set] at Hz
    simp only [↓reduceIte, show sint.nat n < zs.length by omega] at Hz
    cases Hz
    rw [He] at He'; cases He'
    isplitr
    · unfold eventAt
      iexists keySl
      iframe Type' Kv Hkey Hks Hmod
    unfold prevKvOk
    iright
    iexists _
    iframe PrevKv
    first | iexact HpOk | (ileft; itrivial) | (ileft; ipureintro; rfl) | (iright; iexact HpOk)
  · rw [List.getElem?_set, ite_eq_right (Ne.symm hjn)] at Hz
    iapply Hdone $$ %j %z %e' %(by omega) %Hz %He'))

set_option hygiene false in
/-- The store lookup failed (`gerr = ge`, the store's error for a result other than a snapshot):
`errors.Is(err, ErrCompacted)` (`errors_Is_snapErr`); if it holds, `PrevKv` stays `nil`
(`prevkv_tail`), else `fmt.Errorf` wraps the error and it is returned. -/
local macro "prevkv_err" : tactic => `(tactic| (
  icases Hres with %Hres
  obtain ⟨ge, rfl⟩ := Hgok
  (try wp_auto)
  wp_apply errors_Is_snapErr _ (GoInterface.ok ge) (GoInterface.ok eC) $$ [] as %b -
  · isplit
    · iexact Herr
    · iexact HeC
  cases b
  · -- not a compaction: `return fmt.Errorf("... %q ... %d: %w", key, prevRev, err)`
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf $$ [Hsl] as %er ⟨-, #HeS⟩
    · iframe Hsl
      -- **Unfinished** (`sorry`): `fmt.argsOk` of `[ev.Kv.Key, prevRev, err]`. `fmt.argOk`
      -- has no case for a `[]byte` argument (which `fmt` reads: `%q`), and the store's error's
      -- `Error()` is known only for `ErrFutureRev` and `ErrCompacted` (`rpctypesInit`), not for
      -- `ErrNotReady` (`cacheInit`) nor the invalid-revision error (`snapErr .invalid`).
      sorry
    wp_for_post
    iapply HΦ
    isplitl [Hrd]
    · iunfold cacheReader; iexact Hrd
    iexists resp
    iframe Hrp
    iright
    iexists er
    isplitr
    · ipureintro; rfl
    rw [show errorStringSpec er = EtcdGrove.fmt.stringMethodSpec er go!"Error" from rfl]
    iexact HeS
  · -- `errors.Is(err, rpctypes.ErrCompacted)`: `PrevKv` stays `nil`
    (try wp_auto)
    prevkv_tail))

set_option hygiene false in
/-- The end of the loop: `resp.Events = events`, and `nil` with the new response's `respAt` and
`respPrevKvs` from the loop invariant. -/
local macro "prevkv_exit" : tactic => `(tactic| (
  have hnE : sint.nat n = ls.length := by rw [Hsll.1]; word
  (try wp_auto)
  iapply HΦ
  iframe Hrd
  iexists _
  iframe Hrp
  ileft
  isplitr
  · ipureintro; rfl
  isplitl
  · unfold respAt eventsAt
    isplitl
    · iexists zs
      iframe Hesl
      isplitr
      · ipureintro; rw [Hn.2.2, Hlen]
      imodintro
      iintro %i %ev %e %Hi %He
      have hi : i < sint.nat n := by
        rw [hnE, ← Hn.2.2]; exact (List.getElem?_eq_some_iff.1 Hi).1
      ihave ⟨#H1, -⟩ := Hdone $$ %i %ev %e %hi %Hi %He
      iexact H1
    iframe Hhdr
    ipureintro; exact Hrf
  unfold respPrevKvs
  iexists zs
  iframe Hesl
  isplitr
  · ipureintro; rw [Hn.2.2, Hlen]
  imodintro
  iintro %i %ev %e %Hi %He
  have hi : i < sint.nat n := by
    rw [hnE, ← Hn.2.2]; exact (List.getElem?_eq_some_iff.1 Hi).1
  ihave ⟨-, #H2⟩ := Hdone $$ %i %ev %e %hi %Hi %He
  iexact H2))

theorem Cache.attachPrevKV.wp_proof
    (wp_isCreateEvent : isCreateEvent.spec (GF := GF) (hG := hG))
    (wp_waitForRev : store.waitForRev.spec (GF := GF) (hG := hG))
    (wp_Get : store.Get.spec (GF := GF) (hG := hG))
    (wp_Errorf : EtcdGrove.fmt.Errorf.spec (GF := GF) (hG := hG)) :
    Cache.attachPrevKV.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap ctx s rp resp r
  wp_start as ⟨#Hc, #Hctx, Hrd, Hrp, #Hr, #Hcr⟩
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  ihave #Hr' := Hr
  iunfold respAt at Hr'
  icases Hr' with ⟨#Hevs, #Hhdr, %Hrf⟩
  iunfold eventsAt at Hevs
  icases Hevs with ⟨%ls, #Hls, %Hlen, #Hall⟩
  ihave %Hsll := ownSlice_len $$ Hls
  wp_auto
  wp_if_destruct
  · -- no events: nothing to attach
    have h0 : resp.Events'.len = W64 0 := by
      first
      | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      | simpa using Hif
      | exact Hif
    have hl0 : ls = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hsll.1, h0]; rfl
    have he0 : r.events = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← Hlen, hl0]; rfl
    iapply HΦ
    iframe Hrd
    iexists resp
    iframe Hrp
    ileft
    isplitr
    · ipureintro; rfl
    iframe Hr
    unfold respPrevKvs
    iexists ls
    iframe Hls
    isplitr
    · ipureintro; exact Hlen
    imodintro
    iintro %i %ev %e %_ %He
    rw [he0] at He
    simp at He
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Loc) resp.Events'.len) as %esl ⟨Hesl, Hecap⟩
  · ipureintro; exact Hsll.2
  (try wp_auto)
  iunfold eventsCreateRevAt at Hcr
  icases Hcr with ⟨%ls', #Hls', %Hlen', #Hcrall⟩
  -- `slice.forRange`'s own counter is `i_ptr`; the Go variable `i` is `igp`
  rename_i igp
  irename : (igp ↦ zero_val w64 : IProp GF) => gi
  ihave HI : iprop(∃ (n : w64) (e0 : Loc) (ig : w64) (zs : List Loc),
      "j" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗ "gi" ∷ igp ↦ ig ∗ "Hesl" ∷ esl ↦* zs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int) ∧ zs.length = ls.length⌝ ∗
      "#Hdone" ∷ □ (∀ (j : Nat) (z : Loc) (e : EvModel), ⌜j < sint.nat n⌝ -∗ ⌜zs[j]? = some z⌝ -∗
        ⌜r.events[j]? = some e⌝ -∗ eventAt z e ∗ prevKvOk cf.pfx z e) ∗
      "Hrd" ∷ cacheReader cf) $$ [i ev gi Hesl Hrd]
  · iexists W64 0, _, _, _
    simp only [named]
    iframe
    isplitr
    · ipureintro
      refine ⟨by word, by word, ?_⟩
      simp [Hsll.1]
    imodintro
    iintro %j %z %e %Hj
    exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
  wp_for HI
  by_cases hlt : sint.Z n < sint.Z resp.Events'.len
  rotate_left
  · -- the loop is done: `resp.Events = events`, `nil`
    rw [decide_eq_false hlt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    imod ownSlice_persist $$ Hesl with #Hesl
    prevkv_exit
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; word
  · have Hlt : sint.nat n < ls.length := by word
    obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨e, He⟩ : ∃ e, r.events[sint.nat n]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    obtain ⟨l', Hl'⟩ : ∃ l', ls'[sint.nat n]? = some l' :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hlen', ← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z resp.Events'.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z n) l resp.Events' DFrac.discard ls Hn.1 Hl $$ Hls
      with ⟨#Hle, -⟩
    ihave #Hel := Hall $$ %(sint.nat n) %l %e %Hl %He
    ihave ⟨%cr, #Hcre⟩ := Hcrall $$ %(sint.nat n) %l' %e %Hl' %He
    (try wp_auto)
    wp_apply wp_isCreateEvent l e cr $$ [$Hpkg $Hel $Hcre]
    ihave %Hel' := ownSlice_len _ _ _ $$ Hesl
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z esl.len := ⟨Hn.1, by word⟩
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    cases hcm : isCreateModel e cr with
    | true =>
      -- a create event: the delivered event itself
      (try wp_auto)
      rw [ite_eq_left Hbnd2]
      wp_apply wp_store_slice_index esl (sint.Z n) zs l $$ [Hesl] as Hesl
      · iframe Hesl; ipureintro; rw [Hn.2.2]; word
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, l, n, zs.set (sint.nat n) l
      simp only [named]
      iframe
      isplitr
      · ipureintro; refine ⟨by word, by word, by simp [Hn.2.2]⟩
      imodintro
      iintro %j %z %e' %Hj %Hz %He'
      rw [hn1] at Hj
      by_cases hjn : j = sint.nat n
      · subst hjn
        rw [List.getElem?_set] at Hz
        simp only [↓reduceIte, show sint.nat n < zs.length by omega] at Hz
        cases Hz
        rw [He] at He'; cases He'
        iframe Hel
        unfold prevKvOk
        ileft
        iexists cr
        iframe Hcre
        ipureintro; exact hcm
      · rw [List.getElem?_set, ite_eq_right (Ne.symm hjn)] at Hz
        iapply Hdone $$ %j %z %e' %(by omega) %Hz %He'
    | false =>
      -- `clone := &mvccpb.Event{Type: ev.Type, Kv: ev.Kv}`, `prevRev := ev.Kv.ModRevision - 1`
      ihave #Hel2 := Hel
      iunfold eventAt at Hel2
      icases Hel2 with ⟨%keySl, #Htyp, #Hkv, #Hkey, #Hks, #Hmod⟩
      (try wp_auto)
      -- `c.store.waitForRev(ctx, prevRev)`
      iunfold cacheReader at Hrd
      wp_apply wp_waitForRev cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf) ctx s
        (e.rev - W64 1) $$ [$Hpkg $HisStore $Hrd $Hctx] as %werr ⟨Hrd, Hwr⟩
      icases Hwr with (⟨%Hwn, #Hlb⟩ | ⟨%Hwn, #HPD, #Hcl, #HerrS⟩)
      rotate_left
      · -- the context is done: its error
        obtain ⟨we, rfl⟩ : ∃ we, werr = GoInterface.ok we := by
          cases werr with
          | nil => exact absurd rfl Hwn
          | ok we => exact ⟨we, rfl⟩
        (try wp_auto)
        wp_for_post
        iapply HΦ
        isplitl [Hrd]
        · iunfold cacheReader; iexact Hrd
        iexists resp
        iframe Hrp
        iright
        iexists we
        isplitr
        · ipureintro; rfl
        iunfold context.errStringOk at HerrS
        rw [show errorStringSpec we = EtcdGrove.fmt.stringMethodSpec we go!"Error" from rfl]
        iapply HerrS
        ipureintro; rfl
      subst Hwn
      (try wp_auto)
      -- `kvs, _, err := c.store.Get(ev.Kv.Key, nil, prevRev)`
      wp_apply wp_Get cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf) (e.rev - W64 1) keySl
        slice.nil e.key [] DFrac.discard DFrac.discard (e.rev - W64 1)
        $$ [$Hpkg $HisStore $Hrd $Hlb $Hks] as %kvs %lrev %gerr ⟨Hrd, -, -, %st, #Hseen, #-, #Herr, Hres⟩
      · iapply ownSlice_nil
      iunfold storeSeen at Hseen
      icases Hseen with ⟨%Hst, #Hlbst⟩
      ihave #Hepkg : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
      · iPkgInit
      ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
      · iPkgInit
      ihave Hri : (rpctypesInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hrpc
      icases Hri with ⟨⟨%eFR, #HeFR⟩, ⟨%eC, #HeC, #HeCS⟩, -⟩
      ihave Hci : (cacheInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hci with ⟨⟨%eNR, #HeNR⟩, -⟩
      generalize Hm : snapModel st (e.rev - W64 1) = res
      cases res with
      | ok r' m =>
        ihave %Hgn : ⌜gerr = GoInterface.nil⌝ $$ []
        · iunfold snapErr at Herr; iexact Herr
        subst Hgn
        icases Hres with ⟨%Hlrev, #HE, Hkvs, Hcap, #HkvsAt⟩
        ihave %Hkl := ownSlice_len _ _ _ $$ Hkvs
        have hsnap := snapModel_ok_spec Hst.1 Hm
        cases hkr : kvRange e.key [] m with
        | nil =>
          try rw [hkr] at Hkl
          simp only [List.map_nil, List.length_nil] at Hkl
          (try wp_auto)
          rw [show (decide (sint.Z kvs.len > sint.Z (W64 0))) = false by
            apply decide_eq_false; have := Hkl.1; word]
          (try wp_auto)
          wp_apply errors_Is_snapErr (.ok r' m) GoInterface.nil (GoInterface.ok eC) $$ [] as %b -
          · isplit
            · iexact Herr
            · iexact HeC
          cases b
          · (try wp_auto)
            prevkv_tail
          · (try wp_auto)
            prevkv_tail
        | cons x xs =>
          try rw [hkr] at Hkl
          simp only [List.map_cons, List.length_cons] at Hkl
          (try wp_auto)
          have hpos : sint.Z (W64 0) < sint.Z kvs.len := by have := Hkl.1; word
          simp only [hpos, _root_.decide_true]
          (try wp_auto)
          rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z kvs.len by
            have := Hkl.1; constructor <;> word)]
          wp_apply wp_load_slice_index kvs (sint.Z (W64 0)) _ (DFrac.own 1) x.2 (by word) $$ [Hkvs]
            as Hkvs
          · iframe Hkvs; ipureintro; rfl
          (try wp_auto)
          have hx : x ∈ kvRange e.key [] m := by rw [hkr]; exact List.mem_cons_self
          simp only [kvRange, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at hx
          ihave #HpOk : iprop(∃ (r : w64) (m : KvMap), □ isEtcdKvs r cf.pfx m ∗
              ⌜(e.key, x.2) ∈ m ∧
                (e.rev - W64 1 = W64 0 ∨ sint.Z r ≤ sint.Z (e.rev - W64 1))⌝) $$ []
          · iexists r', m
            isplitr
            · imodintro; iunfold etcdCert at HE; iexact HE
            ipureintro
            refine ⟨by rw [← hx.2]; exact hx.1, ?_⟩
            by_cases h0 : e.rev - W64 1 = W64 0
            · exact Or.inl h0
            · right; have := hsnap.2.2.1; rw [ite_eq_right h0] at this; exact this
          prevkv_tail
      | notReady =>
        ihave %Hgok : ⌜∃ ge, gerr = GoInterface.ok ge⌝ $$ []
        · iunfold snapErr at Herr; icombine Herr HeNR gives %Heq; ipureintro; exact ⟨_, Heq⟩
        prevkv_err
      | invalid =>
        ihave %Hgok : ⌜∃ ge, gerr = GoInterface.ok ge⌝ $$ []
        · iunfold snapErr at Herr; iexact Herr
        prevkv_err
      | future =>
        ihave %Hgok : ⌜∃ ge, gerr = GoInterface.ok ge⌝ $$ []
        · iunfold snapErr at Herr; icombine Herr HeFR gives %Heq; ipureintro; exact ⟨_, Heq⟩
        prevkv_err
      | compacted =>
        ihave %Hgok : ⌜∃ ge, gerr = GoInterface.ok ge⌝ $$ []
        · iunfold snapErr at Herr; icombine Herr HeC gives %Heq; ipureintro; exact ⟨_, Heq⟩
        prevkv_err

end proof

end EtcdGrove
end Perennial
