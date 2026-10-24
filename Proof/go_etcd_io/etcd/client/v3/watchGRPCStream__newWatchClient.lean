/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__newWatchClient.lean` (the watch slice's
unit W-C): `newWatchClient` at its first call. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__waitCancelSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__openWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveWatchClient
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveSubstream
public import Proof.go_etcd_io.etcd.client.v3.WatchRecon
public import Proof.go_etcd_io.etcd.client.v3.InvWcJoin

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxHeartbeats 0 in
theorem watchGRPCStream.newWatchClient.wp_proof
    (wp_join : watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG))
    (wp_wait : watchGRPCStream.waitCancelSubstreams.spec (GF := GF) (hG := hG))
    (wp_open : watchGRPCStream.openWatchClient.spec (GF := GF) (hG := hG))
    (wp_serve : watchGRPCStream.serveWatchClient.spec (GF := GF) (hG := hG))
    (wp_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_serveSub : watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.newWatchClient.spec (GF := GF) (hG := hG) := by
  intro V G callSl m0 s0 rc γrc n sent eps γs S U
  wp_start as ⟨#HG, Hsub, Hm0, Hres, Hs0, Hrc, Hrcb, Hgen, Hprod, Hep, %HgOk, Hwsa, Hels, Had, Htt⟩
  ihave #HG' := HG
  iunfold isWGS at HG'
  icases HG' with ⟨%Hwgsnn, ⟨%vs, #Hvs, #Hcoo⟩, #Hsf, %Hlg, #Fowner, #Fremote, #Fcall, #Fctx, #Fckey,
    #Fcancel, #Freqc, #Frespc, #Fdonec, #Ferrc, #Fclosingc, #Flg, #Hctx, #Hcancel, #Hreq, #Herr,
    #Hclosing, #Hdone, #Hrespsc⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  -- (D25) the generation `n` ends
  imod mono_nat_own_update (n + 1) (Nat.le_succ _) $$ Hgen with ⟨Hgen, #Hglb⟩
  wp_apply wp_broadcast_chan_close rc γrc (monoNatLbOwn G.γend (n + 1)) $$ [$Hrcb] as -
  · imodintro; iexact Hglb
  wp_apply chan.wp_make1 (V := Unit) as %rc' %γrc' ⟨#Hrc'c, %-, Hrc'o⟩
  imod alloc_broadcast_chan (E := ⊤) (monoNatLbOwn G.γend (n + 2)) γrc' rc' $$ Hrc'c Hrc'o
    with Hrc'b
  icases ownBroadcastChan_dup_unknown _ _ _ _ $$ Hrc'b with ⟨Hrc'b, #Hrc'u⟩
  -- the substreams, each with its lifetime fixed
  icases client.wsElem_choose V G n γs S U $$ Hels with ⟨%f, Hels⟩
  rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]
  icases Hels with ⟨⟨HCs, Hids⟩, Hdcs⟩
  iunfold sliceOwn at Hs0
  icases Hs0 with ⟨Hs0, Hs0c⟩
  wp_apply wp_join G.wgs m0 S.M s0 S.l (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) U
    (fun ws => lifeDn V G (f ws).1 (f ws).2.2) $$ [$Hsub $Hm0 $Hres $Hs0 $Hdcs]
    as ⟨Hsub, Hm0, Hres, Hs0, Hdcs, #HjM, #Hjl⟩
  · ipureintro
    exact ⟨fun X ws h => HgOk.1 X ws h, fun ws h hn => HgOk.2.2.1 ws h hn⟩
  -- `substreams`' loop: ids reset, the substreams queued
  have Hinj : ∀ X Y ws, S.M !! X = some ws → S.M !! Y = some ws → X = Y := HgOk.2.1
  icases client.wsElemCs_pure V G n γs S U f $$ HCs with ⟨HCs, %Hfph⟩
  have HregM : ∀ X ws, S.M !! X = some ws → (f ws).2.1 = .reg X := by
    intro X ws hX
    obtain ⟨-, hph⟩ := Hfph ws (HgOk.1 X ws hX)
    revert hph
    cases (f ws).2.1 with
    | reg Y => intro hph; rw [Hinj Y X ws hph.1 hX]
    | queued si => intro hph; exact absurd hX (hph.1 X)
    | closedRun Y => intro hph; exact absurd hX (hph.1.2.1 X)
    | orphan => intro hph; exact absurd hX (hph.1 X)
    | closed => intro hph; exact absurd hX (hph.1 X)
  ihave Hids : iprop([∗map] ws ↦ _u ∈ U, ∃ v : w64, wsF ws go!"id" ↦ v ∗
      ⌜v = W64 (-1) ∨ ∃ X, X ∉ ([] : List w64) ∧ S.M !! X = some ws⌝) $$ [Hids]
  · iapply (BigSepM.bigSepM_mono (fun {ws _} hws => by
      iintro Hid
      iexists _
      iframe Hid
      ipureintro
      obtain ⟨-, hph⟩ := Hfph ws hws
      revert hph
      cases (f ws).2.1 with
      | reg Y => intro hph; right; exact ⟨Y, by simp, hph.1⟩
      | _ => intro _; left; rfl)) $$ Hids
  ipersist w
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (s1 : GoSlice) (wv : Loc),
      wgsF G.wgs go!"resuming" ↦ s1 ∗ s1 ↦* (S.l ++ (keys.take i.toNat).filterMap (S.M !! ·)) ∗
      ownSliceCap Loc s1 (DFrac.own 1) ∗ ws_ptr ↦ wv ∗ ⌜0 ≤ i⌝ ∗
      ([∗map] ws ↦ _u ∈ U, ∃ v : w64, wsF ws go!"id" ↦ v ∗
        ⌜v = W64 (-1) ∨ ∃ X, X ∉ keys.take i.toNat ∧ S.M !! X = some ws⌝))) $$ Hm0
  iintro %keys ⟨%Hk1, %Hk2, %Hk3⟩
  isplitl [Hres Hs0 Hs0c ws Hids]
  · iexists s0, _
    simp only [Int.toNat_zero, List.take_zero, List.filterMap_nil, List.append_nil]
    iframe
    ipureintro; exact Int.le_refl 0
  isplitr
  · imodintro
    iintro %ik %X %wsv ⟨%HkX, %HMX⟩ ⟨%s1, %wv, Hres, Hs1, Hs1c, Hwsp, %Hik, Hids⟩
    wp_auto
    have hU : U !! wsv = some () := HgOk.1 X wsv HMX
    icases (BigSepM.bigSepM_delete hU).1 $$ Hids with ⟨⟨%v0, Hid, -⟩, Hids⟩
    wp_auto
    wp_apply wp_slice_literal (V := Loc) [wsv]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [Hs1 Hs1c Hsl1] as %s' ⟨Hs1, Hs1c, -⟩
    · iframe
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    have htake : keys.take (ik + 1).toNat = keys.take ik.toNat ++ [X] := by
      rw [show (ik + 1).toNat = ik.toNat + 1 by omega, List.take_add_one, HkX]; rfl
    iexists s', wsv
    rw [htake, List.filterMap_append]
    simp only [List.filterMap_cons, List.filterMap_nil, HMX, List.append_assoc]
    iframe
    isplitr
    · ipureintro; omega
    iapply (BigSepM.bigSepM_delete hU).2
    isplitl [Hid]
    · iexists _; iframe Hid; ipureintro; left; rfl
    iapply (BigSepM.bigSepM_mono (fun {k _} hk => by
      iintro ⟨%v, Hid, %Hv⟩
      iexists v
      iframe Hid
      ipureintro
      rcases Hv with h | ⟨Y, hY, hMY⟩
      · left; exact h
      · right
        refine ⟨Y, ?_, hMY⟩
        intro hm
        rcases List.mem_append.1 hm with h' | h'
        · exact hY h'
        · simp at h'; subst h'
          rw [HMX] at hMY; cases hMY
          change (GMap.delete wsv U) !! wsv = _ at hk
          rw [GMap.lookup_delete] at hk; cases hk)) $$ Hids
  iintro ⟨%s1, %wv, Hres, Hs1, Hs1c, Hwsp, -, Hids⟩ Hm0
  -- every id is reset
  have Hkall : keys.take (GMap.size S.M : Int).toNat = keys := by
    rw [Int.toNat_natCast, ← Hk2, List.take_length]
  rw [Hkall] at *
  ihave Hids : iprop([∗map] ws ↦ _u ∈ U, wsF ws go!"id" ↦ W64 (-1)) $$ [Hids]
  · iapply (BigSepM.bigSepM_mono (fun {ws _} _ => by
      iintro ⟨%v, Hid, %Hv⟩
      rcases Hv with rfl | ⟨Y, hY, hMY⟩
      · iexact Hid
      · exfalso; exact hY ((Hk1 Y).2 (by simp [hMY])))) $$ Hids
  -- the substreams to queue: `resuming`'s and `substreams`', the nils dropped
  have Hdisj : ∀ X ws, S.M !! X = some ws → ws ∉ S.l := by
    intro X ws hX
    have h := (Hfph ws (HgOk.1 X ws hX)).2
    rw [HregM X ws hX] at h
    exact h.2.1
  obtain ⟨Hmv, Hmvn, Hlnd, HlU⟩ := client.mv_facts S U keys HgOk Hk1 Hk3 Hdisj
  ihave %Hs1len := ownSlice_len $$ Hs1
  wp_auto
  -- the nils dropped, and what each substream's goroutine left taken
  ihave #Hjl' : iprop(□ ∀ ws : Loc, ⌜ws ∈ S.l ++ keys.filterMap (S.M !! ·) ∧ ws ≠ null⌝ →
      □ lifeQ V G (f ws).1 (f ws).2.2) $$ []
  · imodintro
    iintro %ws ⟨%Hm, %Hn⟩
    rcases List.mem_append.1 Hm with h | h
    · iapply Hjl; ipureintro; exact ⟨h, Hn⟩
    · obtain ⟨X, hX⟩ := (Hmv ws).1 h
      iapply HjM; ipureintro; exact hX
  ihave HI : iprop(∃ (k : w64) (wv : Loc) (r : GoSlice), "i" ∷ i_ptr ↦ k ∗ "ws" ∷ ws_ptr ↦ wv ∗
      "res" ∷ resuming_ptr ↦ r ∗
      "Hr" ∷ r ↦* ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k)).filter
        (fun x => decide (x ≠ null)) ∗
      "Hrcap" ∷ ownSliceCap Loc r (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((S.l ++ keys.filterMap (S.M !! ·)).length : Int)⌝ ∗
      "HT" ∷ ([∗list] ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k)).filter
        (fun x => decide (x ≠ null)), wsElemT V G γs S ws (f ws)) ∗
      "HCs" ∷ ([∗map] ws ↦ _u ∈ U, ⌜ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k)).filter
        (fun x => decide (x ≠ null))⌝ ∨ wsElemC V G n γs S ws (f ws))) $$ [i ws resuming HCs]
  · iexists W64 0, _, slice.nil
    simp only [named]
    have h0 : sint.nat (W64 0) = 0 := by word
    rw [h0]
    simp only [List.take_zero, List.filter_nil]
    iframe i ws resuming
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply (ownSliceCap_nil (V := Loc))
    isplitr
    · ipureintro; constructor <;> word
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by iintro H; iright; iexact H)) $$ HCs
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z s1.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat k < (S.l ++ keys.filterMap (S.M !! ·)).length := by
      have := Hs1len.1; word
    obtain ⟨x, Hx⟩ : ∃ x, (S.l ++ keys.filterMap (S.M !! ·))[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s1.len := ⟨Hk.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply +noauto wp_load_slice_index s1 (sint.Z k) _ (DFrac.own 1) x Hk.1 $$ [Hs1] as Hs1
    · iframe; ipureintro; rw [← Hx]
    wp_auto_lc 1
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have htake : (S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k + 1) =
        (S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k) ++ [x] := by
      rw [List.take_add_one, Hx]; rfl
    have hxmem : x ∈ S.l ++ keys.filterMap (S.M !! ·) := List.mem_of_getElem? Hx
    wp_if_destruct
    · -- a nil: skipped
      have hfilt : ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k + 1)).filter
          (fun x => decide (x ≠ null)) = ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k)).filter
          (fun x => decide (x ≠ null)) := by
        rw [htake, List.filter_append]; simp
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1, _, r
      simp only [named]
      rw [hk1, hfilt]
      iframe
      ipureintro; constructor <;> word
    · -- a substream: queued, what its goroutine left taken
      have hxn : x ≠ null := ‹¬x = null›
      have hfilt : ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k + 1)).filter
          (fun x => decide (x ≠ null)) = ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k)).filter
          (fun x => decide (x ≠ null)) ++ [x] := by
        rw [htake, List.filter_append]; simp [hxn]
      have hnotin : x ∉ ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k)).filter
          (fun x => decide (x ≠ null)) := by
        have hsub := ((List.take_sublist (sint.nat k + 1) (S.l ++ keys.filterMap (S.M !! ·))).filter
          (fun x => decide (x ≠ null)))
        have hnd := Hlnd.sublist hsub
        rw [hfilt] at hnd
        intro hm
        exact (List.nodup_append.1 hnd).2.2 x hm x (List.mem_singleton_self _) rfl
      have hxU : U !! x = some () := HlU x (List.mem_filter.2 ⟨hxmem, by simpa using hxn⟩)
      icases (BigSepM.bigSepM_delete hxU).1 $$ HCs with ⟨Hx0, HCs⟩
      icases Hx0 with (%Hc | HxC)
      · exact absurd Hc hnotin
      iunfold wsElemC at HxC
      icases HxC with ⟨%Hpx, #HPx, Hrestx, -, #Hlix, Htkx, -⟩
      ihave #HQx := Hjl' $$ %x %(And.intro hxmem hxn)
      imod client.take_dep V G (f x).1 (f x).2.2 $$ [Hlc1 Htkx] with Hdep
      · iframe; iframe #
      (try wp_auto)
      wp_apply wp_slice_literal (V := Loc) [x]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hr Hrcap Hsl1] as %r' ⟨Hr, Hrcap, -⟩
      · iframe
      (try wp_auto)
      ihave HT : iprop([∗list] ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).take (sint.nat k)).filter
          (fun x => decide (x ≠ null)) ++ [x], wsElemT V G γs S ws (f ws)) $$ [HT Hrestx Hdep]
      · iapply BigSepL.bigSepL_snoc.2
        iframe HT
        unfold wsElemT
        iframe Hrestx Hdep HPx Hlix
        ipureintro; exact Hpx
      ihave HCs : iprop([∗map] ws ↦ _u ∈ U, ⌜ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).take
          (sint.nat k)).filter (fun x => decide (x ≠ null)) ++ [x]⌝ ∨ wsElemC V G n γs S ws (f ws))
          $$ [HCs]
      · iapply (BigSepM.bigSepM_delete hxU).2
        isplitr
        · ileft; ipureintro; simp
        iapply (BigSepM.bigSepM_mono (fun {_ _} _ => by
          iintro (%Hc | H)
          · ileft; ipureintro; exact List.mem_append.2 (Or.inl Hc)
          · iright; iexact H)) $$ HCs
      wp_for_post
      iframe
      iexists k + W64 1, x, r'
      simp only [named]
      rw [hk1, hfilt]
      iframe
      ipureintro; constructor <;> word
  -- `resuming`: the queued substreams `l'`; `substreams`: empty
  have hkl : sint.nat k = (S.l ++ keys.filterMap (S.M !! ·)).length := by
    have : ¬ sint.Z k < sint.Z s1.len := Hif
    have := Hs1len.1; word
  rw [hkl, List.take_length]
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.int64
    (go.GoType.PointerType go_etcd_io.etcd.client.v3.watcherStream.ty)) as %m' Hm'
  wp_apply chan.wp_make1 (V := Unit) as %stopc %γst ⟨#Hstc, %-, Hsto⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γst stopc $$ Hstc Hsto with Hstb
  icases ownBroadcastChan_dup_unknown _ _ _ _ $$ Hstb with ⟨Hstb, #Hstu⟩
  -- (D25) the stream's wait group shared with `waitCancelSubstreams`' goroutines
  iunfold wgAdder at Had
  imod wgsWg_share (wgsF G.wgs go!"wg") $$ Had with ⟨%γS, %γh, Hsh⟩
  -- what each substream's goroutine left, lent
  ihave ⟨HTr, HTw⟩ : iprop(([∗list] ws ∈ (S.l ++ keys.filterMap (S.M !! ·)).filter
        (fun x => decide (x ≠ null)), ⌜(f ws).1.ws = ws ∧ phOk S ws (f ws).2.1⌝ ∗ wsIs V (f ws).1 ∗
        wsRest V γs S.Dm (f ws).1 (f ws).2.1 ∗ lifeInvIs V G (f ws).1 (f ws).2.2) ∗
      ([∗list] ws ∈ (S.l ++ keys.filterMap (S.M !! ·)).filter
        (fun x => decide (x ≠ null)), wcIn V G (f ws).1)) $$ [HT]
  · iapply BigSepL.bigSepL_sep_eqv.1
    iapply (BigSepL.bigSepL_mono (fun {_ _} _ => by
      unfold wsElemT wcIn
      iintro ⟨%Hp, #HP, Hrest, #Hli, Hdep⟩
      iframe Hrest Hdep HP Hli
      ipureintro; exact Hp)) $$ HT
  wp_apply wp_wait V G callSl r _ (DFrac.own 1) (fun ws => (f ws).1) stopc γst γS γh 0
    $$ [$Hres $Hr $Hstu $Hsh $Htt $HTw] as %donec ⟨Hres, Hr, Htt, Hsh, %γd, %Qd, #Hdcb, Hget⟩
  · iframe #
    ipureintro
    intro ws hws
    exact (Hfph ws (HlU ws hws)).1
  simp only [ne_eq, decide_not] at *
  wp_apply wp_open V G.wgs G.ctx G.cd callSl vs $$ [] as %wc %err Hopen
  · iframe #
  wp_apply wp_broadcast_chan_close stopc γst iprop(True) $$ [$Hstb] as -
  · imodintro; itrivial
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdcb
  wp_bind (App (Val (chan.receive _)) (Val #donec))
  wp_apply_core chan.wp_receive (V := Unit) donec γd $$ Hdcc
  iintro -
  iapply broadcast_chan_receive donec γd Qd _ .Unknown $$ Hdcb
  iintro ⟨#HQd, -⟩
  wp_auto_lc 1
  imod Hget $$ Hlc1 HQd with Hout
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hout with ⟨Hout, Htoks⟩
  imod wgsWg_burn_list _ _ _ 0 _ $$ [Hsh Htoks] with Hsh
  · iframe
  imod wgsWg_unshare _ _ _ $$ Hsh with Had
  -- the model's reconnection
  obtain ⟨HgOk', Hrecon⟩ := client.reconnect_ok HgOk (keys.filterMap (S.M !! ·)) Hmv Hmvn Hdisj
  simp only [ne_eq, decide_not] at HgOk' Hrecon
  -- each queued substream's bundle: `run`'s state, what its goroutine gives back, its id, `donec`
  icases client.bigSepM_take_list _ U _ Hlnd HlU $$ Hids with ⟨Hidl, Hids⟩
  icases client.bigSepM_take_list _ U _ Hlnd HlU $$ Hdcs with ⟨Hdcl, Hdcs⟩
  ihave Hbun : iprop([∗list] ws ∈ (S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)),
      ((((⌜(f ws).1.ws = ws ∧ phOk S ws (f ws).2.1⌝ ∗ wsIs V (f ws).1 ∗
        wsRest V γs S.Dm (f ws).1 (f ws).2.1 ∗ lifeInvIs V G (f ws).1 (f ws).2.2) ∗
        wcOut V G (f ws).1) ∗ wsF ws go!"id" ↦ W64 (-1)) ∗
        donecAt ws (lifeDn V G (f ws).1 (f ws).2.2))) $$ [HTr Hout Hidl Hdcl]
  · iapply BigSepL.bigSepL_sep_eqv.2
    iframe Hdcl
    iapply BigSepL.bigSepL_sep_eqv.2
    iframe Hidl
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [HTr]
    · iexact HTr
    iexact Hout
  ihave %Hrlen := ownSlice_len $$ Hr
  (try wp_auto)
  -- the goroutines restarted: every substream not stopped, from its resume revision
  have Hphq : ∀ x ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))), (∃ X, (f x).2.1 = .reg X) ∨ (∃ si, (f x).2.1 = .queued si) := by
    intro x hx
    obtain ⟨hxm, hxn⟩ := List.mem_filter.1 hx
    rcases List.mem_append.1 hxm with h | h
    · right
      have hU : U !! x = some () := HgOk.2.2.1 x h (by simpa using hxn)
      have hph := (Hfph x hU).2
      revert hph
      cases (f x).2.1 with
      | queued si => intro _; exact ⟨si, rfl⟩
      | reg X => intro hph; exact absurd h hph.2.1
      | closedRun X => intro hph; exact absurd h hph.2.1
      | orphan => intro hph; exact absurd h hph.2.1
      | closed => intro hph; exact absurd h hph.2.1
    · left
      obtain ⟨X, hX⟩ := (Hmv x).1 h
      exact ⟨X, HregM X x hX⟩
  ihave HI3 : iprop(∃ (k : w64) (wv : Loc), "i" ∷ i_ptr ↦ k ∗ "ws" ∷ ws_ptr ↦ wv ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).length : Int)⌝ ∗
      "Hnew" ∷ ([∗list] ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).take (sint.nat k), wsElem V G (n + 1) γs (S.reconnect ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))) ws) ∗
      "Hbun" ∷ ([∗list] ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).drop (sint.nat k), ((((⌜(f ws).1.ws = ws ∧ phOk S ws (f ws).2.1⌝ ∗ wsIs V (f ws).1 ∗
        wsRest V γs S.Dm (f ws).1 (f ws).2.1 ∗ lifeInvIs V G (f ws).1 (f ws).2.2) ∗
        wcOut V G (f ws).1) ∗ wsF ws go!"id" ↦ W64 (-1)) ∗
        donecAt ws (lifeDn V G (f ws).1 (f ws).2.2))) ∗
      "Had" ∷ wgsWgAdder (wgsF G.wgs go!"wg") ∗ "Htt" ∷ threadTok) $$ [i ws Hbun Had Htt]
  · iexists W64 0, _
    simp only [named]
    have h0 : sint.nat (W64 0) = 0 := by word
    rw [h0]
    simp only [List.take_zero, List.drop_zero]
    iframe
    isplitr
    · ipureintro; constructor <;> word
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI3
  wp_if_destruct
  · have Hif' : sint.Z k < sint.Z r.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat k < ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).length := by
      have := Hrlen.1; word
    obtain ⟨x, Hx⟩ : ∃ x, ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z r.len := ⟨Hk.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply +noauto wp_load_slice_index r (sint.Z k) _ (DFrac.own 1) x Hk.1 $$ [Hr] as Hr
    · iframe; ipureintro; rw [← Hx]
    wp_auto_lc 1
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have htake : ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).take (sint.nat k + 1) = ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).take (sint.nat k) ++ [x] := by
      rw [List.take_add_one, Hx]; rfl
    have hdrop : ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).drop (sint.nat k) = x :: ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).drop (sint.nat k + 1) := by
      rw [List.drop_eq_getElem_cons Hlt, (List.getElem?_eq_some_iff.1 Hx).2]
    have hxmem : x ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))) := List.mem_of_getElem? Hx
    have hxU : U !! x = some () := HlU x (by simpa using hxmem)
    have hphx := Hphq x hxmem
    irevert Hbun
    rw [hdrop]
    iintro Hbun
    icases BigSepL.bigSepL_cons.1 $$ Hbun with ⟨⟨⟨⟨⟨%Hpx, #HPx, Hrestx, #Hlix⟩, Houtx⟩, Hidx⟩, Hdcx⟩, Hbun⟩
    have hrec : phOk (S.reconnect ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))) x (WPh.queued none) := by
      have := Hrecon x (f x).2.1 hxU Hpx.2
      rcases hphx with ⟨X, hX⟩ | ⟨si, hX⟩ <;> rw [hX] at this <;> simpa [WPh.recon] using this
    generalize hP : (f x).1 = P at *
    obtain ⟨hPx, -⟩ := Hpx
    subst hPx
    iunfold wcOut at Houtx
    icases Houtx with (Hrb | ⟨#Hstp, Hsb⟩)
    · -- resumed: queued from its resume revision, a new goroutine started
      iunfold resumeBody at Hrb
      icases Hrb with ⟨%k0, %rv0, %rcv, %nr, %bl, %dc, Hrun, #Hls, Hcl, Hbl, #Hblok, Houtf, Hdnf,
        Hgx, Hel⟩
      imod client.recon_alive V γs γs S.Dm [] P (f P.ws).2.1 hphx k0 rv0 rcv nr
        $$ [HPx Hlc1 Hrestx Hrun Hls Hgx] with ⟨%k', %rv', %rcv', Hq', Hrun', %Hlen', #Hls', Hgx⟩
      · iframe; iframe #
      wp_auto
      -- the new lifetime's `donec`
      wp_apply (chan.wp_make1 (V := Unit)) as %dnc %γdn ⟨#Hdnc, %-, Hdno⟩
      iunfold donecAt at Hdcx
      icases Hdcx with ⟨Hdcf, -⟩
      icases typedPointsto_half_combine _ _ _ 1 $$ [Hdnf Hdcf] with ⟨%Hdceq, Hdcf⟩
      · iframe
      wp_auto
      icases (typedPointsto_half_split _ _ 1).1 $$ Hdcf with ⟨Hdnf1, Hdnf2⟩
      imod dghostVar_alloc false with ⟨%γt, Hγt⟩
      icases dghostVar_halves _ _ $$ Hγt with ⟨Hγt1, Hγt2⟩
      imod dghostVar_alloc () with ⟨%γk, Htk⟩
      let L : LifePrm := ⟨dnc, γdn, γt, γk, n + 1⟩
      imod alloc_broadcast_chan (E := ⊤) (lifeQ V G P L) γdn dnc $$ Hdnc Hdno with Hdnb
      icases ownBroadcastChan_dup_unknown _ _ _ _ $$ Hdnb with ⟨Hdnb, #Hdnu⟩
      icases (ghostMapElem_halves G.γws P.ws ()).1 $$ Hel with ⟨Hel1, Hel2⟩
      imod inv_alloc lifeN ⊤ (lifeSt V G P L) $$ [Hγt2 Hel2] with #Hli
      · inext
        iunfold lifeSt
        ileft
        iframe
      wp_apply wp_wgsWg_Add $$ [Had Htt] as ⟨Had, Hwd⟩
      · iframe
      (try wp_auto)
      wp_apply wp_fork_tok_self $$ [Hcl Hbl Houtf Hdnf1 Hdnb Hγt1 Hrun' Hgx Hwd Hel1] as Htt
      · wp_apply wp_serveSub V G callSl P L k' rv' rcv' bl rc' γrc'
          $$ [Hcl Hbl Houtf Hdnf1 Hdnb Hγt1 Hrun' Hgx Hwd Hel1] as Htok
        · unfold wgDone
          iframe #
          iframe
          ipureintro; exact Hlen'
        first | iexact Htok | (iframe Htok; ipureintro; simp) | (iframe Htok; ipureintro; decide)
      wp_for_post
      iframe
      iexists k + W64 1, P.ws
      simp only [named]
      rw [hk1, htake]
      iframe
      isplitr
      · ipureintro; constructor <;> word
      iapply BigSepL.bigSepL_singleton.2
      unfold wsElem
      iexists P, .queued none
      isplitr
      · ipureintro; exact ⟨rfl, hrec⟩
      simp only [WPh.id, noCancelOk, WPh.isOrphan]
      iframe HPx Hidx
      have hDm : ∀ l, (S.reconnect l).Dm = [] := fun _ => rfl
      rw [hDm]
      isplitl [Hq']
      · iexact Hq'
      isplitr
      · itrivial
      iapply client.wsLife_fresh V G (n + 1) P L _ rfl
      unfold donecAt
      iframe Hdnf2 Hdnu Hli
      unfold ownTok; iexact Htk
    · -- stopped for good: queued, no goroutine
      ihave #Hstp' := Hstp
      iunfold wsStopped at Hstp'
      icases Hstp' with ⟨#Hgx, #Hclf⟩
      wp_auto
      ihave ⟨Hq', -, Hsb⟩ := client.recon_dead V γs γs S.Dm [] P (f P.ws).2.1 hphx $$ [Hrestx Hsb]
      · iframe Hrestx Hsb; iframe #
      wp_for_post
      iframe
      iexists k + W64 1, P.ws
      simp only [named]
      rw [hk1, htake]
      iframe
      isplitr
      · ipureintro; constructor <;> word
      iapply BigSepL.bigSepL_singleton.2
      unfold wsElem
      iexists P, .queued none
      isplitr
      · ipureintro; exact ⟨rfl, hrec⟩
      simp only [WPh.id, noCancelOk, WPh.isOrphan]
      iframe HPx Hidx
      have hDm : ∀ l, (S.reconnect l).Dm = [] := fun _ => rfl
      rw [hDm]
      isplitl [Hq']
      · iexact Hq'
      isplitr
      · itrivial
      unfold wsLife
      iexists (f P.ws).2.2
      iframe Hdcx Hlix
      isplitl [Hsb]
      · unfold lifeTk; iright; iframe Hsb Hstp
      iright; unfold genOk; iright; iexact Hgx
  -- the loop's end: every substream of the new generation
  have hkl : sint.nat k = ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))).length := by
    have : ¬ sint.Z k < sint.Z r.len := Hif
    have := Hrlen.1; word
  rw [hkl, List.take_length, List.drop_length]
  ihave Hoth : iprop([∗map] ws ↦ _u ∈ U, ⌜ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))⌝ ∨
      wsElem V G (n + 1) γs (S.reconnect ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))) ws) $$ [HCs Hids Hdcs]
  · ihave H3 : iprop([∗map] ws ↦ _u ∈ U, ((⌜ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))⌝ ∨ wsElemC V G n γs S ws (f ws)) ∗
        (⌜ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))⌝ ∨ wsF ws go!"id" ↦ W64 (-1))) ∗
        (⌜ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))⌝ ∨ donecAt ws (lifeDn V G (f ws).1 (f ws).2.2))) $$ [HCs Hids Hdcs]
    · rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]
      iframe
    iapply (BigSepM.bigSepM_mono (fun {ws _} hws => by
      iintro ⟨⟨HC, Hid⟩, Hdc⟩
      by_cases hnot : ws ∈ ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))
      · ileft; ipureintro; exact hnot
      icases HC with (%Hc | HC)
      · exact absurd Hc hnot
      icases Hid with (%Hc | Hid)
      · exact absurd Hc hnot
      icases Hdc with (%Hc | Hdc)
      · exact absurd Hc hnot
      iright
      have hwsn : ws ≠ null := fun e => by
        subst e
        have h0 : U !! null = none := HgOk.2.2.2.2.2.1
        have h1 : U !! null = some () := hws
        rw [h0] at h1; cases h1
      have hph := (Hfph ws hws).2
      have hoth : (∃ X, (f ws).2.1 = .closedRun X) ∨ (f ws).2.1 = .orphan ∨ (f ws).2.1 = .closed := by
        revert hph
        cases (f ws).2.1 with
        | queued si =>
          intro hph; exfalso; apply hnot
          refine List.mem_filter.2 ⟨List.mem_append.2 (Or.inl hph.2.1), ?_⟩
          simpa using hwsn
        | reg X =>
          intro hph; exfalso; apply hnot
          refine List.mem_filter.2 ⟨List.mem_append.2 (Or.inr ((Hmv ws).2 ⟨X, hph.1⟩)), ?_⟩
          simpa using hwsn
        | closedRun X => intro _; exact Or.inl ⟨X, rfl⟩
        | orphan => intro _; exact Or.inr (Or.inl rfl)
        | closed => intro _; exact Or.inr (Or.inr rfl)
      iapply client.recon_other V G n γs S ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null))) ws (f ws) hoth (Hrecon ws (f ws).2.1 hws hph)
      iframe)) $$ H3
  ihave Hall := client.bigSepM_give_list _ U _ Hlnd HlU $$ [Hnew Hoth]
  · iframe
  ihave Hall : iprop(∀ (γs' : StreamNames) (i' : Nat), [∗map] ws ↦ _u ∈ U,
      wsElem (V.atIdx i') G (n + 1) γs' (S.reconnect ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))) ws) $$ [Hall]
  · iintro %γs' %i'
    iapply (BigSepM.bigSepM_mono (fun {ws _} _ =>
      (client.wsElem_recon_any V G (n + 1) γs γs' S _ ws).trans
        (client.wsElem_recon_at V G (n + 1) γs' S _ ws i'))) $$ Hall
  (try wp_auto)
  icases Hopen with (⟨%Herr, %i, %γs2, %Dn, %cd', %Hi, #Hcli, Htok, Hrtok, #Hspec⟩ |
    ⟨⟨%Hwc, %Herr⟩, #Hse⟩)
  · subst Herr
    (try wp_auto)
    -- (D25) the new epoch: its count from `respc`'s position `sent.length`
    imod mono_nat_own_alloc (GF := GF) sent.length with ⟨%γc, Hcnt, -⟩
    imod monoListAuthOwn_update_app (GF := GF) [((γs2, sent.length, γc, i) : EpInfo)] $$ Hep with
      ⟨Hep, #Hlb⟩
    ihave #Hidx := monoListIdxOwn_get (GF := GF) eps.length ((γs2, sent.length, γc, i) : EpInfo)
      (by simp) $$ Hlb
    wp_apply wp_fork $$ [Hrtok Hprod Hcnt]
    · wp_apply wp_serve V G callSl wc γs2 Dn cd' eps.length γc i sent $$ [$Hrtok $Hprod $Hcnt]
      · iframe #
      itrivial
    iapply HΦ
    iexists m', r, rc', γrc', ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))
    iframe
    unfold sliceOwn wgAdder
    iframe
    isplitr
    · ipureintro; exact HgOk'
    ileft
    isplitr
    · ipureintro; rfl
    iexists i, γs2, Dn, cd', γc
    iframe #
    iframe
    ipureintro; exact Hi
  · cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      (try wp_auto)
      wp_apply wp_Error (GoInterface.ok e) $$ [$Hse] as %err' ⟨%Hne', #Hse', -⟩
      · ipureintro; simp
      iapply HΦ
      iexists m', r, rc', γrc', ((S.l ++ keys.filterMap (S.M !! ·)).filter (fun x => !decide (x = null)))
      iframe
      unfold sliceOwn wgAdder
      iframe
      isplitr
      · ipureintro; exact HgOk'
      iright
      isplitr
      · ipureintro; exact ⟨rfl, Hne'⟩
      iframe #
      iframe

end proof

end EtcdGrove
end Perennial
