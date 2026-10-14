/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__monitorLease.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__monitorLease
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__rescind
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__leaseID
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-- `Watch(key, WithRev(rev))` is a single-key watch from `rev` that does not panic. -/
theorem monitorLease_watch_opts (key : GoString) (rev : w64) :
    (opWatchModel key [withRevM rev]).isRangeWatch rev = true ∧
      ¬ opWatchPanics key [withRevM rev] ∧ (opWatchModel key [withRevM rev]).key = key ∧
      (opWatchModel key [withRevM rev]).base.rangeEnd = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [opWatchModel, opWatchPanics, OpFull.watchPanics, opFold, OpFull.getInit, OpFull.newOp,
    OpModel.zero, withRevM, OpFull.isRangeWatch]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.monitorLease.wp_proof
    (hLID : leasingKV.leaseID.spec (GF := GF) (hG := hG))
    (hWR : EtcdGrove.WithRev.spec (GF := GF) (hG := hG))
    (hRes : leasingKV.rescind.spec (GF := GF) (hG := hG)) :
    leasingKV.monitorLease.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key rev
  wp_start as ⟨#Hlkv, Hrd, #Hsr, #Hctx, %Hrev⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hcl, #Hkvf, #Hpfxf, #Hctxf,
    #Hcan, #Hosl, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  ihave #HLC' := HLC
  iunfold isLeasingClient at HLC'
  icases HLC' with ⟨-, ⟨%w, #Hwf, #HW⟩, -⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  wp_apply context.wp_WithCancel iprop(True) lctx lcs $$ [$Hlctx $Hlcc]
      as %cctx %γc %ccancel ⟨#Hcancel, #Hcctx, #Hccc⟩
  ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
  (try wp_auto)
  ihave #Hcctx2 := Hcctx
  iNamed Hcctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  ihave IH : iprop(∃ r : w64, "rev" ∷ rev_ptr ↦ r ∗ "Hrd" ∷ lkvReader lkv γ pfx ∗
      "%Hr" ∷ ⌜0 ≤ sint.Z r ∧ sint.Z r < 2 ^ 63 - 1⌝) $$ [rev Hrd]
  · iexists rev
    simp only [named]
    iframe
    ipureintro; exact Hrev
  wp_for IH
  wp_apply HErrU as %cerr -
  cases cerr with
  | ok e =>
    wp_auto
    simp only [false_neq_true, decide_false, Bool.false_eq_true, ↓reduceIte, decide_true]
    (try wp_auto)
    wp_apply Hcancel'
    · imodintro; itrivial
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  wp_auto
  rw [ite_eq_left (by simp)]
  wp_auto
  wp_if_destruct
  · ihave #HKV' := HKV
    iunfold isEtcdKV at HKV'
    ihave #Hnil := concurrency.optsAt_nil (GF := GF)
    ihave #H0 : etcdReached (GF := GF) (W64 0) $$ []
    · iapply etcdReached_zero
    ihave #HG := HKV' $$ %ctx %cs %(pfx ++ key) %slice.nil %([] : List (OpFull → OpFull)) %(W64 0)
    wp_apply HG $$ [] as %gresp %gerr #Hgres
    · iframe Hctx Hnil H0
      ipureintro
      exact ⟨concurrency.keyOp_not_panics, (concurrency.keyOp_t (pfx ++ key)).1⟩
    iunfold kvGetResult at Hgres
    icases Hgres with (%Hgne | ⟨%Hgnil, %r, %gm, #HgRev, -, -, %HRle, Hgr⟩)
    · -- an error: the next iteration
      obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
        cases gerr with
        | nil => exact absurd rfl Hgne
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      wp_for_post
      iframe
      iexists _
      simp only [named]
      iframe
      ipureintro; assumption
    subst Hgnil
    have HkT : (opGetModel (pfx ++ key) []).t = W64 1 ∧ (opGetModel (pfx ++ key) []).key = pfx ++ key ∧
        (opGetModel (pfx ++ key) []).base.rangeEnd = [] ∧ (opGetModel (pfx ++ key) []).base.rev = W64 0 ∧
        (opGetModel (pfx ++ key) []).base.serializable = false := concurrency.keyOp_t (pfx ++ key)
    have Hr0 : 0 ≤ sint.Z r := by
      have := HRle.1 HkT.2.2.2.2
      rw [show sint.Z (W64 0) = 0 from rfl] at this
      exact this
    have HkP : (opGetModel (pfx ++ key) []).isPrefixGet [] = false :=
      concurrency.keyOp_isPrefixGet [] (pfx ++ key)
    rw [ite_eq_right (c := (opGetModel (pfx ++ key) []).isPrefixGet [] = true) (by rw [HkP]; simp)]
    unfold getRespRange
    rw [ite_eq_left (show (opGetModel (pfx ++ key) []).base.rev = W64 0 ∧
        KeyRangeUnder [] (opGetModel (pfx ++ key) []).key (opGetModel (pfx ++ key) []).base.rangeEnd from
      ⟨HkT.2.2.2.1, by intro k _; exact List.nil_prefix⟩)]
    icases Hgr with ⟨%s', %gsl, %gps, %gkvs, -, -, #Hgsl, #Hgps, #Hgkvs, -⟩
    iunfold getRespRev at HgRev
    icases HgRev with ⟨%ghdr, #Hgh, %Hghnn, #HghR⟩
    iunfold kvPtrsAt at Hgkvs
    icases Hgkvs with ⟨%Hgl, #Hgkv⟩
    ihave %Hgsl' := ownSlice_len $$ Hgps
    wp_auto
    wp_if_destruct
    · -- no key-value: rescind
      wp_apply hRes lkv γ pfx cctx
        ({ Values := lcs.Values, Deadline := lcs.Deadline, Done_gn := γc,
           PDone := iprop(lcs.PDone ∨ True) } : context.ContextDesc (IProp GF)) key r
        $$ [$Hpkg $Hlkv $Hcctx]
      (try wp_auto)
      wp_for_post
      wp_apply Hcancel'
      · imodintro; itrivial
      (try wp_auto)
      iapply HΦ
      itrivial
    have Hglen : 0 < sint.Z gsl.len := by
      have h1 : gsl.len ≠ W64 0 := fun h => Hif (by rw [h])
      have h2 := Hgsl'.2
      have : sint.Z gsl.len ≠ 0 := fun h => h1 (by word)
      omega
    obtain ⟨p0, Hp0⟩ : ∃ p0, gps[sint.nat (W64 0)]? = some p0 :=
      ⟨_, List.getElem?_eq_getElem (by have := Hgsl'.1; word)⟩
    obtain ⟨v0, Hv0⟩ : ∃ v0, gkvs[sint.nat (W64 0)]? = some v0 :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hgl]; have := Hgsl'.1; word)⟩
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gsl.len from ⟨by decide, Hglen⟩)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) p0 gsl DFrac.discard gps (by decide) Hp0 $$ Hgps
      with ⟨#Hle0, -⟩
    ihave #Hkv0 := Hgkv $$ %(sint.nat (W64 0)) %p0 %v0 %Hp0 %Hv0
    iunfold kvValAt at Hkv0
    icases Hkv0 with ⟨%kSl, %vSl, -, -, -, -, -, #HV0, #HVs0, -⟩
    wp_auto
    wp_apply wp_bytes_to_string vSl v0.value DFrac.discard $$ [$HVs0] as -
    (try wp_auto)
    wp_if_destruct
    · -- `"REVOKE"`: rescind
      wp_apply hRes lkv γ pfx cctx
        ({ Values := lcs.Values, Deadline := lcs.Deadline, Done_gn := γc,
           PDone := iprop(lcs.PDone ∨ True) } : context.ContextDesc (IProp GF)) key r
        $$ [$Hpkg $Hlkv $Hcctx]
      (try wp_auto)
      wp_for_post
      wp_apply Hcancel'
      · imodintro; itrivial
      (try wp_auto)
      iapply HΦ
      itrivial
    (try wp_auto)
    wp_apply hWR (r + W64 1) $$ [$Hcv] as %f #Hf
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    ipersist Hsl
    generalize hsl : slice.mk sl _ _ = optsSl
    ihave #Hopts : optsAt optsSl ([withRevM (r + W64 1)] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hsl
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f' %g %Hf' %Hg
      rcases i with _ | i
      · cases Hf'; cases Hg; iexact Hf
      · simp at Hf'
    iunfold isEtcdRangeWatcher at HW
    ihave #HWa := HW $$ %cctx
      %({ Values := lcs.Values, Deadline := lcs.Deadline, Done_gn := γc,
          PDone := iprop(lcs.PDone ∨ True) } : context.ContextDesc (IProp GF))
      %(pfx ++ key) %optsSl %([withRevM (r + W64 1)] : List (OpFull → OpFull)) %(r + W64 1)
    wp_auto
    obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := monitorLease_watch_opts (pfx ++ key) (r + W64 1)
    wp_apply HWa $$ [] as %wch %γw ⟨#Hwch, Hcons, -⟩
    · iframe Hcctx Hopts
      ipureintro
      refine ⟨Hw1, Hw2, by word, ?_⟩
      rw [Hw3, Hw4]; intro k _; exact List.nil_prefix
    ihave IH2 : iprop(∃ (rcv : List go_etcd_io.etcd.client.v3.WatchResponse)
        (v : go_etcd_io.etcd.client.v3.WatchResponse),
        "Hcons" ∷ spscConsumer γw.spsc rcv ∗ "resp" ∷ resp_ptr ↦ v) $$ [Hcons resp]
    · iexists [], _
      simp only [named]
      iframe
    wp_for IH2
    (try rw [ite_eq_left (by simp)])
    (try wp_auto)
    wp_bind (App (Val (chan.receive _)) _)
    wp_apply wp_spsc_receive γw.spsc wch
      (rangeWatchElem γw [] (opWatchModel (pfx ++ key) [withRevM (r + W64 1)]) (r + W64 1))
      (fun _ => iprop(True)) rcv $$ [$Hwch $Hcons] as %v' %ok H
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨-, %Hv⟩
      wp_auto
      wp_for_post
      (try wp_auto)
      wp_for_post
      iframe
      iexists W64 0
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    simp only [↓reduceIte]
    icases H with ⟨HP, Hcons⟩
    iunfold rangeWatchElem at HP
    icases HP with ⟨%rm, %c, %c', #Hevs, -, -, -, -, #Hok⟩
    iunfold eventsAt at Hevs
    icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
    wp_auto
    ihave %Hsl := ownSlice_len $$ Hls
    ihave IH3 : iprop(∃ (n : w64) (e0 : Loc),
        "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝) $$ [i ev]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IH3
    wp_if_destruct
    · have Hif' : sint.Z n < sint.Z v'.Events'.len := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have Hlt : sint.nat n < ls.length := by word
      obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨e, He⟩ : ∃ e, rm.events[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z v'.Events'.len := ⟨Hn.1, by word⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) l v'.Events' DFrac.discard ls Hn.1 Hl $$ Hls
        with ⟨#Hle, -⟩
      ihave #He := Hev $$ %(sint.nat n) %l %e %Hl %He
      iunfold eventAt at He
      icases He with ⟨%keySl, #Htyp, #HKv, -, -, #HMR⟩
      iunfold rangeWatchRespOk at Hok
      icases Hok with ⟨-, #Hok⟩
      ihave #Hok' := Hok $$ %(sint.nat n) %e %He
      iunfold rangeWatchEvOk at Hok'
      icases Hok' with ⟨%Hke, -, #Hdel, #Hput⟩
      ihave #Hval : iprop(∃ (valSl : GoSlice) (val : GoString) (lease : w64),
          structFieldRef mvccpb.KeyValue go!"Value" e.kv ↦□ valSl ∗ valSl ↦*□ val ∗
          structFieldRef mvccpb.KeyValue go!"Lease" e.kv ↦□ lease) $$ []
      · rcases Hke.2.2.2 with ht | ht
        · ihave #Hp := Hput $$ %ht
          icases Hp with ⟨%v0, #Hkv, -⟩
          iunfold kvValAt at Hkv
          icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HV, #HVs, #HL⟩
          iexists vSl, v0.value, v0.lease
          iframe #
        · ihave #Hd := Hdel $$ %ht
          icases Hd with ⟨-, #Hd⟩
          iunfold delKvAt at Hd
          iexact Hd
      icases Hval with ⟨%valSl, %val, %lease, #HV, #HVs, #HL⟩
      wp_auto
      wp_apply wp_bytes_to_string valSl val DFrac.discard $$ [$HVs] as -
      (try wp_auto)
      wp_if_destruct
      · -- `"REVOKE"`: rescind if it is this session's lease, and return
        wp_apply hLID lkv γ pfx $$ [$Hpkg $Hlkv $Hrd $Hsr] as %id ⟨Hrd, -⟩
        (try wp_auto)
        wp_if_destruct
        · wp_apply hRes lkv γ pfx cctx
            ({ Values := lcs.Values, Deadline := lcs.Deadline, Done_gn := γc,
               PDone := iprop(lcs.PDone ∨ True) } : context.ContextDesc (IProp GF)) key e.rev
            $$ [$Hpkg $Hlkv $Hcctx]
          (try wp_auto)
          wp_for_post
          wp_for_post
          wp_for_post
          wp_apply Hcancel'
          · imodintro; itrivial
          (try wp_auto)
          iapply HΦ
          itrivial
        wp_for_post
        wp_for_post
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        itrivial
      -- not `"REVOKE"`: the next event
      wp_for_post
      iframe
      iexists n + W64 1, l
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    (try rw [if_decide_bool_eq_false, ite_eq_right (by intro h; apply Hif; simp [h])])
    wp_for_post
    iframe
    iexists rcv ++ [v'], v'
    simp only [named]
    iframe
  · wp_apply hWR (r + W64 1) $$ [$Hcv] as %f #Hf
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    ipersist Hsl
    generalize hsl : slice.mk sl _ _ = optsSl
    ihave #Hopts : optsAt optsSl ([withRevM (r + W64 1)] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hsl
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f' %g %Hf' %Hg
      rcases i with _ | i
      · cases Hf'; cases Hg; iexact Hf
      · simp at Hf'
    iunfold isEtcdRangeWatcher at HW
    ihave #HWa := HW $$ %cctx
      %({ Values := lcs.Values, Deadline := lcs.Deadline, Done_gn := γc,
          PDone := iprop(lcs.PDone ∨ True) } : context.ContextDesc (IProp GF))
      %(pfx ++ key) %optsSl %([withRevM (r + W64 1)] : List (OpFull → OpFull)) %(r + W64 1)
    wp_auto
    obtain ⟨Hw1, Hw2, Hw3, Hw4⟩ := monitorLease_watch_opts (pfx ++ key) (r + W64 1)
    wp_apply HWa $$ [] as %wch %γw ⟨#Hwch, Hcons, -⟩
    · iframe Hcctx Hopts
      ipureintro
      refine ⟨Hw1, Hw2, by word, ?_⟩
      rw [Hw3, Hw4]; intro k _; exact List.nil_prefix
    ihave IH2 : iprop(∃ (rcv : List go_etcd_io.etcd.client.v3.WatchResponse)
        (v : go_etcd_io.etcd.client.v3.WatchResponse),
        "Hcons" ∷ spscConsumer γw.spsc rcv ∗ "resp" ∷ resp_ptr ↦ v) $$ [Hcons resp]
    · iexists [], _
      simp only [named]
      iframe
    wp_for IH2
    (try rw [ite_eq_left (by simp)])
    (try wp_auto)
    wp_bind (App (Val (chan.receive _)) _)
    wp_apply wp_spsc_receive γw.spsc wch
      (rangeWatchElem γw [] (opWatchModel (pfx ++ key) [withRevM (r + W64 1)]) (r + W64 1))
      (fun _ => iprop(True)) rcv $$ [$Hwch $Hcons] as %v' %ok H
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨-, %Hv⟩
      wp_auto
      wp_for_post
      (try wp_auto)
      wp_for_post
      iframe
      iexists W64 0
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    simp only [↓reduceIte]
    icases H with ⟨HP, Hcons⟩
    iunfold rangeWatchElem at HP
    icases HP with ⟨%rm, %c, %c', #Hevs, -, -, -, -, #Hok⟩
    iunfold eventsAt at Hevs
    icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
    wp_auto
    ihave %Hsl := ownSlice_len $$ Hls
    ihave IH3 : iprop(∃ (n : w64) (e0 : Loc),
        "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ e0 ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝) $$ [i ev]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IH3
    wp_if_destruct
    · have Hif' : sint.Z n < sint.Z v'.Events'.len := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have Hlt : sint.nat n < ls.length := by word
      obtain ⟨l, Hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨e, He⟩ : ∃ e, rm.events[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z v'.Events'.len := ⟨Hn.1, by word⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) l v'.Events' DFrac.discard ls Hn.1 Hl $$ Hls
        with ⟨#Hle, -⟩
      ihave #He := Hev $$ %(sint.nat n) %l %e %Hl %He
      iunfold eventAt at He
      icases He with ⟨%keySl, #Htyp, #HKv, -, -, #HMR⟩
      iunfold rangeWatchRespOk at Hok
      icases Hok with ⟨-, #Hok⟩
      ihave #Hok' := Hok $$ %(sint.nat n) %e %He
      iunfold rangeWatchEvOk at Hok'
      icases Hok' with ⟨%Hke, -, #Hdel, #Hput⟩
      ihave #Hval : iprop(∃ (valSl : GoSlice) (val : GoString) (lease : w64),
          structFieldRef mvccpb.KeyValue go!"Value" e.kv ↦□ valSl ∗ valSl ↦*□ val ∗
          structFieldRef mvccpb.KeyValue go!"Lease" e.kv ↦□ lease) $$ []
      · rcases Hke.2.2.2 with ht | ht
        · ihave #Hp := Hput $$ %ht
          icases Hp with ⟨%v0, #Hkv, -⟩
          iunfold kvValAt at Hkv
          icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HV, #HVs, #HL⟩
          iexists vSl, v0.value, v0.lease
          iframe #
        · ihave #Hd := Hdel $$ %ht
          icases Hd with ⟨-, #Hd⟩
          iunfold delKvAt at Hd
          iexact Hd
      icases Hval with ⟨%valSl, %val, %lease, #HV, #HVs, #HL⟩
      wp_auto
      wp_apply wp_bytes_to_string valSl val DFrac.discard $$ [$HVs] as -
      (try wp_auto)
      wp_if_destruct
      · -- `"REVOKE"`: rescind if it is this session's lease, and return
        wp_apply hLID lkv γ pfx $$ [$Hpkg $Hlkv $Hrd $Hsr] as %id ⟨Hrd, -⟩
        (try wp_auto)
        wp_if_destruct
        · wp_apply hRes lkv γ pfx cctx
            ({ Values := lcs.Values, Deadline := lcs.Deadline, Done_gn := γc,
               PDone := iprop(lcs.PDone ∨ True) } : context.ContextDesc (IProp GF)) key e.rev
            $$ [$Hpkg $Hlkv $Hcctx]
          (try wp_auto)
          wp_for_post
          wp_for_post
          wp_for_post
          wp_apply Hcancel'
          · imodintro; itrivial
          (try wp_auto)
          iapply HΦ
          itrivial
        wp_for_post
        wp_for_post
        wp_for_post
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ
        itrivial
      -- not `"REVOKE"`: the next event
      wp_for_post
      iframe
      iexists n + W64 1, l
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    (try rw [if_decide_bool_eq_false, ite_eq_right (by intro h; apply Hif; simp [h])])
    wp_for_post
    iframe
    iexists rcv ++ [v'], v'
    simp only [named]
    iframe
end proof

end leasing
end EtcdGrove
end Perennial
