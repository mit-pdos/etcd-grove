/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__watch.lean`.
Lean-first. The linearization point is the taking of the lock (the start state, read under it;
a selector, `SendInitialEvents` or a flagged failure fire the caller's update at whatever state).
The watcher's goroutine is `watcher.run`'s spec (`runPre`); the watcher is registered with the
server (its stop flag and stop channel's sending side join `watchersLocked`) under the lock.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__watch
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__chance
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewBadRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.watcher__run
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__list
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.WatchLemmas
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewResourceExpired
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.MapLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.SrvLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem lo_watch [ApiDeps] (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (dq : DFrac)
    (lo : kd.meta.ListOptions) :
    kd.meta.ListOptions.own (GF := GF) opts dq lo ⊢ kd.meta.ListOptions.own opts dq lo ∗
      ⌜opts.LabelSelector' = lo.LabelSelector' ∧ opts.FieldSelector' = lo.FieldSelector' ∧
        (opts.SendInitialEvents' = null ↔ lo.SendInitialEvents' = none) ∧
        opts.ResourceVersion' = lo.ResourceVersion' ∧
        opts.AllowWatchBookmarks' = lo.AllowWatchBookmarks'⌝ := by
  unfold kd.meta.ListOptions.own
  iintro ⟨TypeMeta, %h1, %h2, %h3, %h4, %h5, %h6, TimeoutSeconds, %h7, %h8, SendInitialEvents, %h9⟩
  icases ownPtrD_null _ _ _ _ $$ SendInitialEvents with ⟨SendInitialEvents, %hs⟩
  isplitl
  · iframe
    ipureintro; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · ipureintro; exact ⟨h1, h2, hs, h5, h4⟩

theorem Server.watch.wp_proof
    (wp_chance : Server.chance.spec (GF := GF) (hG := hG))
    (wp_copyObject : copyObject.spec (GF := GF) (hG := hG))
    (wp_run : watcher.run.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : apierrors.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_NewBadRequest : apierrors.NewBadRequest.spec (GF := GF) (hG := hG))
    (wp_NewResourceExpired : apierrors.NewResourceExpired.spec (GF := GF) (hG := hG))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.watch.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg r t ns opts dq lo admin
  wp_start as ⟨#Hs, #Ht, Ho⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  ihave #Hinit : (github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.apimodelInit :
    IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%eS, #HeS⟩, ⟨%eR, #HeR⟩, ⟨%sA, #HeA⟩⟩
  ihave #Hsrv := Hs
  iunfold isServer at Hs
  icases Hs with ⟨%L, #Hs⟩
  ihave %Htl := srvFixed_tableOf s γ L cfg r t $$ [$Hs $Ht]
  subst Htl
  ihave ⟨#Hfx, -⟩ := srvFixed_tbl s γ L cfg r $$ Hs
  iunfold tableFixed at Hfx
  icases Hfx with ⟨#Hres, #Hnsd, #Hobjs, #Hemp, -⟩
  iNamed Hs
  iNamed Hcfg
  icases lo_watch opts dq lo $$ Ho with ⟨Ho, %Hlo⟩
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · by_cases hsn : opts.SendInitialEvents' = null
      rotate_left
      · -- `SendInitialEvents`
        simp only [decide_eq_false hsn, Bool.not_false, ↓reduceIte]
        (try wp_auto)
        wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
        ipersist Hp
        imod (au_read_any γ (fun σ => iprop(∀ w err, kd.meta.ListOptions.own opts dq lo ∗ watchRet γ cfg admin r ns lo σ w err -∗ Φ (PairV #w #err)))) $$ HΦ with ⟨%σ, HΦ⟩
        (try wp_auto)
        iapply HΦ
        iframe
        unfold watchRet
        rw [if_pos (by right; right; cases h : lo.SendInitialEvents' with | none => exact absurd (Hlo.2.2.1.mpr h) hsn | some _ => rfl)]
        isplitr
        · ipureintro; rfl
        unfold errIs
        iexists p, st
        iframe #
        ipureintro
        exact ⟨rfl, Hst.2.1, Hst.2.2⟩
      · -- no selector, no `SendInitialEvents`
        simp only [decide_eq_true hsn, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        have hsie : lo.SendInitialEvents' = none := Hlo.2.2.1.mp hsn
        have hns : ¬ (lo.LabelSelector' ≠ go!"" ∨ lo.FieldSelector' ≠ go!"" ∨
            lo.SendInitialEvents'.isSome) := by
          rw [← Hlo.1, ← Hlo.2.1, hsie]; simp_all
        wp_apply wp_chance $$ [$Hsrv] as %b %Hb
        cases b
        · (try wp_auto)
          wp_apply chan.wp_make1 (V := k8s_io.apimachinery.pkg.watch.Event) as %ch %γc ⟨#Hch, %_, Hoc⟩
          (try wp_auto)
          wp_apply chan.wp_make1 (V := Unit) as %dch %γd ⟨#Hdch, %_, Hod⟩
          (try wp_auto)
          icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hwnn⟩
          iStructNamedSuffix «$r0» "_w"
          ipersist s_w
          ipersist t_w
          ipersist ns_w
          ipersist admin_w
          ipersist bookmarks_w
          ipersist ch_w
          ipersist done_w
          wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
          iunfold lockInv at Hinv
          icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
          iNamed Hlk
          have hwf := histOk_last_wf Hok
          icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
          iunfold tableLocked at Ht0
          icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
          ihave #Hpast := pastSt_of_auth γ _ H σ0 Hok $$ Hhist
          imod (au_read γ H σ0 (fun σ => iprop(∀ w err, kd.meta.ListOptions.own opts dq lo ∗
            watchRet γ cfg admin r ns lo σ w err -∗ Φ (PairV #w #err))))
            $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
          (try wp_auto)
          wp_if_destruct
          · -- the version ""
            have hrv0 : lo.ResourceVersion' = go!"" ∨ lo.ResourceVersion' = go!"0" := Or.inl (Hlo.2.2.2.1 ▸ Hif)
            wp_func_lits
            wp_bind (App (App (Val (map.forRange _ _)) _) _)
            iapply wp_map_for_range (fun (keys : List Key) (i : Int) => iprop(∃ (osl : GoSlice)
                (xs : List GoInterface) (ox : GoInterface) (kx : Key),
                "%Hi" ∷ ⌜0 ≤ i⌝ ∗
                "initial_w" ∷ «$r0_ptr».[apimodel.watcher, go!"initial"] ↦ osl ∗ "Hosl" ∷ osl ↦* xs ∗
                "Hocap" ∷ ownSliceCap apimodel.object osl (DFrac.own 1) ∗
                "Hxs" ∷ ([∗list] x;o ∈ xs;(keys.take i.toNat).filterMap
                  (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none), objAt x (DFrac.own 1) o) ∗
                "obj" ∷ obj_ptr ↦ ox ∗ "key" ∷ key_ptr ↦ kx ∗ "ns" ∷ ns_ptr ↦ ns ∗ "w" ∷ w_ptr ↦ «$r0_ptr» ∗
                "Hrel" ∷ objsRel M (σ0.tbl r).objs)) $$ HM
            iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
            isplitl [initial_w obj key ns w Hrel]
            · iexists slice.nil, [], _, _
              simp only [named]
              iframe
              isplitr
              · ipureintro; exact Int.le_refl _
              isplitr
              · iapply ownSlice_nil
              isplitr
              · iapply ownSliceCap_nil
              simp only [Int.toNat_zero, List.take_zero, List.filterMap_nil]
              iapply BigSepL2.bigSepL2_nil.2; itrivial
            isplitr
            · imodintro
              iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
              iNamed HP
              wp_auto
              icases objsRel_lookup M (σ0.tbl r).objs key v Hv $$ Hrel with ⟨%o, %ho, Hx, Hrelb⟩
              have hstep := take_succ_filterMap key Hi Hkey
                (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none)
              wp_if_destruct
              · wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
                ihave Hrel := Hrelb $$ Hx
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %l1 ⟨Hl1, _⟩
                simp only [go.arrayLiteralSize, List.foldl]
                (try wp_auto)
                wp_apply wp_slice_append $$ [$Hosl $Hocap $Hl1] as %osl' ⟨Hosl, Hocap, -⟩
                (try wp_auto)
                unfold forMapPostcondition
                iright; ileft
                isplitr
                · ipureintro; rfl
                iexists osl', xs ++ [y], _, _
                simp only [named]
                rw [hstep]
                simp only [inNs, _root_.decide_true, Bool.true_or, Bool.or_true, ↓reduceIte, ho, Option.toList_some]
                iframe
                isplitr
                · ipureintro; omega
                iapply BigSepL2.bigSepL2_nil.2; itrivial
              · wp_if_destruct
                · wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
                  ihave Hrel := Hrelb $$ Hx
                  wp_apply wp_slice_literal
                  isplitr
                  · ipureintro; rfl
                  iintro %l1 ⟨Hl1, _⟩
                  simp only [go.arrayLiteralSize, List.foldl]
                  (try wp_auto)
                  wp_apply wp_slice_append $$ [$Hosl $Hocap $Hl1] as %osl' ⟨Hosl, Hocap, -⟩
                  (try wp_auto)
                  unfold forMapPostcondition
                  iright; ileft
                  isplitr
                  · ipureintro; rfl
                  iexists osl', xs ++ [y], _, _
                  simp only [named]
                  rw [hstep]
                  simp only [inNs, _root_.decide_true, Bool.true_or, Bool.or_true, ↓reduceIte, ho, Option.toList_some]
                  iframe
                  isplitr
                  · ipureintro; omega
                  iapply BigSepL2.bigSepL2_nil.2; itrivial
                · have hin : inNs ns key = false := by
                    simp only [inNs, Bool.or_eq_false_iff, decide_eq_false_iff_not]
                    exact ⟨by assumption, by assumption⟩
                  ihave Hrel := Hrelb $$ Hx
                  unfold forMapPostcondition
                  iright; ileft
                  isplitr
                  · ipureintro; rfl
                  iexists osl, xs, _, _
                  simp only [named]
                  rw [hstep]
                  simp only [hin, Bool.false_eq_true, ↓reduceIte, Option.toList_none, List.append_nil]
                  iframe
                  ipureintro; omega
            iintro HP HM
            iNamed HP
            ihave %hdom := (BigSepM2.bigSepM2_lookup_iff (PROP := IProp GF)) $$ Hrel
            have hmem : ∀ k, k ∈ keys ↔ ((σ0.tbl r).objs !! k).isSome := fun k => (Hkset k).trans (hdom k)
            have hperm := perm_keys_filterMap (σ0.tbl r).objs keys Hknodup hmem (inNs ns)
            have htk : keys.take ((GMap.size M : Nat) : Int).toNat = keys := by
              rw [Int.toNat_natCast, ← Hklen, List.take_length]
            rw [htk]
            have hinits : listOk r ns σ0 (keys.filterMap (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none)) := by
              unfold listOk; exact hperm
            generalize (keys.filterMap (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none)) = inits at hinits ⊢
            have hstart : watchStartOk r ns lo σ0 inits σ0.rev := by
              unfold watchStartOk; rw [if_pos hrv0]; exact ⟨rfl, hinits⟩
            (try wp_auto)
            ihave %Hcsl := ownSlice_len _ _ _ $$ Hsl
            ihave %Hcsl2 := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Hcs
            ihave IH : iprop(∃ (n : w64), "next" ∷ next_ptr ↦ n ∗
                "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ (σ0.tbl r).log.length ∧
                  ∀ j (hj : j < sint.nat n) (hj' : j < (σ0.tbl r).log.length),
                    ((σ0.tbl r).log[j]'hj').rv.toNat ≤ σ0.rev.toNat⌝) $$ [next]
            · iexists W64 0
              iframe
              ipureintro
              exact ⟨by word, by simp, fun j hj _ => absurd hj (by simp)⟩
            wp_for IH
            wp_if_destruct
            · have Hlt : sint.nat n < cs.length := by
                have := sint_nat_lt_of_lt n sl.len Hif Hn.1; omega
              have Hlt' : sint.nat n < (σ0.tbl r).log.length := by omega
              have hsucc := w64_succ_nat n Hn.1 (by have := sint_nat_lt sl.len; omega)
              obtain ⟨c, hc⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
              have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
              simp only [Hbnd, _root_.and_self, ↓reduceIte]
              icases ownSlice_elem_acc (sint.Z n) c sl (DFrac.own 1) cs Hn.1 hc $$ Hsl with ⟨Hc, Hslb⟩
              icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
              iStructNamedSuffix Hc "_c"
              (try wp_auto)
              ihave Hc := typedPointsto_combine _ c _ Hcnn $$ [typ_c rv_c obj_c]
              · simp only [TypedPointsto.typedPointstoDef]
                iframe
              ihave Hsl := Hslb $$ %c Hc
              have hset : cs.set (sint.nat n) c = cs := by
                obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hc
                rw [← h2]; exact List.set_getElem_self h1
              rw [show (sint.Z n).toNat = sint.nat n from rfl, hset]
              icases changes_rv_at cs (σ0.tbl r).log (sint.nat n) c _ hc
                (List.getElem?_eq_getElem Hlt') $$ Hcs with ⟨Hcs, %hcrv⟩
              by_cases hle : uint.Z c.rv' ≤ uint.Z σ0.rev
              · -- at most the start version: on
                simp only [hle, _root_.decide_true, ↓reduceIte]
                (try wp_auto)
                wp_for_post
                iframe
                iexists n + W64 1
                iframe
                ipureintro
                refine ⟨hsucc.1, by rw [hsucc.2]; omega, ?_⟩
                intro j hj hj'
                rw [hsucc.2] at hj
                by_cases hjn : j = sint.nat n
                · subst hjn
                  rw [← hcrv]
                  simp [uint.Z] at hle
                  omega
                · exact Hn.2.2 j (by omega) hj'
              · -- after the start version: the loop stops at `n`
                have hft : (#false : val) ≠ #true := by
                  intro h; have := go.intoVal_inj h; simp at this
                simp only [hle, _root_.decide_false]
                rw [decide_eq_false hft]
                simp only [Bool.false_eq_true, ↓reduceIte]
                (try wp_auto)
                (try simp only [decide_True, ↓reduceIte])
                have hls : logStart (σ0.tbl r).log σ0.rev = sint.nat n := by
                  apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                  intro _
                  rw [← hcrv]
                  simp [uint.Z] at hle
                  omega
                (try rw [if_pos (show decide True = true from rfl)])
                (try wp_auto)
                have hnw : W64 (logStart (σ0.tbl r).log σ0.rev) = n := by
                  rw [hls]; exact w64_of_sint_nat n Hn.1
                -- the stop channel, and the watcher registered
                imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                  with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
                · ileft; iexact Hod
                iunfold watchersLocked at Hws
                icases Hws with ⟨%W, Hauth, HWs⟩
                cases hW : W.lookup «$r0_ptr» with
                | some c0 =>
                  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                    with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                  ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                  exact absurd hF id
                | none =>
                imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                    Hlog Hsl Hcap Hcs]
                · iunfold lockInv
                  inext
                  iexists σ0, H
                  iframe Hhist
                  isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold srvLocked
                    iframe
                    ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                    · iunfold tableLocked
                      iexists M, sl, cs
                      iframe
                    iframe
                    ipureintro; exact Huidlt
                  isplitr
                  · ipureintro; exact Hok
                  iunfold watchersLocked
                  iexists W.insert «$r0_ptr» (spscCode g)
                  iframe Hauth
                  iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                  iframe HWs
                  iexists g, false
                  iframe
                  isplitl []
                  · ipureintro; rfl
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  iexact Hdprod
                -- the result channel and the cursor
                imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log σ0.rev, σ0.rev)] : List Pos'))
                  with ⟨%γcur, Hcur, #Hcurlb⟩
                imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                    (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits)
                    (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                  with ⟨%gch, #Hspsc, Hprod, Hcons⟩
                · ileft; iexact Hoc
                rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) =
                  evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits from rfl]
                (try wp_auto)
                rw [← hnw]
                ipersist initial_w
                wp_apply wp_fork $$ [initial_w Hosl Hxs next_w sentRV_w Hprod Hdcons Hcur]
                · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                      (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) $$ [$Hpkg initial_w Hosl Hxs next_w
                      sentRV_w Hprod Hdcons Hcur]
                  · unfold runPre
                    iexists s, (L.tbl r).t, osl, ch, dch, g, opts.AllowWatchBookmarks', xs, σ0.rev, σ0
                    iframe
                    iframe #
                    ipureintro
                    exact ⟨by rw [Hlo.2.2.2.2], Nat.le_refl _⟩
                  ipureintro; exact isPanic_intoVal _
                (try wp_auto)
                iapply HΦ
                iframe Ho
                unfold watchRet
                rw [if_neg hns]
                iright
                iright
                isplitr
                · ipureintro; rfl
                iexists ⟨gch, γcur⟩, inits, σ0.rev
                isplitl []
                · unfold watchAt
                  iexists «$r0_ptr», ch, dch, s, cfg, g
                  iframe #
                  ipureintro; rfl
                isplitl [Hcons]
                · unfold watchCons
                  iexists []
                  iframe
                  isplitr
                  · ipureintro; rfl
                  iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
                iframe #
                ipureintro; exact hstart
            · -- the log's end: the loop stops at `n`
              (try wp_auto)
              have hls : logStart (σ0.tbl r).log σ0.rev = sint.nat n := by
                apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                intro hk
                exfalso
                have := sint_nat_le_of_not_lt n sl.len Hif Hn.1
                omega
              (try rw [if_pos (show decide True = true from rfl)])
              (try wp_auto)
              have hnw : W64 (logStart (σ0.tbl r).log σ0.rev) = n := by
                rw [hls]; exact w64_of_sint_nat n Hn.1
              -- the stop channel, and the watcher registered
              imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
              · ileft; iexact Hod
              iunfold watchersLocked at Hws
              icases Hws with ⟨%W, Hauth, HWs⟩
              cases hW : W.lookup «$r0_ptr» with
              | some c0 =>
                icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                  with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                exact absurd hF id
              | none =>
              imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
              wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                  Hlog Hsl Hcap Hcs]
              · iunfold lockInv
                inext
                iexists σ0, H
                iframe Hhist
                isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold srvLocked
                  iframe
                  ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  iframe
                  ipureintro; exact Huidlt
                isplitr
                · ipureintro; exact Hok
                iunfold watchersLocked
                iexists W.insert «$r0_ptr» (spscCode g)
                iframe Hauth
                iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                iframe HWs
                iexists g, false
                iframe
                isplitl []
                · ipureintro; rfl
                simp only [Bool.false_eq_true, ↓reduceIte]
                iexact Hdprod
              -- the result channel and the cursor
              imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log σ0.rev, σ0.rev)] : List Pos'))
                with ⟨%γcur, Hcur, #Hcurlb⟩
              imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                  (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits)
                  (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                with ⟨%gch, #Hspsc, Hprod, Hcons⟩
              · ileft; iexact Hoc
              rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) =
                evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits from rfl]
              (try wp_auto)
              rw [← hnw]
              ipersist initial_w
              wp_apply wp_fork $$ [initial_w Hosl Hxs next_w sentRV_w Hprod Hdcons Hcur]
              · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                    (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) $$ [$Hpkg initial_w Hosl Hxs next_w
                    sentRV_w Hprod Hdcons Hcur]
                · unfold runPre
                  iexists s, (L.tbl r).t, osl, ch, dch, g, opts.AllowWatchBookmarks', xs, σ0.rev, σ0
                  iframe
                  iframe #
                  ipureintro
                  exact ⟨by rw [Hlo.2.2.2.2], Nat.le_refl _⟩
                ipureintro; exact isPanic_intoVal _
              (try wp_auto)
              iapply HΦ
              iframe Ho
              unfold watchRet
              rw [if_neg hns]
              iright
              iright
              isplitr
              · ipureintro; rfl
              iexists ⟨gch, γcur⟩, inits, σ0.rev
              isplitl []
              · unfold watchAt
                iexists «$r0_ptr», ch, dch, s, cfg, g
                iframe #
                ipureintro; rfl
              isplitl [Hcons]
              · unfold watchCons
                iexists []
                iframe
                isplitr
                · ipureintro; rfl
                iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
              iframe #
              ipureintro; exact hstart
          · wp_if_destruct
            · -- the version "0"
              have hrv0 : lo.ResourceVersion' = go!"" ∨ lo.ResourceVersion' = go!"0" := Or.inr (Hlo.2.2.2.1 ▸ Hif)
              wp_func_lits
              wp_bind (App (App (Val (map.forRange _ _)) _) _)
              iapply wp_map_for_range (fun (keys : List Key) (i : Int) => iprop(∃ (osl : GoSlice)
                  (xs : List GoInterface) (ox : GoInterface) (kx : Key),
                  "%Hi" ∷ ⌜0 ≤ i⌝ ∗
                  "initial_w" ∷ «$r0_ptr».[apimodel.watcher, go!"initial"] ↦ osl ∗ "Hosl" ∷ osl ↦* xs ∗
                  "Hocap" ∷ ownSliceCap apimodel.object osl (DFrac.own 1) ∗
                  "Hxs" ∷ ([∗list] x;o ∈ xs;(keys.take i.toNat).filterMap
                    (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none), objAt x (DFrac.own 1) o) ∗
                  "obj" ∷ obj_ptr ↦ ox ∗ "key" ∷ key_ptr ↦ kx ∗ "ns" ∷ ns_ptr ↦ ns ∗ "w" ∷ w_ptr ↦ «$r0_ptr» ∗
                  "Hrel" ∷ objsRel M (σ0.tbl r).objs)) $$ HM
              iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
              isplitl [initial_w obj key ns w Hrel]
              · iexists slice.nil, [], _, _
                simp only [named]
                iframe
                isplitr
                · ipureintro; exact Int.le_refl _
                isplitr
                · iapply ownSlice_nil
                isplitr
                · iapply ownSliceCap_nil
                simp only [Int.toNat_zero, List.take_zero, List.filterMap_nil]
                iapply BigSepL2.bigSepL2_nil.2; itrivial
              isplitr
              · imodintro
                iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
                iNamed HP
                wp_auto
                icases objsRel_lookup M (σ0.tbl r).objs key v Hv $$ Hrel with ⟨%o, %ho, Hx, Hrelb⟩
                have hstep := take_succ_filterMap key Hi Hkey
                  (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none)
                wp_if_destruct
                · wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
                  ihave Hrel := Hrelb $$ Hx
                  wp_apply wp_slice_literal
                  isplitr
                  · ipureintro; rfl
                  iintro %l1 ⟨Hl1, _⟩
                  simp only [go.arrayLiteralSize, List.foldl]
                  (try wp_auto)
                  wp_apply wp_slice_append $$ [$Hosl $Hocap $Hl1] as %osl' ⟨Hosl, Hocap, -⟩
                  (try wp_auto)
                  unfold forMapPostcondition
                  iright; ileft
                  isplitr
                  · ipureintro; rfl
                  iexists osl', xs ++ [y], _, _
                  simp only [named]
                  rw [hstep]
                  simp only [inNs, _root_.decide_true, Bool.true_or, Bool.or_true, ↓reduceIte, ho, Option.toList_some]
                  iframe
                  isplitr
                  · ipureintro; omega
                  iapply BigSepL2.bigSepL2_nil.2; itrivial
                · wp_if_destruct
                  · wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
                    ihave Hrel := Hrelb $$ Hx
                    wp_apply wp_slice_literal
                    isplitr
                    · ipureintro; rfl
                    iintro %l1 ⟨Hl1, _⟩
                    simp only [go.arrayLiteralSize, List.foldl]
                    (try wp_auto)
                    wp_apply wp_slice_append $$ [$Hosl $Hocap $Hl1] as %osl' ⟨Hosl, Hocap, -⟩
                    (try wp_auto)
                    unfold forMapPostcondition
                    iright; ileft
                    isplitr
                    · ipureintro; rfl
                    iexists osl', xs ++ [y], _, _
                    simp only [named]
                    rw [hstep]
                    simp only [inNs, _root_.decide_true, Bool.true_or, Bool.or_true, ↓reduceIte, ho, Option.toList_some]
                    iframe
                    isplitr
                    · ipureintro; omega
                    iapply BigSepL2.bigSepL2_nil.2; itrivial
                  · have hin : inNs ns key = false := by
                      simp only [inNs, Bool.or_eq_false_iff, decide_eq_false_iff_not]
                      exact ⟨by assumption, by assumption⟩
                    ihave Hrel := Hrelb $$ Hx
                    unfold forMapPostcondition
                    iright; ileft
                    isplitr
                    · ipureintro; rfl
                    iexists osl, xs, _, _
                    simp only [named]
                    rw [hstep]
                    simp only [hin, Bool.false_eq_true, ↓reduceIte, Option.toList_none, List.append_nil]
                    iframe
                    ipureintro; omega
              iintro HP HM
              iNamed HP
              ihave %hdom := (BigSepM2.bigSepM2_lookup_iff (PROP := IProp GF)) $$ Hrel
              have hmem : ∀ k, k ∈ keys ↔ ((σ0.tbl r).objs !! k).isSome := fun k => (Hkset k).trans (hdom k)
              have hperm := perm_keys_filterMap (σ0.tbl r).objs keys Hknodup hmem (inNs ns)
              have htk : keys.take ((GMap.size M : Nat) : Int).toNat = keys := by
                rw [Int.toNat_natCast, ← Hklen, List.take_length]
              rw [htk]
              have hinits : listOk r ns σ0 (keys.filterMap (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none)) := by
                unfold listOk; exact hperm
              generalize (keys.filterMap (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none)) = inits at hinits ⊢
              have hstart : watchStartOk r ns lo σ0 inits σ0.rev := by
                unfold watchStartOk; rw [if_pos hrv0]; exact ⟨rfl, hinits⟩
              (try wp_auto)
              ihave %Hcsl := ownSlice_len _ _ _ $$ Hsl
              ihave %Hcsl2 := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Hcs
              ihave IH : iprop(∃ (n : w64), "next" ∷ next_ptr ↦ n ∗
                  "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ (σ0.tbl r).log.length ∧
                    ∀ j (hj : j < sint.nat n) (hj' : j < (σ0.tbl r).log.length),
                      ((σ0.tbl r).log[j]'hj').rv.toNat ≤ σ0.rev.toNat⌝) $$ [next]
              · iexists W64 0
                iframe
                ipureintro
                exact ⟨by word, by simp, fun j hj _ => absurd hj (by simp)⟩
              wp_for IH
              wp_if_destruct
              · have Hlt : sint.nat n < cs.length := by
                  have := sint_nat_lt_of_lt n sl.len Hif Hn.1; omega
                have Hlt' : sint.nat n < (σ0.tbl r).log.length := by omega
                have hsucc := w64_succ_nat n Hn.1 (by have := sint_nat_lt sl.len; omega)
                obtain ⟨c, hc⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
                have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
                simp only [Hbnd, _root_.and_self, ↓reduceIte]
                icases ownSlice_elem_acc (sint.Z n) c sl (DFrac.own 1) cs Hn.1 hc $$ Hsl with ⟨Hc, Hslb⟩
                icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
                iStructNamedSuffix Hc "_c"
                (try wp_auto)
                ihave Hc := typedPointsto_combine _ c _ Hcnn $$ [typ_c rv_c obj_c]
                · simp only [TypedPointsto.typedPointstoDef]
                  iframe
                ihave Hsl := Hslb $$ %c Hc
                have hset : cs.set (sint.nat n) c = cs := by
                  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hc
                  rw [← h2]; exact List.set_getElem_self h1
                rw [show (sint.Z n).toNat = sint.nat n from rfl, hset]
                icases changes_rv_at cs (σ0.tbl r).log (sint.nat n) c _ hc
                  (List.getElem?_eq_getElem Hlt') $$ Hcs with ⟨Hcs, %hcrv⟩
                by_cases hle : uint.Z c.rv' ≤ uint.Z σ0.rev
                · -- at most the start version: on
                  simp only [hle, _root_.decide_true, ↓reduceIte]
                  (try wp_auto)
                  wp_for_post
                  iframe
                  iexists n + W64 1
                  iframe
                  ipureintro
                  refine ⟨hsucc.1, by rw [hsucc.2]; omega, ?_⟩
                  intro j hj hj'
                  rw [hsucc.2] at hj
                  by_cases hjn : j = sint.nat n
                  · subst hjn
                    rw [← hcrv]
                    simp [uint.Z] at hle
                    omega
                  · exact Hn.2.2 j (by omega) hj'
                · -- after the start version: the loop stops at `n`
                  have hft : (#false : val) ≠ #true := by
                    intro h; have := go.intoVal_inj h; simp at this
                  simp only [hle, _root_.decide_false]
                  rw [decide_eq_false hft]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  (try wp_auto)
                  (try simp only [decide_True, ↓reduceIte])
                  have hls : logStart (σ0.tbl r).log σ0.rev = sint.nat n := by
                    apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                    intro _
                    rw [← hcrv]
                    simp [uint.Z] at hle
                    omega
                  (try rw [if_pos (show decide True = true from rfl)])
                  (try wp_auto)
                  have hnw : W64 (logStart (σ0.tbl r).log σ0.rev) = n := by
                    rw [hls]; exact w64_of_sint_nat n Hn.1
                  -- the stop channel, and the watcher registered
                  imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                    with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
                  · ileft; iexact Hod
                  iunfold watchersLocked at Hws
                  icases Hws with ⟨%W, Hauth, HWs⟩
                  cases hW : W.lookup «$r0_ptr» with
                  | some c0 =>
                    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                      with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                    ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                    exact absurd hF id
                  | none =>
                  imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
                  wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                      Hlog Hsl Hcap Hcs]
                  · iunfold lockInv
                    inext
                    iexists σ0, H
                    iframe Hhist
                    isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                    · iunfold srvLocked
                      iframe
                      ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                      · iunfold tableLocked
                        iexists M, sl, cs
                        iframe
                      iframe
                      ipureintro; exact Huidlt
                    isplitr
                    · ipureintro; exact Hok
                    iunfold watchersLocked
                    iexists W.insert «$r0_ptr» (spscCode g)
                    iframe Hauth
                    iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                    iframe HWs
                    iexists g, false
                    iframe
                    isplitl []
                    · ipureintro; rfl
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    iexact Hdprod
                  -- the result channel and the cursor
                  imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log σ0.rev, σ0.rev)] : List Pos'))
                    with ⟨%γcur, Hcur, #Hcurlb⟩
                  imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                      (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits)
                      (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                    with ⟨%gch, #Hspsc, Hprod, Hcons⟩
                  · ileft; iexact Hoc
                  rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) =
                    evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits from rfl]
                  (try wp_auto)
                  rw [← hnw]
                  ipersist initial_w
                  wp_apply wp_fork $$ [initial_w Hosl Hxs next_w sentRV_w Hprod Hdcons Hcur]
                  · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                        (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) $$ [$Hpkg initial_w Hosl Hxs next_w
                        sentRV_w Hprod Hdcons Hcur]
                    · unfold runPre
                      iexists s, (L.tbl r).t, osl, ch, dch, g, opts.AllowWatchBookmarks', xs, σ0.rev, σ0
                      iframe
                      iframe #
                      ipureintro
                      exact ⟨by rw [Hlo.2.2.2.2], Nat.le_refl _⟩
                    ipureintro; exact isPanic_intoVal _
                  (try wp_auto)
                  iapply HΦ
                  iframe Ho
                  unfold watchRet
                  rw [if_neg hns]
                  iright
                  iright
                  isplitr
                  · ipureintro; rfl
                  iexists ⟨gch, γcur⟩, inits, σ0.rev
                  isplitl []
                  · unfold watchAt
                    iexists «$r0_ptr», ch, dch, s, cfg, g
                    iframe #
                    ipureintro; rfl
                  isplitl [Hcons]
                  · unfold watchCons
                    iexists []
                    iframe
                    isplitr
                    · ipureintro; rfl
                    iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
                  iframe #
                  ipureintro; exact hstart
              · -- the log's end: the loop stops at `n`
                (try wp_auto)
                have hls : logStart (σ0.tbl r).log σ0.rev = sint.nat n := by
                  apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                  intro hk
                  exfalso
                  have := sint_nat_le_of_not_lt n sl.len Hif Hn.1
                  omega
                (try rw [if_pos (show decide True = true from rfl)])
                (try wp_auto)
                have hnw : W64 (logStart (σ0.tbl r).log σ0.rev) = n := by
                  rw [hls]; exact w64_of_sint_nat n Hn.1
                -- the stop channel, and the watcher registered
                imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                  with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
                · ileft; iexact Hod
                iunfold watchersLocked at Hws
                icases Hws with ⟨%W, Hauth, HWs⟩
                cases hW : W.lookup «$r0_ptr» with
                | some c0 =>
                  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                    with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                  ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                  exact absurd hF id
                | none =>
                imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                    Hlog Hsl Hcap Hcs]
                · iunfold lockInv
                  inext
                  iexists σ0, H
                  iframe Hhist
                  isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold srvLocked
                    iframe
                    ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                    · iunfold tableLocked
                      iexists M, sl, cs
                      iframe
                    iframe
                    ipureintro; exact Huidlt
                  isplitr
                  · ipureintro; exact Hok
                  iunfold watchersLocked
                  iexists W.insert «$r0_ptr» (spscCode g)
                  iframe Hauth
                  iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                  iframe HWs
                  iexists g, false
                  iframe
                  isplitl []
                  · ipureintro; rfl
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  iexact Hdprod
                -- the result channel and the cursor
                imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log σ0.rev, σ0.rev)] : List Pos'))
                  with ⟨%γcur, Hcur, #Hcurlb⟩
                imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                    (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits)
                    (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                  with ⟨%gch, #Hspsc, Hprod, Hcons⟩
                · ileft; iexact Hoc
                rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) =
                  evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits from rfl]
                (try wp_auto)
                rw [← hnw]
                ipersist initial_w
                wp_apply wp_fork $$ [initial_w Hosl Hxs next_w sentRV_w Hprod Hdcons Hcur]
                · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                      (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) inits) $$ [$Hpkg initial_w Hosl Hxs next_w
                      sentRV_w Hprod Hdcons Hcur]
                  · unfold runPre
                    iexists s, (L.tbl r).t, osl, ch, dch, g, opts.AllowWatchBookmarks', xs, σ0.rev, σ0
                    iframe
                    iframe #
                    ipureintro
                    exact ⟨by rw [Hlo.2.2.2.2], Nat.le_refl _⟩
                  ipureintro; exact isPanic_intoVal _
                (try wp_auto)
                iapply HΦ
                iframe Ho
                unfold watchRet
                rw [if_neg hns]
                iright
                iright
                isplitr
                · ipureintro; rfl
                iexists ⟨gch, γcur⟩, inits, σ0.rev
                isplitl []
                · unfold watchAt
                  iexists «$r0_ptr», ch, dch, s, cfg, g
                  iframe #
                  ipureintro; rfl
                isplitl [Hcons]
                · unfold watchCons
                  iexists []
                  iframe
                  isplitr
                  · ipureintro; rfl
                  iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
                iframe #
                ipureintro; exact hstart
            · -- another version: the version it names, if issued
              have hrv1 : ¬ (lo.ResourceVersion' = go!"" ∨ lo.ResourceVersion' = go!"0") := by
                rw [← Hlo.2.2.2.1]; rintro (h | h) <;> simp_all
              wp_apply (wp_map_lookup2 go.string go.uint64 L.rvs (issuedMap σ0.rev.toNat) opts.ResourceVersion'
                (DFrac.own 1)) $$ Hrvsm as Hrvsm
              have hrvne : lo.ResourceVersion' ≠ go!"" ∧ lo.ResourceVersion' ≠ go!"0" := by
                constructor <;> intro h <;> exact hrv1 (by simp [h])
              have hiss : σ0.issued lo.ResourceVersion' = issuedMap σ0.rev.toNat !! opts.ResourceVersion' := by
                rw [Hlo.2.2.2.1]; rfl
              ihave Hosl0 := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
              ihave Hocap0 := ownSliceCap_nil (V := GoInterface) (GF := GF)
              cases hk : issuedMap σ0.rev.toNat !! opts.ResourceVersion' with
              | none =>
                -- not issued: expired
                (try simp only [Option.isSome_none, Option.getD_none])
                (try wp_auto)
                wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                · iunfold lockInv
                  iexists σ0, H
                  iframe
                  iunfold srvLocked
                  iframe
                  ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                  · iunfold tableLocked
                    iexists M, sl, cs
                    iframe
                  iframe
                  ipureintro; exact ⟨Huidlt, Hok⟩
                (try wp_auto)
                wp_apply +noauto wp_NewResourceExpired as %p ⟨%st, Hp, %Hst⟩
                ipersist Hp
                (try wp_auto)
                iapply HΦ
                iframe Ho
                unfold watchRet
                rw [if_neg hns]
                iright
                ileft
                isplitr
                · ipureintro
                  exact ⟨rfl, hrvne.1, hrvne.2, Or.inl (by rw [hiss, hk])⟩
                unfold errIs
                iexists p, st
                iframe #
                ipureintro
                exact ⟨rfl, Hst.2.1, Hst.2.2⟩
              | some n0v =>
                (try simp only [Option.isSome_some, Option.getD_some])
                (try wp_auto)
                have hnle : n0v.toNat ≤ σ0.rev.toNat := issuedMap_le _ _ _ σ0.rev.isLt hk
                have hstart : watchStartOk r ns lo σ0 [] n0v := by
                  unfold watchStartOk; rw [if_neg hrv1]; exact ⟨rfl, by rw [hiss, hk]⟩
                wp_if_destruct
                · -- an old version: expired if flagged
                  have hlt := Hif
                  wp_apply wp_chance $$ [$Hsrv] as %b2 %Hb2
                  cases b2
                  · (try wp_auto)
                    ihave Hxs := (BigSepL2.bigSepL2_nil (PROP := IProp GF) (Φ := fun _ x o => objAt (GF := GF) x (DFrac.own 1) o)).2 $$ []
                    · itrivial
                    ihave %Hcsl := ownSlice_len _ _ _ $$ Hsl
                    ihave %Hcsl2 := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Hcs
                    ihave IH : iprop(∃ (n : w64), "next" ∷ next_ptr ↦ n ∗
                        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ (σ0.tbl r).log.length ∧
                          ∀ j (hj : j < sint.nat n) (hj' : j < (σ0.tbl r).log.length),
                            ((σ0.tbl r).log[j]'hj').rv.toNat ≤ n0v.toNat⌝) $$ [next]
                    · iexists W64 0
                      iframe
                      ipureintro
                      exact ⟨by word, by simp, fun j hj _ => absurd hj (by simp)⟩
                    wp_for IH
                    wp_if_destruct
                    · have Hlt : sint.nat n < cs.length := by
                        have := sint_nat_lt_of_lt n sl.len Hif Hn.1; omega
                      have Hlt' : sint.nat n < (σ0.tbl r).log.length := by omega
                      have hsucc := w64_succ_nat n Hn.1 (by have := sint_nat_lt sl.len; omega)
                      obtain ⟨c, hc⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
                      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
                      simp only [Hbnd, _root_.and_self, ↓reduceIte]
                      icases ownSlice_elem_acc (sint.Z n) c sl (DFrac.own 1) cs Hn.1 hc $$ Hsl with ⟨Hc, Hslb⟩
                      icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
                      iStructNamedSuffix Hc "_c"
                      (try wp_auto)
                      ihave Hc := typedPointsto_combine _ c _ Hcnn $$ [typ_c rv_c obj_c]
                      · simp only [TypedPointsto.typedPointstoDef]
                        iframe
                      ihave Hsl := Hslb $$ %c Hc
                      have hset : cs.set (sint.nat n) c = cs := by
                        obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hc
                        rw [← h2]; exact List.set_getElem_self h1
                      rw [show (sint.Z n).toNat = sint.nat n from rfl, hset]
                      icases changes_rv_at cs (σ0.tbl r).log (sint.nat n) c _ hc
                        (List.getElem?_eq_getElem Hlt') $$ Hcs with ⟨Hcs, %hcrv⟩
                      by_cases hle : uint.Z c.rv' ≤ uint.Z n0v
                      · -- at most the start version: on
                        simp only [hle, _root_.decide_true, ↓reduceIte]
                        (try wp_auto)
                        wp_for_post
                        iframe
                        iexists n + W64 1
                        iframe
                        ipureintro
                        refine ⟨hsucc.1, by rw [hsucc.2]; omega, ?_⟩
                        intro j hj hj'
                        rw [hsucc.2] at hj
                        by_cases hjn : j = sint.nat n
                        · subst hjn
                          rw [← hcrv]
                          simp [uint.Z] at hle
                          omega
                        · exact Hn.2.2 j (by omega) hj'
                      · -- after the start version: the loop stops at `n`
                        have hft : (#false : val) ≠ #true := by
                          intro h; have := go.intoVal_inj h; simp at this
                        simp only [hle, _root_.decide_false]
                        rw [decide_eq_false hft]
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        (try wp_auto)
                        (try simp only [decide_True, ↓reduceIte])
                        have hls : logStart (σ0.tbl r).log n0v = sint.nat n := by
                          apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                          intro _
                          rw [← hcrv]
                          simp [uint.Z] at hle
                          omega
                        (try rw [if_pos (show decide True = true from rfl)])
                        (try wp_auto)
                        have hnw : W64 (logStart (σ0.tbl r).log n0v) = n := by
                          rw [hls]; exact w64_of_sint_nat n Hn.1
                        -- the stop channel, and the watcher registered
                        imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                          with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
                        · ileft; iexact Hod
                        iunfold watchersLocked at Hws
                        icases Hws with ⟨%W, Hauth, HWs⟩
                        cases hW : W.lookup «$r0_ptr» with
                        | some c0 =>
                          icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                            with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                          ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                          exact absurd hF id
                        | none =>
                        imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
                        wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                            Hlog Hsl Hcap Hcs]
                        · iunfold lockInv
                          inext
                          iexists σ0, H
                          iframe Hhist
                          isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                          · iunfold srvLocked
                            iframe
                            ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                            · iunfold tableLocked
                              iexists M, sl, cs
                              iframe
                            iframe
                            ipureintro; exact Huidlt
                          isplitr
                          · ipureintro; exact Hok
                          iunfold watchersLocked
                          iexists W.insert «$r0_ptr» (spscCode g)
                          iframe Hauth
                          iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                          iframe HWs
                          iexists g, false
                          iframe
                          isplitl []
                          · ipureintro; rfl
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          iexact Hdprod
                        -- the result channel and the cursor
                        imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log n0v, n0v)] : List Pos'))
                          with ⟨%γcur, Hcur, #Hcurlb⟩
                        imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                            (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj))
                            (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                          with ⟨%gch, #Hspsc, Hprod, Hcons⟩
                        · ileft; iexact Hoc
                        rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) =
                          evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj) from rfl]
                        (try wp_auto)
                        rw [← hnw]
                        ipersist initial_w
                        wp_apply wp_fork $$ [initial_w Hosl0 Hxs next_w sentRV_w Hprod Hdcons Hcur]
                        · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                              (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) $$ [$Hpkg initial_w Hosl0 Hxs next_w
                              sentRV_w Hprod Hdcons Hcur]
                          · unfold runPre
                            iexists s, (L.tbl r).t, slice.nil, ch, dch, g, opts.AllowWatchBookmarks', [], n0v, σ0
                            iframe
                            iframe #
                            ipureintro
                            exact ⟨by rw [Hlo.2.2.2.2], hnle⟩
                          ipureintro; exact isPanic_intoVal _
                        (try wp_auto)
                        iapply HΦ
                        iframe Ho
                        unfold watchRet
                        rw [if_neg hns]
                        iright
                        iright
                        isplitr
                        · ipureintro; rfl
                        iexists ⟨gch, γcur⟩, ([] : List Obj), n0v
                        isplitl []
                        · unfold watchAt
                          iexists «$r0_ptr», ch, dch, s, cfg, g
                          iframe #
                          ipureintro; rfl
                        isplitl [Hcons]
                        · unfold watchCons
                          iexists []
                          iframe
                          isplitr
                          · ipureintro; rfl
                          iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
                        iframe #
                        ipureintro; exact hstart
                    · -- the log's end: the loop stops at `n`
                      (try wp_auto)
                      have hls : logStart (σ0.tbl r).log n0v = sint.nat n := by
                        apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                        intro hk
                        exfalso
                        have := sint_nat_le_of_not_lt n sl.len Hif Hn.1
                        omega
                      (try rw [if_pos (show decide True = true from rfl)])
                      (try wp_auto)
                      have hnw : W64 (logStart (σ0.tbl r).log n0v) = n := by
                        rw [hls]; exact w64_of_sint_nat n Hn.1
                      -- the stop channel, and the watcher registered
                      imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                        with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
                      · ileft; iexact Hod
                      iunfold watchersLocked at Hws
                      icases Hws with ⟨%W, Hauth, HWs⟩
                      cases hW : W.lookup «$r0_ptr» with
                      | some c0 =>
                        icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                          with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                        ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                        exact absurd hF id
                      | none =>
                      imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
                      wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                          Hlog Hsl Hcap Hcs]
                      · iunfold lockInv
                        inext
                        iexists σ0, H
                        iframe Hhist
                        isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                        · iunfold srvLocked
                          iframe
                          ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                          · iunfold tableLocked
                            iexists M, sl, cs
                            iframe
                          iframe
                          ipureintro; exact Huidlt
                        isplitr
                        · ipureintro; exact Hok
                        iunfold watchersLocked
                        iexists W.insert «$r0_ptr» (spscCode g)
                        iframe Hauth
                        iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                        iframe HWs
                        iexists g, false
                        iframe
                        isplitl []
                        · ipureintro; rfl
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        iexact Hdprod
                      -- the result channel and the cursor
                      imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log n0v, n0v)] : List Pos'))
                        with ⟨%γcur, Hcur, #Hcurlb⟩
                      imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                          (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj))
                          (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                        with ⟨%gch, #Hspsc, Hprod, Hcons⟩
                      · ileft; iexact Hoc
                      rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) =
                        evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj) from rfl]
                      (try wp_auto)
                      rw [← hnw]
                      ipersist initial_w
                      wp_apply wp_fork $$ [initial_w Hosl0 Hxs next_w sentRV_w Hprod Hdcons Hcur]
                      · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                            (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) $$ [$Hpkg initial_w Hosl0 Hxs next_w
                            sentRV_w Hprod Hdcons Hcur]
                        · unfold runPre
                          iexists s, (L.tbl r).t, slice.nil, ch, dch, g, opts.AllowWatchBookmarks', [], n0v, σ0
                          iframe
                          iframe #
                          ipureintro
                          exact ⟨by rw [Hlo.2.2.2.2], hnle⟩
                        ipureintro; exact isPanic_intoVal _
                      (try wp_auto)
                      iapply HΦ
                      iframe Ho
                      unfold watchRet
                      rw [if_neg hns]
                      iright
                      iright
                      isplitr
                      · ipureintro; rfl
                      iexists ⟨gch, γcur⟩, ([] : List Obj), n0v
                      isplitl []
                      · unfold watchAt
                        iexists «$r0_ptr», ch, dch, s, cfg, g
                        iframe #
                        ipureintro; rfl
                      isplitl [Hcons]
                      · unfold watchCons
                        iexists []
                        iframe
                        isplitr
                        · ipureintro; rfl
                        iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
                      iframe #
                      ipureintro; exact hstart
                  · (try wp_auto)
                    wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                    · iunfold lockInv
                      iexists σ0, H
                      iframe
                      iunfold srvLocked
                      iframe
                      ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                      · iunfold tableLocked
                        iexists M, sl, cs
                        iframe
                      iframe
                      ipureintro; exact ⟨Huidlt, Hok⟩
                    (try wp_auto)
                    wp_apply +noauto wp_NewResourceExpired as %p ⟨%st, Hp, %Hst⟩
                    ipersist Hp
                    (try wp_auto)
                    iapply HΦ
                    iframe Ho
                    unfold watchRet
                    rw [if_neg hns]
                    iright
                    ileft
                    isplitr
                    · ipureintro
                      exact ⟨rfl, hrvne.1, hrvne.2, Or.inr ⟨n0v, by rw [hiss, hk], by simp [uint.Z] at hlt; omega, Hb2 rfl⟩⟩
                    unfold errIs
                    iexists p, st
                    iframe #
                    ipureintro
                    exact ⟨rfl, Hst.2.1, Hst.2.2⟩
                · (try wp_auto)
                  ihave Hxs := (BigSepL2.bigSepL2_nil (PROP := IProp GF) (Φ := fun _ x o => objAt (GF := GF) x (DFrac.own 1) o)).2 $$ []
                  · itrivial
                  ihave %Hcsl := ownSlice_len _ _ _ $$ Hsl
                  ihave %Hcsl2 := (BigSepL2.bigSepL2_length (PROP := IProp GF)) $$ Hcs
                  ihave IH : iprop(∃ (n : w64), "next" ∷ next_ptr ↦ n ∗
                      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ (σ0.tbl r).log.length ∧
                        ∀ j (hj : j < sint.nat n) (hj' : j < (σ0.tbl r).log.length),
                          ((σ0.tbl r).log[j]'hj').rv.toNat ≤ n0v.toNat⌝) $$ [next]
                  · iexists W64 0
                    iframe
                    ipureintro
                    exact ⟨by word, by simp, fun j hj _ => absurd hj (by simp)⟩
                  wp_for IH
                  wp_if_destruct
                  · have Hlt : sint.nat n < cs.length := by
                      have := sint_nat_lt_of_lt n sl.len Hif Hn.1; omega
                    have Hlt' : sint.nat n < (σ0.tbl r).log.length := by omega
                    have hsucc := w64_succ_nat n Hn.1 (by have := sint_nat_lt sl.len; omega)
                    obtain ⟨c, hc⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
                    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
                    simp only [Hbnd, _root_.and_self, ↓reduceIte]
                    icases ownSlice_elem_acc (sint.Z n) c sl (DFrac.own 1) cs Hn.1 hc $$ Hsl with ⟨Hc, Hslb⟩
                    icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcnn⟩
                    iStructNamedSuffix Hc "_c"
                    (try wp_auto)
                    ihave Hc := typedPointsto_combine _ c _ Hcnn $$ [typ_c rv_c obj_c]
                    · simp only [TypedPointsto.typedPointstoDef]
                      iframe
                    ihave Hsl := Hslb $$ %c Hc
                    have hset : cs.set (sint.nat n) c = cs := by
                      obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hc
                      rw [← h2]; exact List.set_getElem_self h1
                    rw [show (sint.Z n).toNat = sint.nat n from rfl, hset]
                    icases changes_rv_at cs (σ0.tbl r).log (sint.nat n) c _ hc
                      (List.getElem?_eq_getElem Hlt') $$ Hcs with ⟨Hcs, %hcrv⟩
                    by_cases hle : uint.Z c.rv' ≤ uint.Z n0v
                    · -- at most the start version: on
                      simp only [hle, _root_.decide_true, ↓reduceIte]
                      (try wp_auto)
                      wp_for_post
                      iframe
                      iexists n + W64 1
                      iframe
                      ipureintro
                      refine ⟨hsucc.1, by rw [hsucc.2]; omega, ?_⟩
                      intro j hj hj'
                      rw [hsucc.2] at hj
                      by_cases hjn : j = sint.nat n
                      · subst hjn
                        rw [← hcrv]
                        simp [uint.Z] at hle
                        omega
                      · exact Hn.2.2 j (by omega) hj'
                    · -- after the start version: the loop stops at `n`
                      have hft : (#false : val) ≠ #true := by
                        intro h; have := go.intoVal_inj h; simp at this
                      simp only [hle, _root_.decide_false]
                      rw [decide_eq_false hft]
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      (try wp_auto)
                      (try simp only [decide_True, ↓reduceIte])
                      have hls : logStart (σ0.tbl r).log n0v = sint.nat n := by
                        apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                        intro _
                        rw [← hcrv]
                        simp [uint.Z] at hle
                        omega
                      (try rw [if_pos (show decide True = true from rfl)])
                      (try wp_auto)
                      have hnw : W64 (logStart (σ0.tbl r).log n0v) = n := by
                        rw [hls]; exact w64_of_sint_nat n Hn.1
                      -- the stop channel, and the watcher registered
                      imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                        with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
                      · ileft; iexact Hod
                      iunfold watchersLocked at Hws
                      icases Hws with ⟨%W, Hauth, HWs⟩
                      cases hW : W.lookup «$r0_ptr» with
                      | some c0 =>
                        icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                          with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                        ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                        exact absurd hF id
                      | none =>
                      imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
                      wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                          Hlog Hsl Hcap Hcs]
                      · iunfold lockInv
                        inext
                        iexists σ0, H
                        iframe Hhist
                        isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                        · iunfold srvLocked
                          iframe
                          ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                          · iunfold tableLocked
                            iexists M, sl, cs
                            iframe
                          iframe
                          ipureintro; exact Huidlt
                        isplitr
                        · ipureintro; exact Hok
                        iunfold watchersLocked
                        iexists W.insert «$r0_ptr» (spscCode g)
                        iframe Hauth
                        iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                        iframe HWs
                        iexists g, false
                        iframe
                        isplitl []
                        · ipureintro; rfl
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        iexact Hdprod
                      -- the result channel and the cursor
                      imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log n0v, n0v)] : List Pos'))
                        with ⟨%γcur, Hcur, #Hcurlb⟩
                      imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                          (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj))
                          (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                        with ⟨%gch, #Hspsc, Hprod, Hcons⟩
                      · ileft; iexact Hoc
                      rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) =
                        evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj) from rfl]
                      (try wp_auto)
                      rw [← hnw]
                      ipersist initial_w
                      wp_apply wp_fork $$ [initial_w Hosl0 Hxs next_w sentRV_w Hprod Hdcons Hcur]
                      · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                            (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) $$ [$Hpkg initial_w Hosl0 Hxs next_w
                            sentRV_w Hprod Hdcons Hcur]
                        · unfold runPre
                          iexists s, (L.tbl r).t, slice.nil, ch, dch, g, opts.AllowWatchBookmarks', [], n0v, σ0
                          iframe
                          iframe #
                          ipureintro
                          exact ⟨by rw [Hlo.2.2.2.2], hnle⟩
                        ipureintro; exact isPanic_intoVal _
                      (try wp_auto)
                      iapply HΦ
                      iframe Ho
                      unfold watchRet
                      rw [if_neg hns]
                      iright
                      iright
                      isplitr
                      · ipureintro; rfl
                      iexists ⟨gch, γcur⟩, ([] : List Obj), n0v
                      isplitl []
                      · unfold watchAt
                        iexists «$r0_ptr», ch, dch, s, cfg, g
                        iframe #
                        ipureintro; rfl
                      isplitl [Hcons]
                      · unfold watchCons
                        iexists []
                        iframe
                        isplitr
                        · ipureintro; rfl
                        iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
                      iframe #
                      ipureintro; exact hstart
                  · -- the log's end: the loop stops at `n`
                    (try wp_auto)
                    have hls : logStart (σ0.tbl r).log n0v = sint.nat n := by
                      apply logStart_eq _ _ _ Hn.2.1 (fun j hj => Hn.2.2 j hj _)
                      intro hk
                      exfalso
                      have := sint_nat_le_of_not_lt n sl.len Hif Hn.1
                      omega
                    (try rw [if_pos (show decide True = true from rfl)])
                    (try wp_auto)
                    have hnw : W64 (logStart (σ0.tbl r).log n0v) = n := by
                      rw [hls]; exact w64_of_sint_nat n Hn.1
                    -- the stop channel, and the watcher registered
                    imod (start_spsc (V := Unit) dch (fun _ _ => iprop(False)) (fun _ => iprop(True)) γd) $$ Hdch [Hod]
                      with ⟨%g, #Hdspsc, Hdprod, Hdcons⟩
                    · ileft; iexact Hod
                    iunfold watchersLocked at Hws
                    icases Hws with ⟨%W, Hauth, HWs⟩
                    cases hW : W.lookup «$r0_ptr» with
                    | some c0 =>
                      icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = some c0 from hW)) $$ HWs
                        with ⟨⟨%g', %b', -, Hst2, -⟩, -⟩
                      ihave %hF := bool_pointsto_excl _ _ _ $$ [$stopped_w $Hst2]
                      exact absurd hF id
                    | none =>
                    imod (ghost_map_insert_persist «$r0_ptr» (spscCode g) hW) $$ Hauth with ⟨Hauth, #Hreg⟩
                    wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hauth HWs stopped_w Hdprod Hrev Huids Hrvsm Hrc Hback HM Hrel
                        Hlog Hsl Hcap Hcs]
                    · iunfold lockInv
                      inext
                      iexists σ0, H
                      iframe Hhist
                      isplitl [Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
                      · iunfold srvLocked
                        iframe
                        ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
                        · iunfold tableLocked
                          iexists M, sl, cs
                          iframe
                        iframe
                        ipureintro; exact Huidlt
                      isplitr
                      · ipureintro; exact Hok
                      iunfold watchersLocked
                      iexists W.insert «$r0_ptr» (spscCode g)
                      iframe Hauth
                      iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (show Iris.Std.PartialMap.get? W «$r0_ptr» = none from hW)).2
                      iframe HWs
                      iexists g, false
                      iframe
                      isplitl []
                      · ipureintro; rfl
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      iexact Hdprod
                    -- the result channel and the cursor
                    imod (mono_list_own_alloc (GF := GF) ([(logStart (σ0.tbl r).log n0v, n0v)] : List Pos'))
                      with ⟨%γcur, Hcur, #Hcurlb⟩
                    imod (start_spsc (V := k8s_io.apimachinery.pkg.watch.Event) ch
                        (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj))
                        (fun _ => iprop(True)) γc) $$ Hch [Hoc]
                      with ⟨%gch, #Hspsc, Hprod, Hcons⟩
                    · ileft; iexact Hoc
                    rw [show (evOk γ ⟨g, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) =
                      evOk γ ⟨gch, γcur⟩ r ns (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj) from rfl]
                    (try wp_auto)
                    rw [← hnw]
                    ipersist initial_w
                    wp_apply wp_fork $$ [initial_w Hosl0 Hxs next_w sentRV_w Hprod Hdcons Hcur]
                    · wp_apply (wp_run «$r0_ptr» γ ⟨gch, γcur⟩ cfg r ns admin
                          (lo.AllowWatchBookmarks' && cfg.Bookmarks' && !admin) ([] : List Obj)) $$ [$Hpkg initial_w Hosl0 Hxs next_w
                          sentRV_w Hprod Hdcons Hcur]
                      · unfold runPre
                        iexists s, (L.tbl r).t, slice.nil, ch, dch, g, opts.AllowWatchBookmarks', [], n0v, σ0
                        iframe
                        iframe #
                        ipureintro
                        exact ⟨by rw [Hlo.2.2.2.2], hnle⟩
                      ipureintro; exact isPanic_intoVal _
                    (try wp_auto)
                    iapply HΦ
                    iframe Ho
                    unfold watchRet
                    rw [if_neg hns]
                    iright
                    iright
                    isplitr
                    · ipureintro; rfl
                    iexists ⟨gch, γcur⟩, ([] : List Obj), n0v
                    isplitl []
                    · unfold watchAt
                      iexists «$r0_ptr», ch, dch, s, cfg, g
                      iframe #
                      ipureintro; rfl
                    isplitl [Hcons]
                    · unfold watchCons
                      iexists []
                      iframe
                      isplitr
                      · ipureintro; rfl
                      iapply (monoListIdxOwn_get 0 _ rfl) $$ Hcurlb
                    iframe #
                    ipureintro; exact hstart
        · -- a flagged failure
          imod (au_read_any γ (fun σ => iprop(∀ w err, kd.meta.ListOptions.own opts dq lo ∗
            watchRet γ cfg admin r ns lo σ w err -∗ Φ (PairV #w #err)))) $$ HΦ with ⟨%σ, HΦ⟩
          (try wp_auto)
          wp_apply +noauto wp_NewInternalError as %p ⟨%st, Hp, %Hst⟩
          ipersist Hp
          (try wp_auto)
          iapply HΦ
          iframe
          unfold watchRet
          rw [if_neg hns]
          ileft
          isplitr
          · ipureintro; exact ⟨Hb rfl, rfl⟩
          unfold errIs
          iexists p, st
          iframe #
          ipureintro
          exact ⟨rfl, Hst.2.1, Hst.2.2⟩
    · -- a field selector
      wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
      ipersist Hp
      imod (au_read_any γ (fun σ => iprop(∀ w err, kd.meta.ListOptions.own opts dq lo ∗ watchRet γ cfg admin r ns lo σ w err -∗ Φ (PairV #w #err)))) $$ HΦ with ⟨%σ, HΦ⟩
      (try wp_auto)
      iapply HΦ
      iframe
      unfold watchRet
      rw [if_pos (by right; left; rw [← Hlo.2.1]; exact Hif)]
      isplitr
      · ipureintro; rfl
      unfold errIs
      iexists p, st
      iframe #
      ipureintro
      exact ⟨rfl, Hst.2.1, Hst.2.2⟩
  · -- a label selector
    wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
    ipersist Hp
    imod (au_read_any γ (fun σ => iprop(∀ w err, kd.meta.ListOptions.own opts dq lo ∗ watchRet γ cfg admin r ns lo σ w err -∗ Φ (PairV #w #err)))) $$ HΦ with ⟨%σ, HΦ⟩
    (try wp_auto)
    iapply HΦ
    iframe
    unfold watchRet
    rw [if_pos (by left; rw [← Hlo.1]; exact Hif)]
    isplitr
    · ipureintro; rfl
    unfold errIs
    iexists p, st
    iframe #
    ipureintro
    exact ⟨rfl, Hst.2.1, Hst.2.2⟩

end proof

end apimodel
end EtcdGrove
end Perennial
