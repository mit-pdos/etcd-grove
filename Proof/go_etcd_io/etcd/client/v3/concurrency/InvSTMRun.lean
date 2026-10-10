/-
Lemmas for the proofs of `mkSTM`, `runSTM` and `NewSTM`
(`Proof/go_etcd_io/etcd/client/v3/concurrency/{mkSTM,runSTM,NewSTM}.lean`): the STM's methods
(`stmMethods`) from its implementations' specs. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Put
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Del
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__commit
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__reset
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__commit
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem readOptsOk_of_getOptsOk (lvl : w64) (gs : List (OpFull → OpFull)) (h : GetOptsOk lvl gs) :
    ReadOptsOk gs := by
  unfold GetOptsOk at h
  unfold ReadOptsOk
  split at h
  · rcases h with h | ⟨S, h⟩
    · exact .inl h
    · exact .inr (.inr ⟨S, h⟩)
  · exact .inr (.inl h)

theorem preOk_insert_write (st : STMSt) (pre : GMap GoString ReadM) (k : GoString) (w : WriteM)
    (h : PreOk st pre) : PreOk { st with writes := GMap.insert k w st.writes } pre := by
  intro k' h1 h2
  have := h k' h1 h2
  simp only [GMap.lookup_insert_eq_iff]
  split <;> simp_all

theorem preOk_empty (pre : GMap GoString ReadM) : PreOk STMSt.empty pre := by
  intro k h1
  simp [STMSt.empty] at h1

/-- **The methods of a `*stm`** (`RepeatableReads`, `ReadCommitted`). -/
theorem stmMethods_stm
    (hGet : stm.Get.spec (GF := GF) (hG := hG))
    (hPut : stm.Put.spec (GF := GF) (hG := hG))
    (hRev : stm.Rev.spec (GF := GF) (hG := hG))
    (hDel : stm.Del.spec (GF := GF) (hG := hG))
    (hCommit : stm.commit.spec (GF := GF) (hG := hG))
    (hReset : stm.reset.spec (GF := GF) (hG := hG))
    (lvl : w64) (pfx : GoString) (p : Loc) (hlvl : isoSer lvl = false) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ⊢
      stmMethods lvl pfx p := by
  have hb : stmBase lvl p = p := by simp [stmBase, hlvl]
  have hi : stmIface lvl p = interface.mk (go.GoType.PointerType stm.ty) #p := by
    simp [stmIface, hlvl]
  iintro #Hpkg
  unfold stmMethods stmState stmStale
  simp only [hb, hi, hlvl, Bool.false_eq_true, ↓reduceIte]
  isplitr
  · imodintro
    iintro %st %sl %ks
    wp_start_folded as ⟨⟨#Henv, Hr, Hw, ⟨%gs, Ho, %Hgs⟩, #Hcf, -⟩, #Hks, %Hk⟩
    wp_apply hGet p pfx st gs sl ks $$ [$Hpkg $Henv $Hr $Hw $Ho $Hks] as %v ⟨%reads', Hr, Hw, Ho, %Hpost⟩
    · ipureintro; exact ⟨readOptsOk_of_getOptsOk lvl gs Hgs, Hk⟩
    iapply HΦ
    iexists { reads := reads', writes := st.writes }
    iframe
    iframe #
    isplitl <;> ipureintro
    · exact Hgs
    · exact Hpost
  isplitr
  · imodintro
    iintro %st %k %v %sl %gs
    wp_start_folded as ⟨⟨#Henv, Hr, Hw, Ho, #Hcf, -⟩, #Hsl, %Hk⟩
    wp_apply hPut p pfx st.writes k v sl gs $$ [$Hpkg $Hw $Hsl] as Hw
    · ipureintro; exact Hk
    iapply HΦ
    iframe
    iframe #
  isplitr
  · imodintro
    iintro %st %k
    wp_start_folded as ⟨⟨#Henv, Hr, Hw, ⟨%gs, Ho, %Hgs⟩, #Hcf, -⟩, %Hk⟩
    wp_apply hRev p pfx st.reads gs k $$ [$Hpkg $Henv $Hr $Ho] as %r ⟨%reads', Hr, Ho, %Hpost⟩
    · ipureintro; exact ⟨readOptsOk_of_getOptsOk lvl gs Hgs, Hk⟩
    iapply HΦ
    iexists { reads := reads', writes := st.writes }
    iframe
    iframe #
    isplitl <;> ipureintro
    · exact Hgs
    · exact ⟨rfl, Hpost⟩
  isplitr
  · imodintro
    iintro %st %k
    wp_start_folded as ⟨⟨#Henv, Hr, Hw, Ho, #Hcf, -⟩, %Hk⟩
    wp_apply hDel p pfx st.writes k $$ [$Hpkg $Hw] as Hw
    · ipureintro; exact Hk
    iapply HΦ
    iframe
    iframe #
  isplitr
  · imodintro
    iintro %st %lo
    wp_start_folded as ⟨⟨#Henv, Hr, Hw, Ho, #Hcf, -⟩, #Hlo⟩
    wp_apply hCommit lvl p pfx st lo $$ [$Hpkg $Henv $Hr $Hw $Hcf $Hlo] as %resp ⟨Hr, Hw, Hres⟩
    unfold stmRsetOwn stmWsetOwn
    icases Hr with ⟨%m1, %rm, Hr, -⟩
    icases Hw with ⟨%m2, %wm, Hw, -⟩
    iapply HΦ
    iframe
    iframe #
  · imodintro
    wp_start_folded as ⟨#Henv, Hr, Hw, Ho, #Hcf, -⟩
    wp_apply hReset p pfx $$ [$Hpkg $Hr $Hw] as ⟨Hr, Hw⟩
    iapply HΦ
    iframe
    iframe #

/-- **The methods of a `*stmSerializable`** (the serializable levels): `Get`, `Rev`, `commit` its
own, `Put`, `Del`, `reset` the embedded `stm`'s (promoted). -/
theorem stmMethods_ser
    (hPut : stm.Put.spec (GF := GF) (hG := hG))
    (hDel : stm.Del.spec (GF := GF) (hG := hG))
    (hReset : stm.reset.spec (GF := GF) (hG := hG))
    (hSGet : stmSerializable.Get.spec (GF := GF) (hG := hG))
    (hSRev : stmSerializable.Rev.spec (GF := GF) (hG := hG))
    (hSCommit : stmSerializable.commit.spec (GF := GF) (hG := hG))
    (lvl : w64) (pfx : GoString) (p : Loc) (hlvl : isoSer lvl = true) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ⊢
      stmMethods lvl pfx p := by
  have hb : stmBase lvl p = structFieldRef stmSerializable go!"stm" p := by simp [stmBase, hlvl]
  have hi : stmIface lvl p = interface.mk (go.GoType.PointerType stmSerializable.ty) #p := by
    simp [stmIface, hlvl]
  iintro #Hpkg
  unfold stmMethods
  simp only [hi]
  isplitr
  · imodintro
    iintro %st %sl %ks
    wp_start_folded as ⟨Hst, #Hks, %Hk⟩
    wp_apply hSGet lvl p pfx st sl ks $$ [$Hpkg $Hst $Hks] as %v Hres
    · ipureintro; exact ⟨hlvl, Hk⟩
    iapply HΦ; iexact Hres
  isplitr
  · imodintro
    iintro %st %k %v %sl %gs
    wp_start_folded as ⟨Hst, #Hsl, %Hk⟩
    unfold stmState
    simp only [hb, hlvl, ↓reduceIte]
    icases Hst with ⟨#Henv, Hr, Hw, Ho, #Hcf, Hpre⟩
    wp_method_call
    wp_call
    icases Ho with ⟨%gs', Ho, %Hgs'⟩
    icases Hpre with ⟨%pre, Hpre, %Hpok⟩
    wp_apply hPut (structFieldRef stmSerializable go!"stm" p) pfx st.writes k v sl gs
      $$ [$Hpkg $Hw $Hsl] as Hw
    · ipureintro; exact Hk
    iapply HΦ
    iframe
    iframe #
    isplitl <;> ipureintro
    · exact Hgs'
    · exact preOk_insert_write st pre k _ Hpok
  isplitr
  · imodintro
    iintro %st %k
    wp_start_folded as ⟨Hst, %Hk⟩
    wp_apply hSRev lvl p pfx st k $$ [$Hpkg $Hst] as %r Hres
    · ipureintro; exact ⟨hlvl, Hk⟩
    iapply HΦ; iexact Hres
  isplitr
  · imodintro
    iintro %st %k
    wp_start_folded as ⟨Hst, %Hk⟩
    unfold stmState
    simp only [hb, hlvl, ↓reduceIte]
    icases Hst with ⟨#Henv, Hr, Hw, Ho, #Hcf, Hpre⟩
    wp_method_call
    wp_call
    icases Ho with ⟨%gs', Ho, %Hgs'⟩
    icases Hpre with ⟨%pre, Hpre, %Hpok⟩
    wp_apply hDel (structFieldRef stmSerializable go!"stm" p) pfx st.writes k $$ [$Hpkg $Hw] as Hw
    · ipureintro; exact Hk
    iapply HΦ
    iframe
    iframe #
    isplitl <;> ipureintro
    · exact Hgs'
    · exact preOk_insert_write st pre k _ Hpok
  isplitr
  · imodintro
    iintro %st %lo
    wp_start_folded as ⟨Hst, #Hlo⟩
    wp_apply hSCommit lvl p pfx st lo $$ [$Hpkg $Hst $Hlo] as %resp Hres
    · ipureintro; exact hlvl
    iapply HΦ; iexact Hres
  · imodintro
    wp_start_folded as Hst
    unfold stmState stmStale
    simp only [hb, hlvl, ↓reduceIte]
    icases Hst with ⟨#Henv, Hr, Hw, Ho, #Hcf, Hpre⟩
    wp_method_call
    wp_call
    icases Ho with ⟨%gs', Ho, %Hgs'⟩
    icases Hpre with ⟨%pre, Hpre⟩
    wp_apply hReset (structFieldRef stmSerializable go!"stm" p) pfx $$ [$Hpkg $Hr $Hw] as ⟨Hr, Hw⟩
    iapply HΦ
    iframe
    iframe #
    isplitl <;> ipureintro
    · exact Hgs'
    · exact preOk_empty pre

/-- `append(sl1, sl2...)` of two comparison slices (the first one's capacity owned). -/
theorem wp_cmps_append (sl1 sl2 : GoSlice) (ms1 ms2 : List CmpModel) :
    {{ cmpsAt (GF := GF) sl1 ms1 ∗ ownSliceCap go_etcd_io.etcd.client.v3.Cmp sl1 (DFrac.own 1) ∗
        cmpsAt sl2 ms2 }}
      (App (App (Val #(functions go.append
        [go.GoType.SliceType go_etcd_io.etcd.client.v3.Cmp.ty])) (Val #sl1)) (Val #sl2))
    {{ (s : GoSlice), RET #s; cmpsAt s (ms1 ++ ms2) }} := by
  iintro %Φ ⟨H1, Hcap, H2⟩ HΦ
  unfold cmpsAt
  icases H1 with ⟨%cs1, #Hs1, %Hl1, #Hc1⟩
  icases H2 with ⟨%cs2, #Hs2, %Hl2, #Hc2⟩
  wp_apply wp_slice_append_persistent sl1 cs1 sl2 cs2 DFrac.discard $$ [$Hs1 $Hcap $Hs2]
    as %s ⟨#Hs, -, -⟩
  iapply HΦ
  iexists cs1 ++ cs2
  iframe #
  isplitr
  · ipureintro; simp [Hl1, Hl2]
  imodintro
  iintro %i %c %m %Hci %Hmi
  by_cases hi : i < cs1.length
  · rw [List.getElem?_append_left hi] at Hci
    rw [List.getElem?_append_left (by omega)] at Hmi
    iapply Hc1 $$ %i %c %m %Hci %Hmi
  · rw [List.getElem?_append_right (by omega)] at Hci
    rw [List.getElem?_append_right (by omega), ← Hl1] at Hmi
    iapply Hc2 $$ %(i - cs1.length) %c %m %Hci %Hmi

theorem readsAt_empty (pfx : GoString) : ⊢ readsAt (GF := GF) pfx ∅ ∅ := by
  unfold readsAt
  isplitr
  · ipureintro; intro k; rfl
  imodintro
  iintro %k %p %e %Hp %He
  simp at Hp

/-- **A new `*stmSerializable`** (`mkSTM`'s serializable branches): stale, with no get options and
an empty prefetch map. -/
theorem stmStale_ser_init (lvl : w64) (hlvl : isoSer lvl = true) (pfx : GoString) (p c : Loc)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (rs ws pm : Loc) :
    isEtcdSTMClient c pfx ∗ context.isContext ctx cs ∗
      structFieldRef stm go!"client" (structFieldRef stmSerializable go!"stm" p) ↦□ c ∗
      structFieldRef stm go!"ctx" (structFieldRef stmSerializable go!"stm" p) ↦□
        GoInterface.ok ctx ∗
      structFieldRef stm go!"rset" (structFieldRef stmSerializable go!"stm" p) ↦ rs ∗
      structFieldRef stm go!"wset" (structFieldRef stmSerializable go!"stm" p) ↦ ws ∗
      structFieldRef stm go!"getOpts" (structFieldRef stmSerializable go!"stm" p) ↦ slice.nil ∗
      stmConflictsAt lvl pfx (structFieldRef stmSerializable go!"stm" p) ∗
      structFieldRef stmSerializable go!"prefetch" p ↦ pm ∗ pm ↦$ (∅ : GMap GoString Loc) ⊢
    stmStale lvl pfx p := by
  have hb : stmBase lvl p = structFieldRef stmSerializable go!"stm" p := by simp [stmBase, hlvl]
  unfold stmStale stmEnv stmOptsOwn stmPreOwn
  simp only [hb, hlvl, ↓reduceIte]
  iintro ⟨#Hcl, #Hctx, #Hc, #Hx, Hr, Hw, Ho, #Hcf, Hpf, Hpm⟩
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Hre := readsAt_empty (GF := GF) pfx
  iframe
  iframe #
  ipureintro
  simp [GetOptsOk, hlvl]

/-- **A new `*stm`** (`mkSTM`'s other branches): stale, with the get options
`[WithSerializable()]`. -/
theorem stmStale_stm_init (lvl : w64) (hlvl : isoSer lvl = false) (pfx : GoString) (p c : Loc)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (rs ws : Loc) (sl : GoSlice) :
    isEtcdSTMClient c pfx ∗ context.isContext ctx cs ∗
      structFieldRef stm go!"client" p ↦□ c ∗
      structFieldRef stm go!"ctx" p ↦□ GoInterface.ok ctx ∗
      structFieldRef stm go!"rset" p ↦ rs ∗
      structFieldRef stm go!"wset" p ↦ ws ∗
      structFieldRef stm go!"getOpts" p ↦ sl ∗ optsAt sl [withSerializableM] ∗
      stmConflictsAt lvl pfx p ⊢
    stmStale lvl pfx p := by
  have hb : stmBase lvl p = p := by simp [stmBase, hlvl]
  unfold stmStale stmEnv stmOptsOwn
  simp only [hb, hlvl, Bool.false_eq_true, ↓reduceIte]
  iintro ⟨#Hcl, #Hctx, #Hc, #Hx, Hr, Hw, Ho, #Hopts, #Hcf⟩
  iframe
  iframe #
  ipureintro
  simp [GetOptsOk, hlvl]

/-- No comparisons: the nil slice. -/
theorem cmpsAt_nil : ⊢ cmpsAt (GF := GF) slice.nil [] := by
  unfold cmpsAt
  iexists ([] : List go_etcd_io.etcd.client.v3.Cmp)
  isplitl
  · iapply ownSlice_nil
  isplitl
  · ipureintro; rfl
  imodintro
  iintro %i %c %m %Hc %Hm
  simp at Hc

end proof

end concurrency
end EtcdGrove
end Perennial
