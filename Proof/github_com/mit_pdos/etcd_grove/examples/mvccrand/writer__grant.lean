/- Lean-first (no Rocq counterpart). The proof of `writer.grant`: `nextID + 1` is not live and not
`0` (`writerLe`'s bound on the live ids), so `Grant` takes its second arm (`err == nil`), the hook's
triple (`hookOk`) its critical-section contract; the store is not stepped, so `Rev()` (`KV.Rev`, at
the invariant's state, the writer's half of `γ.σ`) is the published revision (`cur`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__grant
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__cur
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.grant.wp_proof (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_cur : writer.cur.spec (GF := GF) (hG := hG))
    (wp_checkHook : writer.checkHook.spec (GF := GF) (hG := hG))
    (wp_Grant : lease.lessor.Grant.spec (GF := GF) (hG := hG)) :
    writer.grant.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L n k T R i s hk hn
  haveI := fun kv γ => hpers.1 kv γ
  wp_start as ⟨Hctx, Hown, Hle, Hpre⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmpkg, #Htpkg, #Hw, #Hinv, #Hhist, #Hkv, #Hhook, Hhok⟩
  iunfold hookOk at Hhok
  icases Hhok with #Hhok
  iunfold writerOwn at Hown
  icases Hown with ⟨Hrdr, Hbk, Hrd, Hidle, Hg, ⟨%Lm, Hlm, %HLm⟩, Hlo⟩
  iunfold writerLe at Hle
  icases Hle with ⟨%lp, %rd, %r, %U, #Hro, Hlrd, Hrvk, Hever, HR, HT, Hrdo, Hdel, Hbe, Hrb, %HlP,
    Hnext, %Hn⟩
  iunfold writerLeRO at Hro
  icases Hro with ⟨%Hle, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #Hlbe⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  wp_auto
  rw [Hle]
  simp only
  -- one write token
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ HT with ⟨HT1, HT⟩
  ihave #Hgr := leaseGranted_of_guard (mvccLeases γ.kv) (n + W64 1) $$ Hguard
  have hid0 : n + W64 1 ≠ W64 0 := by intro h; have := congrArg sint.Z h; word
  have hnin : n + W64 1 ∉ L := by
    intro h; have := (Hn.2.1 _ h).2; word
  have hninU : n + W64 1 ∉ U := by
    intro h; have := Hn.2.2 _ h; word
  wp_apply (wp_Grant lp (mvccLeases γ.kv) (n + W64 1) (W64 3600) L (pendItems σ.log [])
    iprop(True) f T (lease.lessorBeOn lp B.be) R (backend.rbPart B.γB (· = leaseName)) r
    (hookPre wv i s) iprop(True ∗ hookPost wv i) (hookPost wv i) U)
    $$ [Hlo Hrvk HT1 Hbe HR Hrb Hpre Hever]
    as %l %err ⟨HR, Hbe, Hres⟩
  · iframe Hlinv Hlcfg Hlbe Hlo Hrvk HT1 Hbe HR Hrb Hgr Hever
    isplitl [Hpre]
    · iunfold srvApi.csContractA
      iframe Hpre
      isplitl
      · iapply Hhok
      iintro HQ
      imodintro
      iexact HQ
    iright; ipureintro; exact hninU
  icases Hres with (⟨%Hbad, -⟩ | ⟨%Hok, Hlo, Hrvk, Hpost, -, -, Hmt⟩)
  · exfalso
    rcases Hbad.2 with h | h | h
    · exact hid0 h
    · have : sint.Z (W64 3600) = 3600 := by word
      omega
    · exact hnin h
  obtain ⟨rfl, -, -, -, -⟩ := Hok
  icases Hmt with ⟨%mt, -, -, Hrb, Hever, -⟩
  wp_auto
  wp_apply wp_check
  · ipureintro; rfl
  (try wp_auto)
  iunfold hookPost at Hpost
  icases Hpost with ⟨Happ, Hsav⟩
  wp_apply wp_checkHook w wv i $$ [$Hsav $Hw] as Hsav
  (try wp_auto)
  wp_apply (wp_mapInsert go.int64 wv.leases' Lm (n + W64 1) true) $$ [$Hlm] as Hlm
  (try wp_auto)
  -- the store's revision: unchanged
  ihave %Hsh := hsh.1 wv.kv' γ.kv $$ Hkv
  obtain ⟨ty, v, Hkveq, hkv⟩ := Hsh
  ihave #Hkv2 : isMvcc (interface.mkOk ty v) γ.kv $$ []
  · rw [← Hkveq]; iexact Hkv
  rw [Hkveq]
  simp only
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) wv.h' γ) := by unfold worldInv; infer_instance
  have hdisj : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN :=
    nclose_subseteq' "world" (mask_ndot_ne' nroot "mvccrand" "mvcc" (by decide))
  wp_apply (hkv.2.2.1 γ.kv (fun σ1 => iprop(⌜σ1 = σ⌝ ∗ ghostVar γ.σ (1 : Qp).half σ))) $$
    [Hrdr Hgσ] as %rv ⟨Hrdr, %σ1, ⟨%Heq1, Hgσ⟩, %Hrv⟩
  · iframe Hkv2 Hrdr
    iauintro
    unfold atomic_acc
    iinv Hinv with >Hi Hclose
    iunfold worldInv at Hi
    icases Hi with ⟨%σ2, %S, %p, %Hl, %W, Hs, Hgσ2, HS, Hreg, Hpub, Hpv2, Hpm, Hlb0, %Hok⟩
    ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ2 Hgσ
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ2
    iframe Hs
    isplit
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hgσ2 HS Hreg Hpub Hpv2 Hpm Hlb0] with -
      · inext; iunfold worldInv; iexists σ2, S, p, Hl, W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hgσ
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hgσ2 HS Hreg Hpub Hpv2 Hpm Hlb0] with -
      · inext; iunfold worldInv; iexists σ2, S, p, Hl, W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hgσ
      ipureintro; exact Hag
  subst Heq1
  subst Hrv
  wp_apply wp_cur w wv γ (W64 (σ1.rev : Int)) $$ [$Hw $Hinv $Hpv] as Hpv
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  iapply HΦ
  isplitl [Hrdr Hbk Hrd Hg Hlo Hlm Hgσ HW Hpv]
  · iunfold writerOwn
    iframe Hrdr Hbk Hrd Hg Hlo
    isplitl [Hgσ HW Hpv]
    · iunfold writerIdle; iframe; ipureintro; exact Hid
    iexists (<[n + W64 1 := true]> Lm)
    iframe Hlm
    ipureintro
    intro id
    by_cases h : id = n + W64 1
    · subst h; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), HLm id, List.mem_append, List.mem_singleton]
      exact ⟨Or.inl, fun h' => h'.resolve_right h⟩
  isplitr [Happ Hsav]
  · iunfold writerLe
    iexists lp, rd, _, U ++ [n + W64 1]
    iframe
    isplitr
    · iunfold writerLeRO; iframe #; ipureintro; exact Hle
    isplitr
    · ipureintro; exact HlP
    ipureintro
    refine ⟨by word, fun id hid => ?_, fun id hid => ?_⟩
    · rcases List.mem_append.1 hid with h | h
      · have := Hn.2.1 id h; constructor <;> word
      · rw [List.mem_singleton.1 h]; constructor <;> word
    · rcases List.mem_append.1 hid with h | h
      · have := Hn.2.2 id h; word
      · rw [List.mem_singleton.1 h]; exact Int.le_refl _
  iunfold hookPost; iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
