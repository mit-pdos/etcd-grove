/- Lean-first (no Rocq counterpart). The proof of `writer.read`: `Read`'s update fires at the
tester's invariant's state, which is the writer's (its half of `γ.σ`), committed unchanged; so the
read transaction is at `σ`, its revision the published one (`writerIdle`), and the snapshot is the
writer's revisions exactly (`histW_lb`, as in `begin`), each state the store's (`revOk`), which
`checkRange` needs, with the read log's `LogOk` from `Range`'s post and `σ.crev = -1` from the
invariant (the outcome `rangeOutcome`, `rangeOutcomeC_neg`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__read
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__cur
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.checkRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Std.Namespaces

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

private theorem statesP_aux : ∀ (ms : List GoMap) (Hs : List HRev), ms.length = Hs.length →
    (([∗list] x ∈ ms.zip Hs, x.1 ↦$□ x.2.1) : IProp GF) ⊢
      [∗list] x ∈ ms.zip ((Hs.map Prod.fst).zip (List.replicate Hs.length DFrac.discard)),
        x.1 ↦${x.2.2} x.2.1
  | [], _, _ => by simp only [List.zip_nil_left]; exact .rfl
  | _ :: _, [], h => by simp at h
  | m :: ms, e :: Hs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.replicate_succ]
    exact sep_mono .rfl (statesP_aux ms Hs (by simpa using h))

/-- The states' persistent maps, as `checkRange` takes them (each at `DFrac.discard`). -/
private theorem statesP_statesAt' (ms : List GoMap) (Hs : List HRev) :
    statesP (GF := GF) ms Hs ⊢
      statesAt ms (Hs.map Prod.fst) (List.replicate Hs.length DFrac.discard) := by
  iintro H
  iunfold statesP at H
  icases H with ⟨%Hl, H⟩
  iunfold statesAt
  isplitr
  · ipureintro; simp [Hl]
  iapply statesP_aux ms Hs Hl $$ H

end own

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

private theorem worldN_mask' : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN := by
  unfold worldN mvccN
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide : "mvccrand" ≠ "mvcc") p
    ⟨nclose_subseteq _ _ p hp, h'⟩⟩

/-- **The writer's read update at the invariant**: the invariant's state is the writer's (its half
of `γ.σ`), committed unchanged, with no compaction. -/
private theorem writer_read_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (h : Loc) (γ : RandNames) (σ : MvccState) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.σ (1 : Qp).half σ ⊢
      AU <{ ∃∃ σ', mvccState γ.kv σ' }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ.kv σ', COMM iprop(⌜σ' = σ ∧ σ.crev = -1⌝ ∗ ghostVar γ.σ (1 : Qp).half σ) }> := by
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  have Hm := worldN_mask'
  iintro ⟨#Hinv, Hw⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ1, %S, %p, %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ Hw
  have Hag' := Hag.symm
  subst Hag'
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iframe Hw
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iframe Hw
    ipureintro
    exact ⟨rfl, Hok.1⟩

/-- A context descriptor for `context.TODO()`'s context, which `rangeCtx true` ignores (txn's
`todoCd`). -/
private def todoCd' : context.ContextDesc (IProp GF) :=
  { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }

theorem writer.read.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_cur : writer.cur.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_genRange : rng.genRange.spec (GF := GF) (hG := hG))
    (wp_checkRange : checkRange.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG)) :
    writer.read.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L
  haveI := hpers.1 wv.kv' γ.kv
  wp_start as ⟨Hctx, Hown⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmv, #Htu, #Hw, #Hinv, #Hhist, #Hkv, #Hhook, Hhok⟩
  iunfold hookOk at Hhok
  icases Hhok with #Hhok
  iunfold writerOwn at Hown
  icases Hown with ⟨Hrdr, Hbk, Hrd, Hidle, ⟨%g, Hr⟩, Hlm, Hlo⟩
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  obtain ⟨Hpend, Hlen, Hbound, Hmatch⟩ := Hid
  haveI := hpers.1 wv.kv' γ.kv
  ihave %Hsh := (hsh.1 wv.kv' γ.kv) $$ Hkv
  obtain ⟨tyK, vK, hkv, hRead, -⟩ := Hsh
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  wp_auto
  wp_apply wp_cur w wv γ (W64 (σ.rev : Int)) $$ [$Hw $Hinv $Hpv] as Hpv
  (try wp_auto)
  wp_apply wp_traceTODO as %trace ⟨%Htn, Htr⟩
  rw [hkv]
  (try wp_auto)
  wp_apply (hRead γ.kv _ trace true
      (fun σ' => iprop(⌜σ' = σ ∧ σ.crev = -1⌝ ∗ ghostVar γ.σ (1 : Qp).half σ))) $$
      [$Hmv $Hkv $Hrdr $Htr Hgσ] as %t ⟨Htr, %σ', Htx, %Heq, Hgσ⟩
  · isplitr
    · ipureintro; exact Htn
    iapply writer_read_au hpers wv.h' γ σ $$ [$Hinv $Hgσ]
  obtain ⟨rfl, hcrev⟩ := Heq
  icases (persistent_entails_right (hsh.2.2.1 t γ.kv trace (.read σ'))) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tyT, vT, rfl, hRev, -, hRange, -, -, -, hEnd⟩ := Hsht
  (try wp_auto)
  wp_apply (hRev γ.kv trace (.read σ')) $$ [$Hmv $Htx] as Htx
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [MTxn.state, decide_true]
  (try wp_auto)
  -- the snapshot is the writer's revisions
  icases histW_lb γ.h Hs $$ HW with ⟨HW, #Hlb⟩
  wp_apply wp_snapshot wv.h' γ.h Hs $$ [$Hrd $Hlb]
    as %s ⟨Hrd, %ms, %Hs', %Hpre, %Hscap, #Hlb', #Hms, #Hst⟩
  ihave %Hle : ⌜Hs' <+: Hs⌝ $$ [HW]
  · iunfold histW at HW
    icases HW with ⟨%x, %Hx, -, Hl, -, -⟩
    ihave %H := mono_list_auth_lb_valid γ.h.l _ _ _ $$ Hl Hlb'
    ipureintro; exact H.2
  have hHs : Hs' = Hs := List.IsPrefix.eq_of_length Hle (Nat.le_antisymm Hle.length_le Hpre.1.length_le)
  subst hHs
  ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  have h2 := Hpre.2
  have hrev : σ'.rev = Hs'.length - 1 := by unfold MvccState.rev; omega
  have hcur0 : 0 ≤ sint.Z (W64 (σ'.rev : Int)) := by rw [hrev]; word
  have hcur1 : sint.Z (W64 (σ'.rev : Int)) + 2 < 2 ^ 63 := by rw [hrev]; word
  have hcurZ : sint.Z (W64 (σ'.rev : Int)) = (σ'.rev : Int) := by rw [hrev]; word
  (try wp_auto)
  wp_apply wp_genRange wv.r' g (W64 (σ'.rev : Int)) hcur0 hcur1 $$ [$Hr]
    as %qq ⟨⟨%g', Hr⟩, %kk, %e, Hk, Hkcap, He, Hecap, %Hq⟩
  imod ownSlice_persist $$ Hk with #Hk
  imod ownSlice_persist $$ He with #He
  (try wp_auto)
  wp_apply wp_ctxTODO
  ihave #Hrctx : mvcc.rangeCtx true todoCtxVal (todoCd' (GF := GF)) $$ []
  · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
  (try wp_auto)
  wp_apply (hRange γ.kv trace true (.read σ') todoCtxVal todoCd' true qq.key' qq.end' kk e qq.ro')
      $$ [$Hmv $Htx $Htr $Hrctx $Hk $He]
    as %rr %err ⟨%Hrn, Htx, Htr, Hout, -, %Hlwf⟩
  simp only [MTxn.readLog, MTxn.readRev, MTxn.state] at Hlwf
  rw [show (MTxn.read σ').readLog = σ'.log from rfl, show (MTxn.read σ').readRev = W64 (σ'.rev : Int)
    from rfl, show (MTxn.read σ').state.crev = -1 from hcrev]
  ihave Hout := mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ hcur0 $$ Hout
  have hne : σ'.log ≠ [] := by intro h0; rw [h0] at Hlen; simp at Hlen; subst Hlen; simp at h2
  have hLog : txn.LogOk σ'.log := txn.LogOk.of_cert ⟨Hlwf.1, by omega, Hlwf.2⟩ hne
  have hcurlt : sint.nat (W64 (σ'.rev : Int)) < ms.length := by
    have : sint.nat (W64 (σ'.rev : Int)) = (sint.Z (W64 (σ'.rev : Int))).toNat := rfl
    rw [this, hcurZ]; omega
  have hms : ∀ r : Nat, r ≤ sint.nat (W64 (σ'.rev : Int)) →
      ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch M (stateAt σ'.log r) := by
    intro r hr
    have : sint.nat (W64 (σ'.rev : Int)) = (sint.Z (W64 (σ'.rev : Int))).toNat := rfl
    rw [this, hcurZ] at hr
    obtain ⟨e', he', hok⟩ := Hmatch r (by omega)
    exact ⟨e'.1, by rw [List.getElem?_map, he']; rfl, hok.1⟩
  ihave Hsts := statesP_statesAt' ms Hs' $$ Hst
  (try wp_auto)
  wp_apply (wp_checkRange s DFrac.discard ms (Hs'.map Prod.fst)
      (List.replicate Hs'.length DFrac.discard) (W64 (σ'.rev : Int)) qq kk e DFrac.discard
      DFrac.discard rr err σ'.log hLog hcur0 hcurlt hms) $$ [$Hms $Hsts $Hk $He $Hout]
  · ipureintro; exact Hrn rfl
  iintro -
  (try wp_auto)
  have hE := hEnd γ.kv trace (.read σ') 1 B iprop(True) iprop(True)
  dsimp only at hE
  wp_apply hE $$ [$Hmv $Htx] as ⟨Hrdr, -⟩
  (try wp_auto)
  iapply HΦ
  iunfold writerOwn
  iunfold writerIdle
  iframe
  ipureintro; exact ⟨Hpend, Hlen, Hbound, Hmatch⟩

end proof

end mvccrand
end EtcdGrove
end Perennial
