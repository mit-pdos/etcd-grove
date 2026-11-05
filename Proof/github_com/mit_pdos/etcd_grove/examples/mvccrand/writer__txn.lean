/- Lean-first (no Rocq counterpart). The proof of `writer.txn`: the read transaction as `read`'s (its
update commits the invariant's state, the writer's half of `γ.σ`, so its revision is the published
one; `FirstRev` is `σ.crev = -1`); the range of its key checked against the snapshot (the writer's
revisions exactly). Read-only: `NewReadOnlyTxnWrite` keeps the read view (`Rev`, no change), each
range as `reader`'s. Writing: the read ended, a write transaction as `put`'s (begun at the same `σ`:
the writer's half), its revision the read's; the loop of `writeOp`s keeps `pendOk` and the pending
log's `LogOk` (from the read's `LogWf'`, `LogWf'.append_nil`), at most six changes and one value
each; the changes' check from `Txn.Changes` and the model's length (`pendOf_chs_length`); `end` with
`tw.End` (`endCb_txnEnd`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__txn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__cur
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__writeOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.checkRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.TxnEnd
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriteLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.iris.style.nameCheck false

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

private theorem statesP_aux' : ∀ (ms : List GoMap) (Hs : List HRev), ms.length = Hs.length →
    (([∗list] x ∈ ms.zip Hs, x.1 ↦$□ x.2.1) : IProp GF) ⊢
      [∗list] x ∈ ms.zip ((Hs.map Prod.fst).zip (List.replicate Hs.length DFrac.discard)),
        x.1 ↦${x.2.2} x.2.1
  | [], _, _ => by simp only [List.zip_nil_left]; exact .rfl
  | _ :: _, [], h => by simp at h
  | m :: ms, e :: Hs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.replicate_succ]
    exact sep_mono .rfl (statesP_aux' ms Hs (by simpa using h))

/-- The states' persistent maps, as `checkRange` takes them (each at `DFrac.discard`). -/
private theorem statesP_statesAt'' (ms : List GoMap) (Hs : List HRev) :
    statesP (GF := GF) ms Hs ⊢
      statesAt ms (Hs.map Prod.fst) (List.replicate Hs.length DFrac.discard) := by
  iintro H
  iunfold statesP at H
  icases H with ⟨%Hl, H⟩
  iunfold statesAt
  isplitr
  · ipureintro; simp [Hl]
  iapply statesP_aux' ms Hs Hl $$ H

end own

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

private theorem worldN_mask'' : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN := by
  unfold worldN mvccN
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide : "mvccrand" ≠ "mvcc") p
    ⟨nclose_subseteq _ _ p hp, h'⟩⟩

/-- **The writer's read update at the invariant** (`read`'s): committed unchanged. -/
private theorem txn_read_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (h : Loc) (γ : RandNames) (σ : MvccState) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.σ (1 : Qp).half σ ⊢
      AU <{ ∃∃ σ', mvccState γ.kv σ' }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ.kv σ', COMM iprop(⌜σ' = σ ∧ σ.crev = -1⌝ ∗ ghostVar γ.σ (1 : Qp).half σ) }> := by
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  have Hm := worldN_mask''
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

/-- **The writer's write update at the invariant** (`put`'s): its begin state is the writer's. -/
private theorem txn_write_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (h : Loc) (γ : RandNames) (σ : MvccState) (hpn : σ.pending = none) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.σ (1 : Qp).half σ ⊢
      AU <{ ∃∃ σ', mvccState γ.kv σ' }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ'.pending = none⌝ ∗ mvccState γ.kv σ',
          COMM iprop(⌜σ' = σ ∧ σ.crev = -1 ∧ 1 ≤ σ.rev⌝ ∗ ghostVar γ.σ (1 : Qp).half σ) }> := by
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  have Hm := worldN_mask''
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
  · iintro ⟨-, Hσ⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; iframe #; ipureintro; exact Hok
    imodintro
    iframe Hw
    ipureintro
    obtain ⟨h1, h2, h3, -⟩ := Hok
    refine ⟨rfl, h1, ?_⟩
    have : sint.nat p = (sint.Z p).toNat := rfl
    omega

/-- A context descriptor for `context.TODO()`'s context, which `rangeCtx true` ignores. -/
private def todoCdT : context.ContextDesc (IProp GF) :=
  { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }

/-- **A read transaction's `End`**: the thread token back. -/
private theorem end_readT {ty : go.GoType} {v : val}
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (γ : MvccName) (trace : Loc) (σ : MvccState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvccTxn (interface.mkOk ty v) γ trace (.read σ) }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); threadTok }} := by
  have hB : Nonempty MvccStorage := by
    refine ⟨etcdStorage ⟨?_, ∅, 0, W64 0, null, ?_, false⟩⟩
    · constructor <;> first | exact default | (constructor <;> exact default)
    · exact default
  obtain ⟨B⟩ := hB
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iapply (hEnd γ trace (.read σ) 1 B iprop(True) iprop(True)) $$ [Htx]
  · iframe Hpkg Htx
  inext
  iintro ⟨Htt, -⟩
  iapply HΦ $$ Htt

theorem writer.txn.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_cur : writer.cur.spec (GF := GF) (hG := hG))
    (wp_begin : writer.begin.spec (GF := GF) (hG := hG))
    (wp_checkHook : writer.checkHook.spec (GF := GF) (hG := hG))
    (wp_end : writer.end.spec (GF := GF) (hG := hG))
    (wp_writeOp : writer.writeOp.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_genKey : rng.genKey.spec (GF := GF) (hG := hG))
    (wp_genRange : rng.genRange.spec (GF := GF) (hG := hG))
    (wp_checkRange : checkRange.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_roTxn : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG)) :
    writer.txn.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L i s n hn0 hn1
  haveI := hpers.1 wv.kv' γ.kv
  wp_start as ⟨Hctx, Hown, Hpre, Hvals⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmv, #Htu, #Hw, #Hinv, #Hhist, #Hkv, #Hhook, Hhok⟩
  iunfold hookOk at Hhok
  icases Hhok with #Hhok
  iunfold writerOwn at Hown
  icases Hown with ⟨Htt, Hbk, Hrd, Hidle, ⟨%g, Hg⟩, Hlm, Hlo⟩
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  obtain ⟨Hpn, Hlen, Hbound, Hmatch⟩ := Hid
  ihave %Hsh := (hsh.1 wv.kv' γ.kv) $$ Hkv
  obtain ⟨tyK, vK, hkv, hRead, hWriteC, -⟩ := Hsh
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  wp_auto
  wp_apply wp_cur w wv γ (W64 (σ.rev : Int)) $$ [$Hpkg $Hw $Hinv $Hpv] as Hpv
  (try wp_auto)
  wp_apply wp_intn wv.r' g (W64 4) (by decide) $$ [$Hpkg $Hg] as %x ⟨⟨%g1, Hg⟩, %Hx⟩
  (try wp_auto)
  simp only [go_etcd_io.etcd.server.v3.storage.mvcc.ConcurrentReadTxMode,
    go_etcd_io.etcd.server.v3.storage.mvcc.SharedBufReadTxMode]
  wp_auto
  wp_join iprop(∃ (md : w32) (g2 : rng), w_ptr ↦ w ∗ mode_ptr ↦ md ∗ wv.r' ↦ g2) at next
    with [w mode Hg] as ⟨%md, %g2, w, mode, Hg⟩
  · by_cases hx0 : x = W64 0
    · simp only [hx0, decide_true, Bool.not_true]
      wp_auto
      wp_join_done
    · simp only [decide_eq_false hx0, Bool.not_false]
      wp_auto
      wp_apply wp_intn wv.r' g1 (W64 2) (by decide) $$ [$Hpkg $Hg] as %y ⟨⟨%g2, Hg⟩, %Hy⟩
      wp_if_destruct
      · (try wp_auto)
        wp_join_done
      · wp_join_done
  -- the read transaction, at the writer's state
  wp_apply wp_traceTODO $$ [$Htu] as %trace ⟨%Htn, Htr⟩
  rw [hkv]
  (try wp_auto)
  wp_apply (hRead γ.kv md trace true
      (fun σ' => iprop(⌜σ' = σ ∧ σ.crev = -1⌝ ∗ ghostVar γ.σ (1 : Qp).half σ))) $$
      [$Hmv $Hkv $Htt $Htr Hgσ] as %t ⟨Htr, %σ', Htx, %Heq, Hgσ⟩
  · isplitr
    · ipureintro; exact Htn
    iapply txn_read_au hpers wv.h' γ σ $$ [$Hinv $Hgσ]
  have Heq0 := Heq.1.symm
  subst Heq0
  have hcrev := Heq.2
  icases (persistent_entails_right (hsh.2.2.1 t γ.kv trace (.read σ))) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tyT, vT, rfl, hRev, hFirst, hRange, -, -, -, hEnd⟩ := Hsht
  (try wp_auto)
  wp_apply (hRev γ.kv trace (.read σ)) $$ [$Hmv $Htx] as Htx
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [MTxn.state, decide_true]
  (try wp_auto)
  wp_apply (hFirst γ.kv trace (.read σ)) $$ [$Hmv $Htx] as Htx
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; rw [hcrev]
  (try wp_auto)
  wp_apply wp_genKey wv.r' g2 $$ [$Hpkg $Hg] as %ks ⟨⟨%g3, Hg⟩, %kk, Hks, -, %Hkk⟩
  (try wp_auto)
  -- the snapshot is the writer's revisions
  icases histW_lb γ.h Hs $$ HW with ⟨HW, #Hlb⟩
  wp_apply wp_snapshot wv.h' γ.h Hs $$ [$Hpkg $Hrd $Hlb]
    as %sl ⟨Hrd, %ms, %Hs', %Hpre, %Hscap, #Hlb', #Hms, #Hst⟩
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
  have hrev : σ.rev = Hs'.length - 1 := by unfold MvccState.rev; omega
  have hcur0 : 0 ≤ sint.Z (W64 (σ.rev : Int)) := by rw [hrev]; word
  have hcur1 : sint.Z (W64 (σ.rev : Int)) + 2 < 2 ^ 63 := by rw [hrev]; word
  have hcurZ : sint.Z (W64 (σ.rev : Int)) = (σ.rev : Int) := by rw [hrev]; word
  have hcurlt : sint.nat (W64 (σ.rev : Int)) < ms.length := by
    have : sint.nat (W64 (σ.rev : Int)) = (sint.Z (W64 (σ.rev : Int))).toNat := rfl
    rw [this, hcurZ]; omega
  have hms : ∀ r : Nat, r ≤ sint.nat (W64 (σ.rev : Int)) →
      ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch M (stateAt σ.log r) := by
    intro r hr
    have : sint.nat (W64 (σ.rev : Int)) = (sint.Z (W64 (σ.rev : Int))).toNat := rfl
    rw [this, hcurZ] at hr
    obtain ⟨e', he', hok⟩ := Hmatch r (by omega)
    exact ⟨e'.1, by rw [List.getElem?_map, he']; rfl, hok.1⟩
  have hne : σ.log ≠ [] := by intro h0; have h0l := congrArg List.length h0; simp only [List.length_nil] at h0l; omega
  -- the range of the key
  wp_apply wp_ctxTODO
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave #Hctxr : mvcc.rangeCtx true todoCtxVal (todoCdT (GF := GF)) $$ []
  · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
  wp_apply (hRange γ.kv trace true (.read σ) todoCtxVal todoCdT true ks slice.nil kk []
      (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)) $$ [$Hmv $Htx $Htr $Hctxr $Hks $Hnil]
    as %rr %err ⟨%Hrn, Htx, Htr, Hout, -, %Hlwf⟩
  simp only [MTxn.readLog, MTxn.readRev, MTxn.state] at Hlwf
  rw [show (MTxn.read σ).readLog = σ.log from rfl, show (MTxn.read σ).readRev = W64 (σ.rev : Int)
    from rfl, show (MTxn.read σ).state.crev = -1 from hcrev]
  ihave Hout := mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ hcur0 $$ Hout
  ihave Hout : rangeOutcome rr err σ.log (W64 (σ.rev : Int)) (decide ((slice.nil : GoSlice) = slice.nil))
      kk [] (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) $$ [Hout]
  · simp only [decide_true]; iexact Hout
  have hLog : txn.LogOk σ.log := txn.LogOk.of_cert ⟨Hlwf.1, by omega, Hlwf.2⟩ hne
  ihave Hsts := statesP_statesAt'' ms Hs' $$ Hst
  wp_apply (wp_checkRange sl DFrac.discard ms (Hs'.map Prod.fst)
      (List.replicate Hs'.length DFrac.discard) (W64 (σ.rev : Int))
      { key' := ks, end' := slice.nil, ro' := zeroValDef } kk [] DFrac.discard DFrac.discard rr err
      σ.log hLog hcur0 hcurlt hms) $$ [$Hpkg $Hmv $Hms $Hsts $Hks $Hnil $Hout] as -
  · ipureintro; exact Hrn rfl
  (try wp_auto)
  by_cases hx0 : x = W64 0
  · -- read-only: the read transaction made a write one, one to three ranges
    simp only [hx0, decide_true, Bool.not_true, Bool.not_false]
    (try wp_auto)
    wp_apply (wp_roTxn _ γ.kv trace σ) $$ [$Hmv $Htx] as %t1 Htx
    icases (persistent_entails_right (hsh.2.2.1 t1 γ.kv trace (.read σ))) $$ Htx with ⟨%Hsh1, Htx⟩
    obtain ⟨ty1, v1, rfl, hRev1, -, hRange1, -, -, hCh1, hEnd1⟩ := Hsh1
    (try wp_auto)
    wp_apply wp_intn wv.r' g3 (W64 3) (by decide) $$ [$Hpkg $Hg] as %y ⟨⟨%g4, Hg⟩, %Hy⟩
    (try wp_auto)
    ihave HJ : (∃ (jv : w64) (g5 : rng), "j" ∷ j_ptr ↦ jv ∗ "Hg" ∷ wv.r' ↦ g5 : IProp GF) $$ [j Hg]
    · iexists W64 0, g4; iframe
    wp_for HJ
    wp_if_destruct
    · wp_apply wp_genRange wv.r' g5 (W64 (σ.rev : Int)) hcur0 hcur1 $$ [$Hpkg $Hg]
        as %qq ⟨⟨%g6, Hg⟩, %kk2, %e2, Hk2, -, He2, -, %Hq2⟩
      imod ownSlice_persist $$ Hk2 with #Hk2
      imod ownSlice_persist $$ He2 with #He2
      (try wp_auto)
      wp_apply wp_ctxTODO
      (try wp_auto)
      wp_apply (hRange1 γ.kv trace true (.read σ) todoCtxVal todoCdT true qq.key' qq.end' kk2 e2 qq.ro')
          $$ [$Hmv $Htx $Htr $Hctxr $Hk2 $He2]
        as %rr2 %err2 ⟨%Hrn2, Htx, Htr, Hout2, -, -⟩
      rw [show (MTxn.read σ).readLog = σ.log from rfl, show (MTxn.read σ).readRev = W64 (σ.rev : Int)
        from rfl, show (MTxn.read σ).state.crev = -1 from hcrev]
      ihave Hout2 := mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ hcur0 $$ Hout2
      ihave Hsts := statesP_statesAt'' ms Hs' $$ Hst
      wp_apply (wp_checkRange sl DFrac.discard ms (Hs'.map Prod.fst)
          (List.replicate Hs'.length DFrac.discard) (W64 (σ.rev : Int)) qq kk2 e2 DFrac.discard
          DFrac.discard rr2 err2 σ.log hLog hcur0 hcurlt hms)
        $$ [$Hpkg $Hmv $Hms $Hsts $Hk2 $He2 $Hout2] as -
      · ipureintro; exact Hrn2 rfl
      wp_for_post
      iframe
      iexists _, _
      iframe
    · wp_apply (hRev1 γ.kv trace (.read σ)) $$ [$Hmv $Htx] as Htx
      (try wp_auto)
      simp only [MTxn.state, decide_true]
      (try wp_auto)
      wp_apply (hCh1 γ.kv trace (.read σ)) $$ [$Hmv $Htx] as %chs ⟨Htx, %Hchs⟩
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]
        simp only [MTxn.pend, List.length_nil] at Hchs
        word
      (try wp_auto)
      wp_apply (end_readT hEnd1 γ.kv trace σ) $$ [$Hmv $Htx] as Htt
      (try wp_auto)
      iapply HΦ
      isplitl [Htt Hbk Hrd Hgσ HW Hpv Hg Hlm Hlo]
      · iexists σ, Hs'
        iunfold writerOwn
        iunfold writerIdle
        iframe
        ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
      isplitl [Hpre]
      · iright; iframe
      iexists n; iframe; ipureintro; omega
  · -- writing: the read ended, a write transaction at its revision
    simp only [decide_eq_false hx0, Bool.not_true, Bool.not_false]
    (try wp_auto)
    wp_apply (end_readT hEnd γ.kv trace σ) $$ [$Hmv $Htx] as Htt
    (try wp_auto)
    ihave Hidle : writerIdle γ σ Hs' $$ [Hgσ HW Hpv]
    · iunfold writerIdle; iframe; ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
    wp_apply wp_begin w wv γ σ Hs' $$ [$Hpkg $Hw $Hrd $Hinv $Hidle] as %p ⟨Hrd, Hidle, Hp⟩
    (try wp_auto)
    wp_apply wp_traceTODO $$ [$Htu] as %trace2 ⟨%Htr2, Htrc2⟩
    (try wp_auto)
    iunfold writerIdle at Hidle
    icases Hidle with ⟨Hgσ, HW, Hpv, -⟩
    wp_apply (hWriteC γ.kv trace2 true q B iprop(True) (hookPre wv i s) iprop(True ∗ hookPost wv i) f
        (fun σ' => iprop(⌜σ' = σ ∧ σ.crev = -1 ∧ 1 ≤ σ.rev⌝ ∗ ghostVar γ.σ (1 : Qp).half σ)))
      $$ [$Hmv $Hkv $Htt $Htrc2 $Hbk $Hhook $Hpre Hgσ]
      as %tw ⟨Htrc2, Hbk, ⟨%σ0, Htw, ⟨%Heq2, Hgσ⟩⟩, ⟨-, Hpost⟩⟩
    · isplitr
      · ipureintro; exact Htr2
      isplitr
      · iapply Hhok
      iapply txn_write_au hpers wv.h' γ σ Hpn $$ [$Hinv $Hgσ]
    have Heq3 := Heq2.1.symm
    subst Heq3
    have hrev1 := Heq2.2.2
    icases (persistent_entails_right (hsh.2.2.1 tw γ.kv trace2 (.write σ []))) $$ Htw
      with ⟨%Hsht2, Htw⟩
    obtain ⟨tty, tv, rfl, hRevW, -, -, -, -, hChW, hEndW⟩ := Hsht2
    ihave Hidle : writerIdle γ σ Hs' $$ [Hgσ HW Hpv]
    · iunfold writerIdle; iframe; ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
    (try wp_auto)
    iunfold hookPost at Hpost
    icases Hpost with ⟨Happ, Hsav⟩
    wp_apply wp_checkHook w wv i $$ [$Hpkg $Hw $Hsav] as Hsav
    (try wp_auto)
    wp_apply (hRevW γ.kv trace2 (.write σ [])) $$ [$Hmv $Htw] as Htw
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp only [MTxn.state, decide_true]
    (try wp_auto)
    wp_apply wp_intn wv.r' g3 (W64 3) (by decide) $$ [$Hpkg $Hg] as %y ⟨⟨%g4, Hg⟩, %Hy⟩
    (try wp_auto)
    have hlogwf : txn.LogOk (σ.log ++ [[]]) := by
      refine txn.LogOk.of_cert ⟨LogWf'.append_nil Hlwf.1 hne, by simp; omega, ?_⟩ (by simp)
      intro cs hcs
      simp only [List.mem_append, List.mem_singleton] at hcs
      rcases hcs with h | h
      · exact Hlwf.2 cs h
      · subst h; simp
    have hok0 : pendOk σ Hs' [] ⟨W64 (Hs'.length : Int), lastSt Hs', []⟩ :=
      ⟨rfl, stMatch_lastSt σ Hs' Hlen (by omega) Hmatch⟩
    ihave HJ : (∃ (jv : w64) (pend : List Change) (P : PendM) (nv : w64),
        "j" ∷ j_ptr ↦ jv ∗ "Hrd" ∷ histRd wv.h' γ.h ∗ "Hidle" ∷ writerIdle γ σ Hs' ∗
        "Htw" ∷ mvccTxn (interface.mkOk tty tv) γ.kv trace2 (.write σ pend) ∗
        "Htrc2" ∷ traceutil.ownTrace trace2 true ∗
        "Hp" ∷ ownPending p P ∗ "Hg" ∷ (∃ g : rng, wv.r' ↦ g) ∗
        "Hlm" ∷ (∃ Lm : GMap w64 Bool, wv.leases' ↦$ Lm ∗ ⌜∀ id, (Lm !! id).isSome = true ↔ id ∈ L⌝) ∗
        "Hlo" ∷ lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log pend) ∗
        "Hvals" ∷ wF go!"vals" w ↦ nv ∗
        ⌜pendOk σ Hs' pend P ∧ txn.LogOk (σ.log ++ [pend]) ∧ 0 ≤ sint.Z jv ∧ sint.Z jv ≤ 3 ∧
          (pend.length : Int) ≤ 6 * sint.Z jv ∧ sint.Z n ≤ sint.Z nv ∧
          sint.Z nv ≤ sint.Z n + sint.Z jv⌝ : IProp GF)
      $$ [j Hrd Hidle Htw Htrc2 Hp Hg Hlm Hlo Hvals]
    · iexists W64 0, [], ⟨W64 (Hs'.length : Int), lastSt Hs', []⟩, n
      iframe
      isplitl [Hg]
      · iexists g4; iframe
      ipureintro
      refine ⟨hok0, hlogwf, ?_⟩
      simp only [List.length_nil]
      word
    wp_for HJ
    icases HJ with %HJp
    obtain ⟨hok, hLok, hj0, hj3, hpl, hnv0, hnv1⟩ := HJp
    wp_if_destruct
    · -- one more operation
      icases Hg with ⟨%g5, Hg⟩
      ihave HctxW : writerCtx w wv γ B f $$ []
      · iunfold writerCtx; iunfold hookOk; rw [hkv]; iframe #
      wp_apply (wp_writeOp w wv γ B f σ Hs' L (interface.mkOk tty tv) trace2 true p P pend nv
          hok hLok hcrev hrev1 (by omega) (by omega) (by word))
        $$ [$HctxW $Hrd $Hidle $Htw $Htrc2 $Hp $Hlm $Hlo $Hvals Hg]
        as ⟨%pend', %P', %n', %Hop, Hrd, Hidle, Htw, Htrc2, Hp, Hg, Hlm, Hlo, Hvals⟩
      · iexists g5; iframe
      wp_for_post
      iframe
      iexists _, pend ++ pend', P', n'
      iframe
      ipureintro
      obtain ⟨hok', hLok', hpl', hn'⟩ := Hop
      have hy3 : sint.Z (W64 1 + y) ≤ 3 := by word
      have hj1 : sint.Z (jv + W64 1) = sint.Z jv + 1 := by word
      refine ⟨hok', hLok', by omega, by omega, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · rcases hn' with rfl | rfl
        · omega
        · have : sint.Z (nv + W64 1) = sint.Z nv + 1 := by word
          omega
    · -- the changes' check, then `end`
      wp_apply (hChW γ.kv trace2 (.write σ pend)) $$ [$Hmv $Htw] as %chs ⟨Htw, %Hchs⟩
      iunfold ownPending at Hp
      icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
      ihave %Hcl := ownSlice_len $$ Hpch
      have hcl' : P.chs.length = pend.length := by rw [hok.1]; exact pendOf_chs_length _ _ _
      (try wp_auto)
      wp_apply wp_check
      · ipureintro
        simp only [MTxn.pend] at Hchs
        have h1 : sint.Z chs.len = (pend.length : Int) := by
          obtain ⟨ha, hb⟩ := Hchs; word
        have h2 : sint.Z pv.changes'.len = (pend.length : Int) := by
          have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
          omega
        simp only [decide_eq_true_eq]; rw [h1, h2]
      (try wp_auto)
      ihave Hp : ownPending p P $$ [Hpv Hpst Hpch Hpcap]
      · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
      ihave #Hkv0 : isMvcc wv.kv' γ.kv $$ []
      · rw [hkv]; iexact Hkv
      ihave Hcb := endCb_txnEnd hpers hEndW wv.h' γ σ Hs' pend P trace2 q B hok Hpn Hlen Hmatch
      wp_apply (wp_end w wv γ σ Hs' p P pend (methods tty go!"End" tv)
          iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
            inv worldN (worldInv wv.h' γ) ∗
            mvccTxn (interface.mkOk tty tv) γ.kv trace2 (.write σ pend) ∗
            mvccBackend γ.kv q B iprop(True))
          (mvccBackend γ.kv q B iprop(True)) hok)
        $$ [$Hpkg $Hmv $Hw $Hrd $Hinv $Hkv0 $Hidle $Hp $Hcb $Htw $Hbk] as ⟨Hrd, Htt, Hbk, Hidle⟩
      iapply HΦ
      isplitl [Htt Hbk Hrd Hidle Hg Hlm Hlo]
      · iexists _, _
        iunfold writerOwn
        iframe Htt Hbk Hrd Hidle Hg Hlm
        rw [pendItems_commit]; iexact Hlo
      isplitl [Happ Hsav]
      · ileft; iunfold hookPost; iframe
      iexists nv; iframe; ipureintro; omega

end proof

end mvccrand
end EtcdGrove
end Perennial
