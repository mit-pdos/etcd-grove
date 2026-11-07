/- Lean-first (no Rocq counterpart). The proof of `reader`: each read's update (`KV.Rev`,
`KV.Read`) commits the tester's invariant's state unchanged (`reader_au`), recording what the
invariant says of it then (`readQ`): the floor, a lower bound of the published revision `Load`ed
before, at most the revision read (the monotone counter `γ.pub`); the history's lower bound `Hl`
covering the notified log (`histOkM`); no compaction. So `seen`'s checks hold, and the snapshot
taken after has every revision up to the one read, each state the store's (`hist_match`), which
`checkRange` needs. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.reader
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__seen
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__intn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.checkRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Std.Namespaces

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

/-! ## The history against the read log -/

section model
variable [GooseExts]

/-- **The history's states match the read log**: a lower bound `Hl` covering the notified log
(`histOkM`), and any extension `Hs` of it, have the store's state at each revision of the log. -/
theorem hist_match (σ : MvccState) (Hl Hs : List HRev) (hok : histOkM σ Hl) (hpre : Hl <+: Hs)
    (r : Nat) (hr : r < σ.log.length) :
    ∃ M, (Hs.map Prod.fst)[r]? = some M ∧ stMatch M (stateAt σ.log r) := by
  have hle : σ.log.length ≤ σ.notifiedLog.length := by
    unfold MvccState.notifiedLog; split <;> simp
  obtain ⟨e, he, hrev⟩ := hok.2 r (by omega)
  refine ⟨e.1, ?_, ?_⟩
  · rw [List.getElem?_map, Perennial.prefix_getElem? hpre he]; rfl
  · have h1 := hrev.1
    have : stateAt σ.notifiedLog r = stateAt σ.log r := by
      unfold MvccState.notifiedLog; split
      · rfl
      · exact stateAt_append_lt _ _ hr
    rw [this] at h1; exact h1

/-- **`seen`'s premises at a read**: the floor at most the revision read, the revision in the
history's lower bound (the log's bound: the revision as a word is the revision). -/
theorem seen_ok (σ : MvccState) (Hl : List HRev) (fl : w64) (hfl0 : 0 ≤ sint.Z fl)
    (hq : sint.nat fl ≤ σ.rev ∧ 1 ≤ σ.rev ∧ σ.crev = -1 ∧ histOkM σ Hl ∧
      σ.log.length + 3 ≤ 2 ^ 63) :
    sint.Z fl ≤ sint.Z (W64 (σ.rev : Int)) ∧ sint.Z (W64 (σ.rev : Int)) < Hl.length ∧
      sint.Z (W64 (σ.rev : Int)) = σ.rev := by
  obtain ⟨hf, h1, -, hh, hb⟩ := hq
  have hle : σ.log.length ≤ σ.notifiedLog.length := by
    unfold MvccState.notifiedLog; split <;> simp
  have hr : σ.rev < σ.log.length := by unfold MvccState.rev at h1 ⊢; omega
  have hz : sint.Z (W64 (σ.rev : Int)) = σ.rev := by word
  have hfz : (sint.nat fl : Int) = sint.Z fl := by
    have : sint.nat fl = (sint.Z fl).toNat := rfl
    omega
  refine ⟨?_, ?_, hz⟩ <;> rw [hz]
  · omega
  · have := hh.1; omega

/-- **`checkRange`'s premises at a read** at the state `σ`, with the snapshot `Hs` (its maps
`ms`) taken after: the revision read not negative, in the snapshot, every revision up to it the
log's state. -/
theorem check_ok (σ : MvccState) (Hl Hs : List HRev) (ms : List GoMap) (fl : w64)
    (hq : sint.nat fl ≤ σ.rev ∧ 1 ≤ σ.rev ∧ σ.crev = -1 ∧ histOkM σ Hl ∧
      σ.log.length + 3 ≤ 2 ^ 63)
    (hpre : Hl <+: Hs) (hms : ms.length = Hs.length) :
    0 ≤ sint.Z (W64 (σ.rev : Int)) ∧ sint.nat (W64 (σ.rev : Int)) < ms.length ∧
      ∀ r : Nat, r ≤ sint.nat (W64 (σ.rev : Int)) →
        ∃ M, (Hs.map Prod.fst)[r]? = some M ∧ stMatch M (stateAt σ.log r) := by
  obtain ⟨-, h1, -, hh, hb⟩ := hq
  have hle : σ.log.length ≤ σ.notifiedLog.length := by
    unfold MvccState.notifiedLog; split <;> simp
  have hr : σ.rev < σ.log.length := by unfold MvccState.rev at h1 ⊢; omega
  have hz : sint.nat (W64 (σ.rev : Int)) = σ.rev := by
    have : sint.nat (W64 (σ.rev : Int)) = (sint.Z (W64 (σ.rev : Int))).toNat := rfl
    rw [this]
    have : sint.Z (W64 (σ.rev : Int)) = σ.rev := by word
    omega
  have hlen := hpre.length_le
  have h2 := hh.1
  refine ⟨by word, by omega, fun r hr' => hist_match σ Hl Hs hh hpre r (by omega)⟩

/-- **The read log is well formed** (`checkRange`'s `LogOk`), from the range contract's facts. -/
theorem logOk_read (σ : MvccState) (hb : σ.log.length + 3 ≤ 2 ^ 63) (h1 : 1 ≤ σ.rev)
    (hwf : LogWf' σ.log ∧ ∀ cs ∈ σ.log, cs.length < 2 ^ 63) : txn.LogOk σ.log := by
  have hne : σ.log ≠ [] := by
    intro h0; unfold MvccState.rev at h1; rw [h0] at h1; simp at h1
  exact txn.LogOk.of_cert ⟨hwf.1, by omega, hwf.2⟩ hne

end model

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem statesP_aux : ∀ (ms : List GoMap) (Hs : List HRev), ms.length = Hs.length →
    (([∗list] x ∈ ms.zip Hs, x.1 ↦$□ x.2.1) : IProp GF) ⊢
      [∗list] x ∈ ms.zip ((Hs.map Prod.fst).zip (List.replicate Hs.length DFrac.discard)),
        x.1 ↦${x.2.2} x.2.1
  | [], _, _ => by simp only [List.zip_nil_left]; exact .rfl
  | _ :: _, [], h => by simp at h
  | m :: ms, e :: Hs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.replicate_succ]
    exact sep_mono .rfl (statesP_aux ms Hs (by simpa using h))

/-- The states' persistent maps, as `checkRange` takes them (each at `DFrac.discard`). -/
theorem statesP_statesAt (ms : List GoMap) (Hs : List HRev) :
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

/-- **What a reader's read learns of the state it reads** (persistent): the floor `fl` (a lower
bound of the published revision) at most its revision, a lower bound of the history covering its
notified log, no compaction, and the log's bound. -/
def readQ (γ : RandNames) (fl : Nat) (σ : MvccState) : IProp GF :=
  iprop(∃ Hl : List HRev, monoListLbOwn γ.h.l Hl ∗
    ⌜fl ≤ σ.rev ∧ 1 ≤ σ.rev ∧ σ.crev = -1 ∧ histOkM σ Hl ∧ σ.log.length + 3 ≤ 2 ^ 63⌝)

instance readQ_persistent (γ : RandNames) (fl : Nat) (σ : MvccState) :
    Persistent (readQ (GF := GF) γ fl σ) := by
  unfold readQ; infer_instance

theorem worldN_mask : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN := by
  unfold worldN mvccN
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide : "mvccrand" ≠ "mvcc") p
    ⟨nclose_subseteq _ _ p hp, h'⟩⟩

/-- **A reader's read update at the invariant**: the state committed unchanged, with `readQ`. -/
theorem reader_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (kv : GoInterface) (h : Loc) (γ : RandNames) (fl : Nat) :
    isMvcc kv γ.kv ∗ inv worldN (worldInv h γ) ∗ monoNatLbOwn γ.pub fl ⊢
      AU <{ ∃∃ σ, mvccState γ.kv σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ.kv σ, COMM readQ γ fl σ }> := by
  haveI := hpers.1 kv γ.kv
  haveI := hpers.2.2.2.2.2.1
  haveI := hpers.2.2.2.2.2.2.1
  haveI : ∀ h γ, Timeless (worldInv (GF := GF) h γ) := fun _ _ => by
    unfold worldInv; infer_instance
  have Hm := worldN_mask
  iintro ⟨#Hkv, #Hinv, #Hfl⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p, %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  ihave %Hle := monoNatLbOwn_valid γ.pub 1 (sint.nat p) fl $$ Hpm Hfl
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
    iempintro
  · iintro Hσ
    icases (persistent_entails_right (hreach kv γ.kv σ)) $$ [$Hkv $Hσ] with ⟨%Hr, -, Hσ⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; iframe #; ipureintro; exact Hok
    imodintro
    unfold readQ
    iexists Hl
    iframe Hlb
    ipureintro
    obtain ⟨hc, h1, h2, hh, -⟩ := Hok
    have : (1 : Int) ≤ sint.nat p := by have : sint.nat p = (sint.Z p).toNat := rfl; omega
    exact ⟨by omega, by omega, hc, hh, Hr.2⟩

/-- **A transaction is an interface value whose type meets `TxnWrite`'s contracts**
(`shapes.law`; txn's `mvccTxn_shape`), the transaction kept. -/
theorem mvccTxn_shape (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (t : GoInterface) (γ : MvccName) (trace : Loc) (k : MTxn) :
    mvccTxn (GF := GF) t γ trace k ⊢
      ⌜∃ ty v, t = interface.mkOk ty v ∧ isTxn (GF := GF) ty v⌝ ∗ mvccTxn t γ trace k :=
  persistent_entails_right (hsh.2.2.1 t γ trace k)

/-- **A read transaction's outcome** at no compaction is `rangeOutcome` at its log and
revision (`rangeOutcomeC_neg`). -/
theorem outcome_read (rr : Loc) (err : GoInterface) (σ : MvccState) (en : Bool) (kk e : GoString)
    (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (hc : σ.crev = -1)
    (hb : σ.log.length + 3 ≤ 2 ^ 63) :
    rangeOutcomeC (GF := GF) rr err (MTxn.read σ).readLog (MTxn.read σ).readRev
        (MTxn.read σ).state.crev en kk e ro ⊢
      rangeOutcome rr err σ.log (W64 (σ.rev : Int)) en kk e ro := by
  simp only [MTxn.readLog, MTxn.readRev, MTxn.state]
  rw [hc]
  have : σ.rev ≤ σ.log.length := by unfold MvccState.rev; omega
  exact rangeOutcomeC_neg rr err σ.log _ en kk e ro (by word)

/-- A context descriptor for `context.TODO()`'s context, which `rangeCtx true` ignores (txn's
`todoCd`). -/
def todoCd : context.ContextDesc (IProp GF) :=
  { Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) }

/-- **A read transaction's `End`**: the thread token and the store's reader token back (`Txn.End.contract` at a read
transaction, whose backend arguments do not matter; txn's `end_read`). -/
theorem end_read {ty : go.GoType} {v : val}
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (γ : MvccName) (trace : Loc) (σ : MvccState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvccTxn (interface.mkOk ty v) γ trace (.read σ) }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); threadTok ∗ mvccReaders γ 1 }} := by
  have hB : Nonempty MvccStorage := by
    refine ⟨etcdStorage ⟨?_, ∅, 0, W64 0, null, ?_, false⟩⟩
    · constructor <;> first | exact default | (constructor <;> exact default)
    · exact default
  obtain ⟨B⟩ := hB
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iapply (hEnd γ trace (.read σ) 1 B iprop(True) iprop(True)) $$ [Htx]
  · iframe Hpkg Htx
  inext
  iintro ⟨Htt, Hrdr, -⟩
  iapply HΦ; iframe

theorem reader.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_seen : history.seen.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_intn : rng.intn.spec (GF := GF) (hG := hG))
    (wp_genRange : rng.genRange.spec (GF := GF) (hG := hG))
    (wp_checkRange : checkRange.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_roTxn : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG)) :
    reader.spec (GF := GF) (hG := hG) := by
  intro kv h r γ g reads
  haveI := hpers.1 kv γ.kv
  wp_start as ⟨#Hkv, #Hinv, Hrd, Htt, Hrdr, Hr⟩
  ihave %Hsh := (hsh.1 kv γ.kv) $$ Hkv
  obtain ⟨tyK, vK, rfl, hRead, -, hRev, -⟩ := Hsh
  wp_auto
  ihave HI : (∃ (nv : w64) (g1 : rng), "n" ∷ n_ptr ↦ nv ∗ "Hr" ∷ r ↦ g1 : IProp GF) $$ [n Hr]
  · iexists W64 0, g; iframe
  wp_for HI
  wp_if_destruct
  · -- an iteration: the floor, the published revision loaded in the invariant
    wp_apply_core sync.atomic.Int64.wp_Load (hPub h) (DFrac.own 1) $$ [] [-]
    · iPkgInit
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑worldN from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iunfold worldInv at Hi
    icases Hi with ⟨%σ, %S, %p, %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, #Hlb, %Hok⟩
    ihave #Hfl := monoNatLbOwn_get γ.pub 1 (sint.nat p) $$ Hpm
    iexists p
    iframe Hpub
    iintro Hpub
    imod Hcl with -
    imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; iframe #; ipureintro; exact Hok
    imodintro
    have Hp1 : 1 ≤ sint.Z p := Hok.2.1
    clear Hok
    wp_auto
    wp_join iprop(∃ (fl : w64) (g2 : rng), floor_ptr ↦ fl ∗ r ↦ g2 ∗
        monoNatLbOwn γ.pub (sint.nat fl) ∗ ⌜0 ≤ sint.Z fl⌝) at next with [floor Hr]
      as ⟨%fl, %g2, floor, Hr, #Hfl, %Hfl0⟩
    · wp_apply wp_intn r g1 (W64 4) (by decide) $$ [$Hr] as %x ⟨⟨%g2, Hr⟩, %Hx⟩
      wp_if_destruct
      · ihave #H0 := monoNatLbOwn_le (γ := γ.pub) (sint.nat (W64 0)) (by word) $$ Hfl
        wp_join_done
        iexists W64 0, g2; iframe; iframe #; ipureintro; decide
      · wp_join_done
        iexists p, g2; iframe; iframe #; ipureintro; omega
    wp_apply wp_intn r g2 (W64 4) (by decide) $$ [$Hr] as %sw ⟨⟨%g3, Hr⟩, %Hsw⟩
    wp_if_destruct
    · -- `Rev`
      ihave Hau := reader_au hpers hreach _ h γ (sint.nat fl) $$ [$Hkv $Hinv $Hfl]
      wp_apply (hRev γ.kv (readQ γ (sint.nat fl))) $$ [$Hkv $Htt $Hrdr $Hau] as %rv ⟨Htt, Hrdr, %σ, HQ, %Hrv⟩
      iunfold readQ at HQ
      icases HQ with ⟨%Hl, #Hlb, %Hq⟩
      obtain ⟨h1, h2, h3⟩ := seen_ok σ Hl fl Hfl0 Hq
      subst Hrv
      wp_apply (wp_seen h γ.h Hl fl _ _ h1 h2) $$ [$Hrd $Hlb] as Hrd
      wp_for_post
      iframe
      iexists _, _
      iframe
    wp_if_destruct
    · -- a read-only transaction
      wp_apply wp_traceTODO as %trc ⟨%Htrn, Htrc⟩
      ihave Hau := reader_au hpers hreach _ h γ (sint.nat fl) $$ [$Hkv $Hinv $Hfl]
      wp_apply (hRead γ.kv _ trc true (readQ γ (sint.nat fl))) $$ [$Hkv $Htt $Hrdr $Htrc $Hau]
        as %t0 ⟨Htrc, %σ, Htx, HQ⟩
      · ipureintro; exact Htrn
      iunfold readQ at HQ
      icases HQ with ⟨%Hl, #Hlb, %Hq⟩
      obtain ⟨h1, h2, h3⟩ := seen_ok σ Hl fl Hfl0 Hq
      have hrv : σ.rev + 3 ≤ 2 ^ 63 := by have := Hq.2.2.2.2; unfold MvccState.rev; omega
      wp_apply (wp_roTxn t0 γ.kv trc σ) $$ [$Htx] as %t1 Htx
      icases mvccTxn_shape hsh t1 γ.kv trc (.read σ) $$ Htx with ⟨%Hsh, Htx⟩
      obtain ⟨tyT, vT, rfl, hTRev, -, hTRange, -, -, hTChanges, hTEnd⟩ := Hsh
      wp_apply (hTRev γ.kv trc (.read σ)) $$ [$Htx] as Htx
      simp only [MTxn.state]
      wp_apply (wp_seen h γ.h Hl fl _ _ h1 h2) $$ [$Hrd $Hlb] as Hrd
      wp_apply (wp_snapshot h γ.h Hl) $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
      wp_apply (wp_genRange r g3 _ (by rw [h3]; omega) (by rw [h3]; omega)) $$ [$Hr]
        as %q ⟨⟨%g4, Hr⟩, %kk, %e, Hk, Hkc, He, Hec, %Hq'⟩
      ipersist Hk
      ipersist He
      wp_apply wp_ctxTODO
      ihave #Hctx : mvcc.rangeCtx (GF := GF) true todoCtxVal todoCd $$ []
      · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
      wp_apply (hTRange γ.kv trc true (.read σ) todoCtxVal todoCd true q.key' q.end' kk e q.ro')
        $$ [$Htx $Htrc $Hctx $Hk $He] as %rr %err ⟨%Hrn, Htx, Htrc, Hout, -, %Hlwf⟩
      ihave Hout := outcome_read rr err σ _ kk e q.ro' Hq.2.2.1 Hq.2.2.2.2 $$ Hout
      ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
      · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
      ihave Hsts := statesP_statesAt ms Hs $$ Hst
      obtain ⟨c0, c1, c2⟩ := check_ok σ Hl Hs ms fl Hq Hpre.1 Hmlen
      have hlog := logOk_read σ Hq.2.2.2.2 Hq.2.1 Hlwf
      wp_apply (wp_checkRange s DFrac.discard ms (Hs.map Prod.fst)
        (List.replicate Hs.length DFrac.discard) _ q kk e DFrac.discard DFrac.discard rr err σ.log
        hlog c0 c1 c2) $$ [$Hms $Hsts $Hk $He $Hout] as -
      · ipureintro; exact Hrn rfl
      wp_apply (hTChanges γ.kv trc (.read σ)) $$ [$Htx] as %chs ⟨Htx, %Hchs⟩
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]
        simp only [MTxn.pend, List.length_nil] at Hchs
        word
      wp_apply (end_read hTEnd γ.kv trc σ) $$ [$Htx] as ⟨Htt, Hrdr⟩
      wp_for_post
      iframe
      iexists _, _
      iframe
    · -- a read transaction, with 1 to 3 ranges
      wp_apply wp_traceTODO as %trc ⟨%Htrn, Htrc⟩
      ihave Hau := reader_au hpers hreach _ h γ (sint.nat fl) $$ [$Hkv $Hinv $Hfl]
      wp_apply (hRead γ.kv _ trc true (readQ γ (sint.nat fl))) $$ [$Hkv $Htt $Hrdr $Htrc $Hau]
        as %t0 ⟨Htrc, %σ, Htx, HQ⟩
      · ipureintro; exact Htrn
      iunfold readQ at HQ
      icases HQ with ⟨%Hl, #Hlb, %Hq⟩
      obtain ⟨h1, h2, h3⟩ := seen_ok σ Hl fl Hfl0 Hq
      have hrv : σ.rev + 3 ≤ 2 ^ 63 := by have := Hq.2.2.2.2; unfold MvccState.rev; omega
      icases mvccTxn_shape hsh t0 γ.kv trc (.read σ) $$ Htx with ⟨%Hsh, Htx⟩
      obtain ⟨tyT, vT, rfl, hTRev, hTFirst, hTRange, -, -, -, hTEnd⟩ := Hsh
      wp_apply (hTRev γ.kv trc (.read σ)) $$ [$Htx] as Htx
      simp only [MTxn.state]
      wp_apply (wp_seen h γ.h Hl fl _ _ h1 h2) $$ [$Hrd $Hlb] as Hrd
      wp_apply (wp_snapshot h γ.h Hl) $$ [$Hrd $Hlb] as %s ⟨Hrd, %ms, %Hs, %Hpre, %Hcap, #Hlb', #Hms, #Hst⟩
      wp_apply (hTFirst γ.kv trc (.read σ)) $$ [$Htx] as Htx
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]; rw [Hq.2.2.1]
      wp_apply wp_intn r g3 (W64 3) (by decide) $$ [$Hr] as %y ⟨⟨%g4, Hr⟩, %Hy⟩
      ihave %Hmlen : ⌜ms.length = Hs.length⌝ $$ [Hst]
      · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
      obtain ⟨c0, c1, c2⟩ := check_ok σ Hl Hs ms fl Hq Hpre.1 Hmlen
      ihave #Hctx : mvcc.rangeCtx (GF := GF) true todoCtxVal todoCd $$ []
      · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
      ihave HJ : (∃ (jv : w64) (g5 : rng), "j" ∷ j_ptr ↦ jv ∗ "Hr" ∷ r ↦ g5 : IProp GF) $$ [j Hr]
      · iexists W64 0, g4; iframe
      wp_for HJ
      wp_if_destruct
      · -- a range
        wp_apply (wp_genRange r g5 _ (by rw [h3]; omega) (by rw [h3]; omega)) $$ [$Hr]
          as %q ⟨⟨%g6, Hr⟩, %kk, %e, Hk, Hkc, He, Hec, %Hq'⟩
        ipersist Hk
        ipersist He
        wp_apply wp_ctxTODO
        wp_apply (hTRange γ.kv trc true (.read σ) todoCtxVal todoCd true q.key' q.end' kk e q.ro')
          $$ [$Htx $Htrc $Hctx $Hk $He] as %rr %err ⟨%Hrn, Htx, Htrc, Hout, -, %Hlwf⟩
        ihave Hout := outcome_read rr err σ _ kk e q.ro' Hq.2.2.1 Hq.2.2.2.2 $$ Hout
        ihave Hsts := statesP_statesAt ms Hs $$ Hst
        have hlog := logOk_read σ Hq.2.2.2.2 Hq.2.1 Hlwf
        wp_apply (wp_checkRange s DFrac.discard ms (Hs.map Prod.fst)
          (List.replicate Hs.length DFrac.discard) _ q kk e DFrac.discard DFrac.discard rr err σ.log
          hlog c0 c1 c2) $$ [$Hms $Hsts $Hk $He $Hout] as -
        · ipureintro; exact Hrn rfl
        wp_for_post
        iframe
        iexists _, _
        iframe
      · wp_apply (end_read hTEnd γ.kv trc σ) $$ [$Htx] as ⟨Htt, Hrdr⟩
        wp_for_post
        iframe
        iexists _, _
        iframe
  · iapply HΦ
    iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
