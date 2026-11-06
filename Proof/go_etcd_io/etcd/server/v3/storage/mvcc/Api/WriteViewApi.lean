/-
**`KV.Put` and `KV.DeleteRange`** (M4, track B, 2026-11-06). Lean-first (no Rocq counterpart).
Over the sealed definitions of `Api.lean` (imported with `import all`).

A store's `Put`/`DeleteRange` is its write view's (`writeView.Put`/`DeleteRange`, promoted):
`tw := wv.kv.Write(traceutil.TODO()); defer tw.End(); return tw.Put(...)` (`DeleteRange` likewise),
where `wv.kv` is the store's handle itself (the store, or the watchable store over it). The proof is
over the API's own contracts: `KV.Write.contract` at the handle's type, then `Txn.Put`/`DeleteRange`
and `Txn.End` at the transaction's (`wtxnHyp`: a write transaction's type has them, from `mvccTxn`'s
write arm, `wtxnHyp_holds`). The client's single update (`opAU`, fired at `End`'s notify step) is
split: `Write`'s update peeks at it (`opAU_write`: aborted, keeping the lessor's items at the begin
state, `pendItems σ.log [] = I`), and `End`'s is it (`opAU_end`: at the state the transaction began
at, which `End`'s update fixes, `σ = σ₀`). The hook between: `Write` runs it (`Pre` to `Q'`), the
caller's `Q' ={⊤}=∗ P ∗ Post` gives `End` the lock's invariant back.

At `*watchableStore` the write view is the watchable store's (`isWatchableStore`'s `HwvW`), and
`KV.Write` is `WatchTxnApi.watchableStore.Write.wp_api`'s (under its `wwriterHyp`). At `*store` the
plain handle has no write view yet (track A's handle contents): not here.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.ShapesLaw
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WatchTxnApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WsOpsApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.EndApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapLaws
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- **A one-revision write's update** (`KV.Put`'s and `KV.DeleteRange`'s), at the changes `ds σ` of
the state it fires at. -/
abbrev opAU (γ : MvccName) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (ds : MvccState → List Change) (Q : MvccState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗ ⌜pendItems σ.log [] = I⌝ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ.pending = none⌝ ∗ mvccState γ (σ.notify (ds σ)) ∗ ⧖ (logCh (σ.log ++ [ds σ])), COMM
        AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
          <{ ⌜σ' = σ.notify (ds σ)⌝ ∗ mvccState γ σ'.commitPending, COMM Q σ }> }>)

/-- **`Write`'s update, from the write's** (a peek): aborted at the begin, the write's update kept,
with the lessor's items at the begin state. -/
theorem opAU_write (γ : MvccName) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (ds : MvccState → List Change) (Q : MvccState → IProp GF) :
    opAU (GF := GF) γ I ds Q ⊢
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = none⌝ ∗ mvccState γ σ, COMM opAU γ I ds Q ∗ ⌜pendItems σ.log [] = I⌝ }> := by
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, HAU⟩
  ihave HAC := aupd_aacc $$ HAU
  iunfold atomic_acc at HAC
  unfold atomic_acc
  imod HAC with HAC
  isimp only [texist_cons, texist_nil] at HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  icases HAC with ⟨%σ, Hα, Hcl⟩
  isimp only [Std.Tele.app, ULift.down] at Hα
  icases Hα with ⟨Hst, %Hpi⟩
  imodintro
  iexists σ
  iframe Hst
  isplit
  · iintro Hst
    icases Hcl with ⟨Habort, -⟩
    imod Habort $$ [Hst] with HAU
    · isimp only [Std.Tele.app, ULift.down]
      isplitl [Hst]
      · iexact Hst
      ipureintro; exact Hpi
    imodintro
    iexact HAU
  · iintro ⟨%Hpn, Hst⟩
    icases Hcl with ⟨Habort, -⟩
    imod Habort $$ [Hst] with HAU
    · isimp only [Std.Tele.app, ULift.down]
      isplitl [Hst]
      · iexact Hst
      ipureintro; exact Hpi
    imodintro
    isplitl [HAU]
    · iexact HAU
    ipureintro; exact Hpi

/-- **`End`'s update, from the write's**, at the state the transaction began at (nothing pending
there). -/
theorem opAU_end (γ : MvccName) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (ds : MvccState → List Change) (Q : MvccState → IProp GF) (σ₀ : MvccState)
    (hpn : σ₀.pending = none) :
    opAU (GF := GF) γ I ds Q ⊢
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ = σ₀⌝ ∗ mvccState γ (σ.notify (ds σ₀)) ∗ ⧖ (logCh (σ.log ++ [ds σ₀])), COMM
            AU <{ ∃∃ (σ' : MvccState), mvccState γ σ' }> @ ⊤ \ ↑mvccN, ∅
              <{ ⌜σ' = σ₀.notify (ds σ₀)⌝ ∗ mvccState γ σ'.commitPending, COMM Q σ₀ }> }> := by
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, HAU⟩
  ihave HAC := aupd_aacc $$ HAU
  iunfold atomic_acc at HAC
  unfold atomic_acc
  imod HAC with HAC
  isimp only [texist_cons, texist_nil] at HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  icases HAC with ⟨%σ, Hα, Hcl⟩
  isimp only [Std.Tele.app, ULift.down] at Hα
  icases Hα with ⟨Hst, %Hpi⟩
  imodintro
  iexists σ
  iframe Hst
  isplit
  · iintro Hst
    icases Hcl with ⟨Habort, -⟩
    imod Habort $$ [Hst] with HAU
    · isimp only [Std.Tele.app, ULift.down]
      isplitl [Hst]
      · iexact Hst
      ipureintro; exact Hpi
    imodintro
    iexact HAU
  · iintro ⟨%Heq, Hst, Hrc⟩
    subst Heq
    icases Hcl with ⟨-, Hcommit⟩
    ispecialize Hcommit $$ %Std.Tele.Arg.nil
    imod Hcommit $$ [Hst Hrc] with HΦ
    · isimp only [Std.Tele.app, ULift.down]
      isplitr
      · ipureintro; exact hpn
      isplitl [Hst]
      · iexact Hst
      iexact Hrc
    imodintro
    isimp only [Std.Tele.app, ULift.down] at HΦ
    iexact HΦ

/-- **A write transaction's type has `Put`, `DeleteRange` and `End`'s contracts** (the hypothesis
`writeView_Put_api`/`_DeleteRange_api` take; `wtxnHyp_holds`). -/
abbrev wtxnHyp : Prop :=
  ∀ (t : GoInterface) (γ : MvccName) (trace : Loc) (σ : MvccState) (pend : List Change),
    mvccTxn (GF := GF) t γ trace (.write σ pend) ⊢
      ⌜∃ (ty : go.GoType) (v : val), t = interface.mkOk ty v ∧ Txn.Put.contract (GF := GF) ty v ∧
        Txn.DeleteRange.contract (GF := GF) ty v ∧ Txn.End.contract (GF := GF) ty v⌝

/-- `wtxnHyp`, from the contracts at the two write transactions' types (`wrWrap_ty`). -/
theorem wtxnHyp_holds
    (hPM : ∀ t : Loc, Txn.Put.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t)
    (hDM : ∀ t : Loc, Txn.DeleteRange.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t)
    (hEM : ∀ t : Loc, Txn.End.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t)
    (hPT : ∀ t : Loc,
      Txn.Put.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t)
    (hDT : ∀ t : Loc,
      Txn.DeleteRange.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t)
    (hET : ∀ t : Loc,
      Txn.End.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t) :
    wtxnHyp (GF := GF) := by
  intro t γ trace σ pend
  iintro Htx
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
  ihave %h := wrWrap_ty t _ s mw σ.log $$ Hwrap
  ipureintro
  obtain ⟨l, h | h⟩ := h <;> subst h
  · exact ⟨_, _, rfl, hPM l, hDM l, hEM l⟩
  · exact ⟨_, _, rfl, hPT l, hDT l, hET l⟩

/-- A write transaction began with nothing pending. -/
theorem mvccTxn_write_pending (t : GoInterface) (γ : MvccName) (trace : Loc) (σ : MvccState)
    (pend : List Change) :
    mvccTxn (GF := GF) t γ trace (.write σ pend) ⊢ ⌜σ.pending = none⌝ := by
  iintro Htx
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, -⟩
  ipureintro; exact Hk0.1

/-- **A write view's `Put`, by the caller's update** (see the header), its `kv` the handle `kty kv`
whose `Write` meets its contract. -/
theorem writeView_Put_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (kty : go.GoType) (kv : val) (hW : KV.Write.contract (GF := GF) kty kv)
    (hTx : wtxnHyp (GF := GF))
    (wv : Loc) (γ : MvccName) (key value : GoSlice) (k vv : GoString) (leaseID : w64) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (q : Qp) (B : MvccStorage)
    (P Pre Q' Post : IProp GF) (f : GoFunc) (Q : MvccState → IProp GF) :
    {{ pkgInit ∗ wv.[writeView, go!"kv"] ↦□ (interface.mkOk kty kv : GoInterface) ∗
        isMvcc (interface.mkOk kty kv) γ ∗ threadTok ∗ key ↦*□ k ∗ value ↦*□ vv ∗
        ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗
        lease.leaseOwn (mvccLeases γ) L I ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ ∗
        mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
        opAU γ I (fun _ => [.put k vv leaseID]) Q }}
      (App (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"Put")) (Val #key))
        (Val #value)) (Val #leaseID))
    {{ (rev : w64), RET #rev; threadTok ∗ mvccBackend γ q B P ∗ Post ∗ ∃ σ : MvccState, Q σ ∗
        lease.leaseOwn (mvccLeases γ) L (pendItems σ.log [.put k vv leaseID]) ∗
        ⌜rev = W64 (σ.log.length : Int)⌝ }} := by
  wp_start as ⟨#Hkv, #Hmv, Htok, #Hkey, #Hval, %Hklen, Hown, %Hlease, HB, #Hhk, Hpre, Hrun, Hupd,
    Hau⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  ihave Hwau := opAU_write γ I (fun _ => [.put k vv leaseID]) Q $$ Hau
  -- `wv.kv.Write(t)`: the client's update peeked at
  wp_apply (hW γ t true q B P Pre Q' f
      (fun σ => iprop(opAU γ I (fun _ => [.put k vv leaseID]) Q ∗ ⌜pendItems σ.log [] = I⌝)))
      $$ [Htok Htrc HB Hpre Hrun Hwau]
    as %tw ⟨Htrc, HB, ⟨%σ, Htx, Hau, %Hpi⟩, HQ'⟩
  · iframe Hmv Htok Htrc HB Hhk Hpre Hrun Hwau
    ipureintro; exact Ht
  ihave %Hty := hTx tw γ t σ [] $$ [$Htx]
  obtain ⟨ty, v, rfl, hPut, -, hEnd⟩ := Hty
  ihave %Hpn := mvccTxn_write_pending _ γ t σ [] $$ [$Htx]
  subst Hpi
  (try wp_auto)
  -- `tw.Put(key, value, lease)`
  wp_apply (hPut γ t true σ [] key value k vv leaseID L) $$ [Htx Htrc Hown]
    as ⟨Htx, Htrc, Hown⟩
  · iframe Htx Htrc Hkey Hval Hown
    ipureintro; exact ⟨Hklen, Hlease⟩
  (try wp_auto)
  -- the deferred `tw.End()`: the client's update, at the begin state
  rw [List.nil_append] at *
  imod Hupd $$ HQ' with ⟨HP, HPost⟩
  ihave Heau := opAU_end γ (pendItems σ.log []) (fun _ => [.put k vv leaseID]) Q σ Hpn $$ Hau
  wp_apply (hEnd γ t (.write σ [.put k vv leaseID]) q B P (Q σ)) $$ [Htx HB HP Heau]
    as ⟨Htok, HB, HQ⟩
  · dsimp only
    iframe Htx HB HP Heau
  (try wp_auto)
  iapply HΦ
  iframe Htok HB HPost
  iexists σ
  iframe HQ Hown
  ipureintro; rfl

/-- **A write view's `DeleteRange`, by the caller's update** (as `writeView_Put_api`). -/
theorem writeView_DeleteRange_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (kty : go.GoType) (kv : val) (hW : KV.Write.contract (GF := GF) kty kv)
    (hTx : wtxnHyp (GF := GF))
    (wv : Loc) (γ : MvccName) (key endk : GoSlice) (k e : GoString) (L : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (q : Qp) (B : MvccStorage)
    (P Pre Q' Post : IProp GF) (f : GoFunc) (Q : MvccState → IProp GF) :
    let ds (σ : MvccState) := (delKeys σ.log [] (decide (endk = slice.nil)) k e).map Change.del
    {{ pkgInit ∗ wv.[writeView, go!"kv"] ↦□ (interface.mkOk kty kv : GoInterface) ∗
        isMvcc (interface.mkOk kty kv) γ ∗ threadTok ∗ key ↦*□ k ∗ endk ↦*□ e ∗
        lease.leaseOwn (mvccLeases γ) L I ∗
        mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
        opAU γ I ds Q }}
      (App (App (Val (wv @!! go.GoType.PointerType writeView.ty @!! go!"DeleteRange")) (Val #key))
        (Val #endk))
    {{ (n rev : w64), RET (PairV #n #rev); threadTok ∗ mvccBackend γ q B P ∗ Post ∗
        ∃ σ : MvccState, Q σ ∗ lease.leaseOwn (mvccLeases γ) L (pendItems σ.log (ds σ)) ∗
        ⌜n = W64 ((ds σ).length : Int) ∧ rev = W64 ((writeRev σ.log (ds σ) : Nat) : Int)⌝ }} := by
  intro ds
  wp_start as ⟨#Hkv, #Hmv, Htok, #Hkey, #Hend, Hown, HB, #Hhk, Hpre, Hrun, Hupd, Hau⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  ihave Hwau := opAU_write γ I ds Q $$ Hau
  -- `wv.kv.Write(t)`: the client's update peeked at
  wp_apply (hW γ t true q B P Pre Q' f
      (fun σ => iprop(opAU γ I ds Q ∗ ⌜pendItems σ.log [] = I⌝)))
      $$ [Htok Htrc HB Hpre Hrun Hwau]
    as %tw ⟨Htrc, HB, ⟨%σ, Htx, Hau, %Hpi⟩, HQ'⟩
  · iframe Hmv Htok Htrc HB Hhk Hpre Hrun Hwau
    ipureintro; exact Ht
  ihave %Hty := hTx tw γ t σ [] $$ [$Htx]
  obtain ⟨ty, v, rfl, -, hDel, hEnd⟩ := Hty
  ihave %Hpn := mvccTxn_write_pending _ γ t σ [] $$ [$Htx]
  subst Hpi
  (try wp_auto)
  -- `tw.DeleteRange(key, end)`
  wp_apply (hDel γ t σ [] key endk k e L) $$ [Htx Hown]
    as %n %rev ⟨Htx, Hown, %Hnr, -⟩
  · iframe Htx Hkey Hend Hown
  (try wp_auto)
  -- the deferred `tw.End()`: the client's update, at the begin state
  rw [List.nil_append] at *
  imod Hupd $$ HQ' with ⟨HP, HPost⟩
  ihave Heau := opAU_end γ (pendItems σ.log []) ds Q σ Hpn $$ Hau
  wp_apply (hEnd γ t (.write σ (ds σ)) q B P (Q σ)) $$ [Htx HB HP Heau]
    as ⟨Htok, HB, HQ⟩
  · dsimp only
    iframe Htx HB HP Heau
  (try wp_auto)
  iapply HΦ
  iframe Htok HB HPost
  iexists σ
  iframe HQ Hown
  ipureintro; exact Hnr

/-- The watchable handle's inner store's write view (over the watchable store). -/
theorem watchable_writeView (s st : Loc) (γw : WsNames) :
    isWatchableStore (GF := GF) s st γw ⊢ ∃ wv : Loc,
      st.[store, go!"WriteView"] ↦□
        (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
      wv.[writeView, go!"kv"] ↦□
        (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s : GoInterface) := by
  iintro #Hws
  iunfold isWatchableStore at Hws
  iNamed Hws
  iexact HwvW

/-- The watchable handle: its store and inner store. -/
private theorem isMvcc_watchable (s : Loc) (γ : MvccName) :
    isMvcc (GF := GF) (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s) γ ⊢
      ∃ (st : Loc) (γw : WsNames), ⌜γw.st = (γ : StoreNames)⌝ ∗ isWatchableStore s st γw := by
  iintro #Hmv
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -⟩
    exfalso
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, #Hws, -⟩
  obtain ⟨Hk, hγ⟩ := Hk
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs
  iexists st, γw
  iframe Hws
  ipureintro; exact hγ

/-- **`KV.Put.contract` at `*watchableStore`**, over its `KV.Write` (`wwriterHyp`, as
`watchableStore.Write.wp_api`). -/
theorem watchableStore.Put.wp_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hW : watchableStore.Write.spec (GF := GF))
    (hTx : wtxnHyp (GF := GF)) :
    watchableStore.Put.spec (GF := GF) := by
  intro s γ key value k vv leaseID L I q B P Pre Q' Post f Q
  wp_start as ⟨#Hmv, Htok, #Hkey, #Hval, %Hklen, Hown, %Hlease, HB, #Hhk, Hpre, Hrun, Hupd, Hau⟩
  icases isMvcc_watchable s γ $$ Hmv with ⟨%st, %γw, %hγ, #Hws⟩
  icases watchable_writeView s st γw $$ Hws with ⟨%wv, #HWV, #Hwvkv⟩
  ihave #Hws' := Hws
  iunfold isWatchableStore at Hws'
  iNamed Hws'
  (try wp_auto)
  wp_method_call; wp_call
  (try wp_auto)
  wp_apply (writeView_Put_api hTODO _ _ (hW s) hTx wv γ key value k vv leaseID L I q B P Pre Q' Post
      f Q) $$ [Htok Hown HB Hpre Hrun Hupd Hau] as %rev Hr
  · iframe Hwvkv Hmv Htok Hkey Hval Hown HB Hhk Hpre Hrun Hupd Hau
    ipureintro; exact ⟨Hklen, Hlease⟩
  iapply HΦ; iexact Hr

/-- **`KV.DeleteRange.contract` at `*watchableStore`** (as `Put`). -/
theorem watchableStore.DeleteRange.wp_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hW : watchableStore.Write.spec (GF := GF))
    (hTx : wtxnHyp (GF := GF)) :
    watchableStore.DeleteRange.spec (GF := GF) := by
  intro s γ key endk k e L I q B P Pre Q' Post f Q
  wp_start as ⟨#Hmv, Htok, #Hkey, #Hend, Hown, HB, #Hhk, Hpre, Hrun, Hupd, Hau⟩
  icases isMvcc_watchable s γ $$ Hmv with ⟨%st, %γw, %hγ, #Hws⟩
  icases watchable_writeView s st γw $$ Hws with ⟨%wv, #HWV, #Hwvkv⟩
  ihave #Hws' := Hws
  iunfold isWatchableStore at Hws'
  iNamed Hws'
  (try wp_auto)
  wp_method_call; wp_call
  (try wp_auto)
  wp_apply (writeView_DeleteRange_api hTODO _ _ (hW s) hTx wv γ key endk k e L I q B P Pre Q' Post
      f Q) $$ [Htok Hown HB Hpre Hrun Hupd Hau] as %n %rev Hr
  · iframe Hwvkv Hmv Htok Hkey Hend Hown HB Hhk Hpre Hrun Hupd Hau
  iapply HΦ; iexact Hr

/-- **The plain handle's write view** (track A, request 3: the write view in `isMvccPlain`): its
`kv` the store itself. -/
private theorem isMvcc_plainW (s : Loc) (γ : MvccName) :
    isMvcc (GF := GF) (interface.mkOk (go.GoType.PointerType store.ty) #s) γ ⊢
      ∃ wv : Loc, s.[store, go!"WriteView"] ↦□
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        wv.[writeView, go!"kv"] ↦□
          (interface.mkOk (go.GoType.PointerType store.ty) #s : GoInterface) := by
  iintro Hmv
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, -⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -, -, -, -, -, ⟨%rv, %wv, -, -, #Hwv, #HwvI⟩⟩
    have hs : s = s' := mkOk_loc_inj _ Hk
    subst hs
    iunfold isWriteView at HwvI
    iNamed HwvI
    iexists wv
    iframe Hwv Hkv
  iunfold isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, -⟩
  exfalso
  obtain ⟨Hk, -⟩ := Hk
  rw [interface_mkOk_inj] at Hk
  exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])

/-- **`KV.Put.contract` at `*store`**, over its `KV.Write` (`store.Write.wp_api`, no hypothesis). -/
theorem store.Put.wp_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hW : store.Write.spec (GF := GF))
    (hTx : wtxnHyp (GF := GF)) :
    store.Put.spec (GF := GF) := by
  intro s γ key value k vv leaseID L I q B P Pre Q' Post f Q
  wp_start as ⟨#Hmv, Htok, #Hkey, #Hval, %Hklen, Hown, %Hlease, HB, #Hhk, Hpre, Hrun, Hupd, Hau⟩
  icases isMvcc_plainW s γ $$ Hmv with ⟨%wv, #HWV, #Hwvkv⟩
  (try wp_auto)
  wp_apply (writeView_Put_api hTODO _ _ (hW s) hTx wv γ key value k vv leaseID L I q B P Pre Q' Post
      f Q) $$ [Htok Hown HB Hpre Hrun Hupd Hau] as %rev Hr
  · iframe Hwvkv Hmv Htok Hkey Hval Hown HB Hhk Hpre Hrun Hupd Hau
    ipureintro; exact ⟨Hklen, Hlease⟩
  iapply HΦ; iexact Hr

/-- **`KV.DeleteRange.contract` at `*store`** (as `Put`). -/
theorem store.DeleteRange.wp_api (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hW : store.Write.spec (GF := GF))
    (hTx : wtxnHyp (GF := GF)) :
    store.DeleteRange.spec (GF := GF) := by
  intro s γ key endk k e L I q B P Pre Q' Post f Q
  wp_start as ⟨#Hmv, Htok, #Hkey, #Hend, Hown, HB, #Hhk, Hpre, Hrun, Hupd, Hau⟩
  icases isMvcc_plainW s γ $$ Hmv with ⟨%wv, #HWV, #Hwvkv⟩
  (try wp_auto)
  wp_apply (writeView_DeleteRange_api hTODO _ _ (hW s) hTx wv γ key endk k e L I q B P Pre Q' Post
      f Q) $$ [Htok Hown HB Hpre Hrun Hupd Hau] as %n %rev Hr
  · iframe Hwvkv Hmv Htok Hkey Hend Hown HB Hhk Hpre Hrun Hupd Hau
  iapply HΦ; iexact Hr

end proof

end api
end mvcc
end EtcdGrove
end Perennial
