/-
**`KV.Read.contract` at `*store`** (M4, track B, 2026-11-06). Lean-first (no Rocq counterpart). Over
the sealed definitions of `Api.lean` (imported with `import all`).

**Conditional on track A's readers' pool** (`readerHyp`, a hypothesis of the theorem, not an axiom):
a plain handle does not yet hold the readers' pool, here a thread token turned into a reader of the
store with its way back (`tokBack`). The read's update fires under `s.revMu` (§3) by agreement with
the lock's slot (`readCbC`: the state's log and compaction revision are the slot's, which are the
transaction's), and the transaction is `mvccTxnI`'s read arm, without its trace.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.EndSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read

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

/-- **The hypothesis**: a plain handle's store lends a reader for a thread token (track A's readers'
pool; see the header). -/
abbrev readerHyp : Prop :=
  ∀ (s : Loc) (γ : StoreNames),
    isStore (GF := GF) s γ ∗ api.locIs γ.api s ⊢ |={⊤}=>
      (threadTok ={⊤}=∗ storeReaderC s γ ∗ tokBack s γ)

/-- The read's step, from the client's update (see the header). -/
theorem readCbC_of_au (γ : StoreNames) (Q : MvccState → IProp GF) :
    iprop(AU <{ ∃∃ (σ : MvccState), mvccStateI γ.api σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccStateI γ.api σ, COMM Q σ }>) ⊢
      readCbC γ (fun L c => iprop(∃ σ : MvccState, Q σ ∗
        ⌜σ.log = L ∧ σ.crev = c ∧ MvccReachable σ⌝)) := by
  iintro Hau
  iunfold readCbC
  iintro %q %L %c HX
  iunfold slotX at HX
  iunfold revMuAbs at HX
  icases HX with ⟨Ha, Hc⟩
  ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤)
    (fun _ _ => CoPset.mem_full) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, Hσ, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  iunfold mvccStateI at Hσ
  icases Hσ with ⟨Ha', Hp', Hcr, Hnl, %Hreach⟩
  ihave %Hag := absPart_agree _ _ _ _ _ _ _ $$ [Ha' Ha]
  · iframe Ha' Ha
  imod Hcommit $$ [Ha' Hp' Hcr Hnl] with HQ
  · iunfold mvccStateI
    iframe Ha' Hp' Hcr Hnl
    ipureintro; exact Hreach
  imodintro
  isplitl [Ha Hc]
  · iunfold slotX; iunfold revMuAbs; iframe Ha Hc
  iexists σ
  iframe HQ
  ipureintro; exact ⟨Hag.1, Hag.2, Hreach⟩

/-- **`KV.Read.contract` at `*store`**, under `readerHyp`. -/
theorem store.Read.wp_api (hR : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hres : readerHyp (GF := GF)) :
    store.Read.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) mode trace te Q
  iintro %Φ ⟨#Hpkg, Hmv, Htok, %Htrnn, Htrc, Hau⟩ HΦ
  -- the handle: a plain store
  iunfold isMvcc at Hmv
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  rotate_left 1
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, -⟩
    exfalso
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccPlain at Hmv
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, -⟩
  have hs : s = s' := mkOk_loc_inj _ Hk
  subst hs
  imod hres s γ $$ [Hs Hloc] with Hpool
  · iframe Hs Hloc
  imod Hpool $$ Htok with ⟨Hrd, Hback⟩
  imod crevLb_neg γ.idx with #Hlb
  imod ownToks_0 (GF := GF) γ.revs with Hnone
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  iunfold mvccState at Hau
  ihave Hcb := readCbC_of_au γ Q $$ Hau
  ihave #HZ : □ (iprop(True) : IProp GF) $$ []
  · iintro !>; itrivial
  ihave Hla : logLent (GF := GF) γ.idx none $$ []
  · unfold logLent; itrivial
  iapply (hR s γ mode trace 0 [[], []] te (-1) iprop(True) none _) $$ [Hrd Hnone Htrc Hla Hcb] [HΦ Hback]
  · iframe Hpkg Hs Hrd Hnone Htrc Hla Hcb HZ Hc0 Hlb
    ipureintro; exact Htrnn
  inext
  iintro %mw ⟨%log, %rev, %crev, Htx, Htrc, -, -, -, -, %Hpre0, -, -, ⟨%σ, HQ, %Hσ⟩⟩
  obtain ⟨hl, hc, hre⟩ := Hσ
  subst hl hc
  -- the transaction's revision is its log's last
  icases isTxnReadT_rev _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, %Hrev⟩
  subst Hrev
  iapply HΦ
  iframe Htrc
  iexists σ
  iframe HQ
  iunfold mvccTxn
  simp only [mvccTxnI]
  iexists mw, s, 0
  iframe Htx Hback
  isplitr
  · ipureintro; exact hre
  iapply roWrap_zero

end proof

end api
end mvcc
end EtcdGrove
end Perennial
