/-
**`KV.Write.contract` at `*store`** (M4, track B, 2026-11-06). Lean-first (no Rocq counterpart). Over
the sealed definitions of `Api.lean` (imported with `import all`).

**The writer's resources from the handle** (track A, request 3, 2026-11-06; until then the
hypothesis `writerHyp`): the reader from the handle's readers' supply (`rdSupply_lendL`, under a
later, which `store.Write`'s first step strips), the certificate map's free entry and that the store
has no watchers (`isMvcc`'s plain disjunct), the write-back supply (`mvccBackend`'s, at the share's
physical names); the revision token and the pin are the writer's state's (`wrState`, `wrPin`), so
`store.Write` takes nothing of them from its caller.

The proof: the handle's store, the backend share at its current names `p` (its objects' share pins
the names for `store.Write`, its token excludes the frozen state, `slotF_share_excl`), the hook's
context by the frozen hook's state (`writeCtxM`: `hookRun`'s two arms), the begin's step from the
client's update by agreement with the writer's slot (`writeCb`: the state's log and compaction
revision are the slot's, nothing pending), and the transaction `mvccTxnI` without its trace.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.EndSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Instance
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write

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

/-- The begin's step, from the client's update (see the header). -/
theorem writeCb_of_au (γ : StoreNames) (p : PhysNames) (R : MvccState → IProp GF) :
    iprop(AU <{ ∃∃ (σ : MvccState), mvccStateI γ.api σ }> @ ⊤ \ ↑mvccN, ∅
        <{ ⌜σ.pending = none⌝ ∗ mvccStateI γ.api σ, COMM R σ }>) ⊢
      writeCb (γ.withPhys p) (fun L c => iprop(∃ σ : MvccState, R σ ∗
        ⌜σ.log = L ∧ σ.crev = c ∧ σ.pending = none ∧ MvccReachable σ⌝)) := by
  iintro Hau
  iunfold writeCb
  simp only [StoreNames.withPhys_api]
  iintro %L %c ⟨Ha, Hp⟩
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
  icases Hσ with ⟨Ha', Hp', Hcr, Hnl, %Hreach, #Hrcm⟩
  ihave %Hag := absPart_agree _ _ _ _ _ _ _ $$ [Ha' Ha]
  · iframe Ha' Ha
  ihave %Hpg := pndPart_agree _ _ _ _ _ $$ [Hp' Hp]
  · iframe Hp' Hp
  imod Hcommit $$ [Ha' Hp' Hcr Hnl] with HR
  · isplitr
    · ipureintro; exact Hpg
    iunfold mvccStateI
    iframe Ha' Hp' Hcr Hnl
    iframe Hrcm; ipureintro; exact Hreach
  imodintro
  iframe Ha Hp
  iexists σ
  iframe HR
  ipureintro; exact ⟨Hag.1, Hag.2, Hpg, Hreach⟩

/-- **`KV.Write.contract` at `*store`.** -/
theorem store.Write.wp_api (hW : mvcc.store.Write.spec (GF := GF) (hG := hG)) :
    store.Write.spec (GF := GF) := by
  intro s (γ : mvcc.StoreNames) trace te q B P Pre Q f R
  iintro %Φ ⟨#Hpkg, Hmv, Htok, %Htrnn, Htrc, HB, #Hhk, Hpre, Hrun, Hau⟩ HΦ
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
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, -, #Hsup, #Hfree, -⟩
  have hs : s = s' := mkOk_loc_inj _ Hk
  subst hs
  -- the backend share at the store's current names
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p, %o, %d, Hcur, %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, hdB⟩ := Hd
  subst hdB
  rw [show (hookIs d f : IProp GF) = backend.plHookRO d.γB f from rfl] at *
  -- the writer's resources: the reader from the handle's supply, the write-back supply the share's,
  -- the token and the pin the writer's state's (a store without watchers)
  imod mvcc.rdSupply_lendL s γ $$ [$Hsup $Htok] with ⟨Hrd, Hback⟩
  ihave Hrd : ▷ storeReaderC (GF := GF) s (γ.withPhys p) $$ [Hrd]
  · rw [storeReaderC_withPhys]; iexact Hrd
  ihave Hback : tokBack (GF := GF) s (γ.withPhys p) $$ [Hback]
  · rw [show tokBack (GF := GF) s (γ.withPhys p) = tokBack s γ from rfl]; iexact Hback
  ihave #Hfree' : certFree (GF := GF) (γ.withPhys p) $$ []
  · rw [show certFree (GF := GF) (γ.withPhys p) = certFree γ from rfl]; iexact Hfree
  ihave Hwt : (storeWT (GF := GF) (γ.withPhys p) ∨ □ (⧗ 1 ={⊤}=∗ storeWT (γ.withPhys p))) $$ []
  · iright; iexact Hwts
  imod crevLb_neg (γ.withPhys p).idx with #Hlb
  -- the hook's context, by the frozen hook's state
  ihave ⟨%hk, %dq, Hctx⟩ : (∃ (hk : Option val) (dq : DFrac),
      writeCtxM (GF := GF) (γ.withPhys p) P hk Pre Q dq) $$ [Hpre Hrun]
  · by_cases hf : f = func.nil
    · iexists none, DFrac.discard
      rw [writeCtxM_none]
      iunfold hookRun at Hrun
      simp only [hf, ↓reduceIte]
      iframe Hhp Hpre Hrun
      rw [StoreNames.withPhys_kb, hpk]
      iunfold kbHookNilAt
      rw [← hf]; iexact Hhk
    · iexists (some #f), DFrac.discard
      rw [writeCtxM_some]
      iunfold hookRun at Hrun
      simp only [hf, ↓reduceIte]
      icases Hrun with #Hrun
      iframe Hpre Hrun
      iunfold hookOk
      iframe Hhp
      iunfold hookFn
      rw [StoreNames.withPhys_kb, hpk]
      iunfold kbHookIs
      iunfold bkHookIs
      iexists f
      iframe Hhk
      ipureintro; exact ⟨rfl, hf⟩
  -- the begin's step, from the client's update
  iunfold mvccState at Hau
  ihave Hcb := writeCb_of_au γ p R $$ Hau
  ihave #Hx : □ (slotF (γ.withPhys p) ∗ api.shareTok γ.api q -∗ False) $$ []
  · iintro !> H
    iapply (slotF_share_excl (γ := γ.withPhys p) (a := γ.api) rfl q) $$ H
  ihave #HZ : □ (iprop(True) : IProp GF) $$ []
  · iintro !>; itrivial
  iapply (hW s (γ.withPhys p) trace P Pre Q hk dq te (-1) iprop(True) _ o
      (api.shareTok γ.api q) _) $$ [Hrd Hwt Hctx Hcur HF Hcb Htrc] [HΦ Hback]
  · rw [isStore_withPhys]
    iframe Hpkg Hs Hrd Hwt Hctx Hcur HF Hcb Htrc Hx HZ Hlb
    ipureintro; exact Htrnn
  inext
  iintro %mw ⟨⟨%ilog, %crev, Htx, -, -, -, ⟨%σ, HR, %Hσ⟩⟩, Htrc, HQ, -, Hcur, HF⟩
  obtain ⟨hl, hc, hpn, hre⟩ := Hσ
  subst hl hc
  iapply HΦ
  iframe Htrc HQ
  isplitl [HF Hcur]
  · iunfold mvccBackend
    iframe HF
    iexists p, o, d
    iframe Hcur Hbk Hrg Hhp Hwts
    ipureintro; exact ⟨⟨hpk, hcm, rfl⟩, Hlp⟩
  iexists σ
  iframe HR
  iunfold mvccTxn
  simp only [mvccTxnI]
  iexists mw, s, p, (W64 0), (W64 0), (W64 0)
  iframe Htx Hback Hfree'
  isplitr
  · ipureintro; exact ⟨hpn, hre⟩
  iunfold wrWrap; ileft; ipureintro; exact ⟨rfl, by simpa using Hwq⟩

end proof

end api
end mvcc
end EtcdGrove
end Perennial
