/-
Lean-first (no Rocq counterpart).

# lintest/logkvrw: the driver's library spec with a thread token (2026-10-28)

A **local workaround** (`notes/logkv-eval-rw.md`): logkvrw's `Get` takes the read lock of an
`RWMutex`, which needs one of the lock's bounded reader tokens; Perennial lends them to live
threads through a thread pool (`Perennial/Proof/sync/RWMutexThreads.lean`), paid for with the
caller's thread token (`threadTok`). The driver's `applySpec` (`Proof/.../lintest/Defs.lean`)
gives the library no resource, so no implementation that needs a reader slot can meet it.

`applySpecTok` is `applySpec` with the calling goroutine's thread token in the precondition and
given back in the postcondition: every `apply` call of the driver runs on a goroutine of its own
(`Run`'s clients), which owns its token. It is weaker as a requirement on the library (an
`applySpec` gives an `applySpecTok` by framing), so a `Run` spec over it is stronger. The change
belongs in `lintest`'s `applySpec` itself; this package's copies (`RunTok`, `runClientTok`) prove
`Run` and `runClient` over it until then.

- `wp_apply_commit_tok`: `ClientSteps.lean`'s `wp_apply_commit`, the thread token passed through.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.ClientSteps

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {σ : Type}

/-- A library operation, logically atomic against the model, called with the calling
goroutine's thread token, which it gives back (see the file header). -/
def applySpecTok (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF) (libState : σ → IProp GF)
    (Eapp : CoPset) (f : GoFunc) : IProp GF :=
  iprop(∀ i : GoInterface,
    {{ inOk i ∗ threadTok }} <<{ ∀∀ s, libState s }>> (App (Val #f) (Val #i)) @@ Eapp
    <<{ ∃∃ s' o, libState s' ∗ ⌜S.M.step s (i, o) = some s'⌝ }>>
    {{ RET #o; S.ioOk i o ∗ threadTok }})

instance applySpecTok_persistent (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF)
    (libState : σ → IProp GF) (Eapp : CoPset) (f : GoFunc) :
    Persistent (applySpecTok S inOk libState Eapp f) := by
  unfold applySpecTok; infer_instance

end defs

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {σ : Type}

/-- `wp_apply_commit` over `applySpecTok`: the thread token passed through. -/
theorem wp_apply_commit_tok (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF)
    (libState : σ → IProp GF)
    (clockVal : w64 → IProp GF) (Eapp : CoPset) (n : Nat) (γ : GName) (apply : GoFunc)
    (c : Nat) (v : ClientV) (i : GoInterface) (HE : (↑lintestN : CoPset) ⊆ ⊤ \ Eapp) :
    {{ applySpecTok S inOk libState Eapp apply ∗ inOk i ∗ threadTok ∗
        inv lintestN (linInv S.M libState clockVal n γ) ∗ £ 1 ∗ clientTok γ c v }}
      (App (Val #apply) (Val #i))
    {{ (o : GoInterface) (t : w64), RET #o; clientTok γ c (v.1 ++ [((i, o), t)], v.2) ∗
        ⌜sint.Z v.2 ≤ sint.Z t⌝ ∗ S.ioOk i o ∗ threadTok }} := by
  iintro %Φ ⟨#Happ, Hin, Htt, #Hinv, Hlc, Htok⟩ HΦ
  iunfold applySpecTok at Happ
  iapply Happ $$ %i [Hin Htt]
  · iframe
  inext
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%s, %t, %L, %Ls, Hlib, Hcv, Hauth, %Hok⟩
  icombine Hauth Htok gives %Hlook
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists s
  iframe Hlib
  iintro %s' %o ⟨Hlib, %Hstep⟩
  imod Hmask with -
  imod ghost_map_update (v.1 ++ [((i, o), t)], v.2) $$ Hauth Htok with ⟨Hauth, Htok⟩
  imod Hclose $$ [Hlib Hcv Hauth] with -
  · inext
    iexists s', t, L ++ [⟨c, v.1.length, (i, o), sint.Z t⟩], _
    iframe
    ipureintro
    exact Hok.commit Hlook Hstep
  imodintro
  iintro ⟨Hio, Htt⟩
  iapply HΦ
  iframe
  ipureintro
  exact Hok.lr_le' Hlook

end steps

end logkvrw
end lintest
end EtcdGrove
end Perennial
