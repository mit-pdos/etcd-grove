/-
Lean-first (no Rocq counterpart).

# lintest: a client's calls of the clock and of the library, under `Run`'s invariant
(2026-10-14)

The two closures a client calls, specified against the ghost log (`linInv`, `Defs.lean`), from
their logically atomic specs (`clockSpec`, `applySpec`): each opens the invariant at its
linearization point (with a later credit, since `libState` and `clockVal` need not be
timeless) and takes the step of `InvLemmas.lean`.

- `wp_clock_read`: a reading `t'` is recorded as the client's last reading, and it is at
  least every `τ` of the client's records and its previous reading.
- `wp_apply_commit`: the operation is linearized when the clock reads `t`, appended to the log
  and to the client's records with `τ = t`, and `t` is at least the client's last reading.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.InvLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {σ : Type}

/-- A clock reading under the invariant (see the file header). -/
theorem wp_clock_read (M : SeqModel σ OpV) (libState : σ → IProp GF)
    (clockVal : w64 → IProp GF) (Eclk : CoPset) (n : Nat) (γ : GName) (clock : GoFunc)
    (c : Nat) (v : ClientV) (HE : (↑lintestN : CoPset) ⊆ ⊤ \ Eclk) :
    {{ clockSpec clockVal Eclk clock ∗ inv lintestN (linInv M libState clockVal n γ) ∗ £ 1 ∗
        clientTok γ c v }}
      (App (Val #clock) (Val #()))
    {{ (t' : w64), RET #t'; clientTok γ c (v.1, t') ∗
        ⌜(∀ p ∈ v.1, sint.Z p.2 ≤ sint.Z t') ∧ sint.Z v.2 ≤ sint.Z t'⌝ }} := by
  iintro %Φ ⟨#Hclk, #Hinv, Hlc, Htok⟩ HΦ
  iunfold clockSpec at Hclk
  iapply Hclk
  inext
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with ⟨%s, %t, %L, %Ls, Hlib, Hcv, Hauth, %Hok⟩
  icombine Hauth Htok gives %Hlook
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists t
  iframe Hcv
  iintro %t' ⟨Hcv, %Hle⟩
  imod Hmask with -
  imod ghost_map_update (v.1, t') $$ Hauth Htok with ⟨Hauth, Htok⟩
  imod Hclose $$ [Hlib Hcv Hauth] with -
  · inext
    iexists s, t', L, _
    iframe
    ipureintro
    exact Hok.read Hlook Hle
  imodintro
  iintro -
  iapply HΦ
  iframe
  ipureintro
  exact ⟨fun p hp => Int.le_trans (Hok.recs_le Hlook hp) Hle, Int.le_trans (Hok.lr_le' Hlook) Hle⟩

/-- A library operation under the invariant (see the file header). -/
theorem wp_apply_commit (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF)
    (libState : σ → IProp GF)
    (clockVal : w64 → IProp GF) (Eapp : CoPset) (n : Nat) (γ : GName) (apply : GoFunc)
    (c : Nat) (v : ClientV) (i : GoInterface) (HE : (↑lintestN : CoPset) ⊆ ⊤ \ Eapp) :
    {{ applySpec S inOk libState Eapp apply ∗ inOk i ∗
        inv lintestN (linInv S.M libState clockVal n γ) ∗ £ 1 ∗ clientTok γ c v }}
      (App (Val #apply) (Val #i))
    {{ (o : GoInterface) (t : w64), RET #o; clientTok γ c (v.1 ++ [((i, o), t)], v.2) ∗
        ⌜sint.Z v.2 ≤ sint.Z t⌝ ∗ S.ioOk i o }} := by
  iintro %Φ ⟨#Happ, Hin, #Hinv, Hlc, Htok⟩ HΦ
  iunfold applySpec at Happ
  iapply Happ $$ %i Hin
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
  iintro Hio
  iapply HΦ
  iframe
  ipureintro
  exact Hok.lr_le' Hlook

end steps

end lintest
end EtcdGrove
end Perennial
