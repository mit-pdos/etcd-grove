/-
Lean-first (no Rocq counterpart).

# lintest/perclient: a client's call of the library, under `Run`'s invariant (2026-11-22)

lintest's `wp_apply_commit` (`lintest/ClientSteps.lean`) for a library told its client's index
(`applySpecId`): client `id`'s call `apply(id, i)`, for `0 ≤ id < clients`, is linearized when the
clock reads `t`, appended to the log and to the client's records with `τ = t`; when the library
returns an output `o'` other than the committed one, the record and its log entry take `o'`. The
clock's reading is lintest's `wp_clock_read`, used as is.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.InvLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace perclient

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open lintest

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {σ : Type}

/-- Client `id`'s library operation under the invariant (see the file header). -/
theorem wp_apply_commit_id (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF)
    (libState : σ → IProp GF) (P : Nat → IProp GF)
    (clockVal : w64 → IProp GF) (Eapp : CoPset) (n : Nat) (γ : GName) (apply : GoFunc)
    (clients id : w64) (c : Nat) (v : ClientV) (i : GoInterface)
    (HE : (↑lintestN : CoPset) ⊆ ⊤ \ Eapp) (Hid : 0 ≤ sint.Z id ∧ sint.Z id < sint.Z clients) :
    {{ applySpecId S inOk libState Eapp clients P apply ∗ inOk i ∗ threadTok ∗ P (sint.nat id) ∗
        inv lintestN (linInv S.M libState clockVal n γ) ∗ £ 1 ∗ £ 1 ∗ clientTok γ c v }}
      (App (App (Val #apply) (Val #id)) (Val #i))
    {{ (o : GoInterface) (t : w64), RET #o; clientTok γ c (v.1 ++ [((i, o), t)], v.2) ∗
        ⌜sint.Z v.2 ≤ sint.Z t⌝ ∗ S.ioOk i o ∗ threadTok }} := by
  iintro %Φ ⟨#Happ, Hin, Htt, HP, #Hinv, Hlc, Hlc', Htok⟩ HΦ
  iunfold applySpecId at Happ
  iapply wp_fupd
  iapply Happ $$ %id %i [Hin Htt HP]
  · iframe
    ipureintro; exact Hid
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
  iintro %o' ⟨%Heq, Hio, Htt⟩
  -- the record takes the returned output
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc' Hi with Hi
  icases Hi with ⟨%s2, %t2, %L2, %Ls2, Hlib, Hcv, Hauth, %Hok2⟩
  icombine Hauth Htok gives %Hlook2
  imod ghost_map_update (v.1 ++ [((i, o'), t)], v.2) $$ Hauth Htok with ⟨Hauth, Htok⟩
  imod Hclose $$ [Hlib Hcv Hauth] with -
  · inext
    iexists s2, t2, L2.map (swapRec c v.1.length (i, o')), _
    iframe
    ipureintro
    exact Hok2.swap Hlook2 Heq
  imodintro
  iapply HΦ
  iframe
  ipureintro
  exact Hok.lr_le' Hlook

end steps

end perclient
end EtcdGrove
end Perennial
