/-
**The KV invariant fixes the auth layer off** (the auth plan's E2p, 2026-10-26; `notes/decisions.md`,
"E2p of the auth plan"): `kvInv` keeps `γk.ch0 = alarmChain false false false`, so a caller that
also takes `γk.ch0 = alarmChain true false false` (`NewServer.specM true`'s premise, with
`kvInv` in its precondition) has an unsatisfiable precondition: `server_new_auth_on` is vacuous
until the KV invariant is stated for the mode `on`. Kept as a check of that finding; it goes when
the KV invariant takes the mode.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The KV invariant's start chain has the auth layer off.** -/
theorem kvInv_ch0_off (γ : ServerRaftNames) (γk : KVNames) :
    ⊢ kvInv (GF := GF) γ γk ={⊤}=∗ ⌜γk.ch0 = apply.alarmChain false false false⌝ := by
  iintro #Hinv
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  exact Hok.2.2.2.1

/-- **`NewServer.specM true`'s precondition is unsatisfiable**: its `kvInv` and its premise on the
start chain (`ρ.rd.kv.ch0 = alarmChain on false false` at `on = true`) disagree on the auth
layer. -/
theorem kvInv_ch0_on_false (γ : ServerRaftNames) (γk : KVNames)
    (h : γk.ch0 = apply.alarmChain true false false) :
    ⊢ kvInv (GF := GF) γ γk ={⊤}=∗ False := by
  iintro #Hinv
  imod kvInv_ch0_off γ γk $$ Hinv with %h0
  ipureintro
  have := congrArg apply.Chain.authOn (h.symm.trans h0)
  simp at this

end lemmas

end EtcdGrove
end Perennial
