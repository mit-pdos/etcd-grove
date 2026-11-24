/- Lean-first (no Rocq counterpart).

# `callOn`'s proof

The workers' wait group is `sync.tokJoin`'s (as net/rpc's `ServeCodec`: each `Add(1)` deposits the
caller's thread token, the worker's deferred `Done` gives one back), with no lending. Each worker
takes 8 credits; each of its calls one (`randomArgs`), made with `Call` or with `Go` and a receive on
its `Done` channel (the steps of `Client.Call`'s proof), its outcome checked (`check`, `EchoCall.lean`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.callOn
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.randomArgs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.below
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.EchoCall
public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.Client__Go
public import Perennial.Proof.sync.WaitGroupTokJoin
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

def wkN : Namespace := nroot.@"rpcdriver.workers"

/-- A call's outcome as `Client.Call.spec` gives it, as `check` takes it. -/
theorem echo_outcome (pa pr : Loc) (id : w64) (dsl : GoSlice) (data : List w8)
    (fail : GoString) (err : GoInterface) :
    ((⌜err = interface.nil⌝ ∗ echoRargs (GF := GF) pa id dsl data fail ∗
        ∃ rep, echoTheta pr id data fail rep true) ∨
      (∃ msg : GoString, ⌜msg ≠ [] ∧ err = net.rpc.serverErr msg⌝ ∗ net.rpc.errMsg err msg ∗
        echoRargs pa id dsl data fail ∗ (∃ rep, echoPhi id data fail rep msg) ∗ echoD pr) ∨
      (⌜err ≠ interface.nil ∧ net.rpc.notServerErr err⌝ ∗ models_lab.errAny err ∗ True)) ⊢
    callOutcome pa pr id dsl data fail err := by
  iintro H
  iunfold callOutcome
  icases H with (⟨%He, HR, %rep, HT⟩ | ⟨%msg, ⟨%Hm, %He⟩, -, HR, ⟨%rep, HP⟩, -⟩ | ⟨%He, -, -⟩)
  · ileft
    iunfold echoRargs at HR
    icases HR with ⟨Ha, Hd⟩
    iunfold echoTheta at HT
    simp only [↓reduceIte]
    icases HT with ⟨%hf, %dsl', Hr, Hd'⟩
    iframe Ha Hd
    isplitr
    · ipureintro; exact ⟨He, hf⟩
    iexists dsl'; iframe
  · iright; ileft
    iunfold echoRargs at HR
    icases HR with ⟨Ha, -⟩
    iunfold echoPhi at HP
    icases HP with %HP
    iexists msg
    iframe Ha
    ipureintro
    refine ⟨He, ?_⟩
    rcases HP with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨hs, -⟩
    · exact absurd hm Hm
    · exact .inl hm
    · exact .inr hs
  · iright; iright; ipureintro; exact He

theorem callOn.wp_proof (L : CodecLaws (GF := GF))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_randomArgs : randomArgs.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_Call : net.rpc.Client.Call.spec (GF := GF) (hG := hG))
    (wp_Go : net.rpc.Client.Go.spec (GF := GF) (hG := hG)) :
    callOn.spec (GF := GF) (hG := hG) := by
  intro γid γb c ids W a hSS
  wp_start as ⟨%Hb, #Hf, #Hstr, #Hcl, #Hset, #Hctr, Hcred, Htok⟩
  wp_auto
  sorry

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
