/-
The craq kit's server machines (kit.go's `Server`, `runNode`) and the codec's registration
(`Register`): over Net's `SetCodec`, go-craq's packages' specs (`Specs.lean`, taken as theorem
arguments as paxos's `KitProof.lean` does), the bindings' receivers (`Netrpc/BindingsProof.lean`)
and net/rpc over HTTP's server side (`RpcHttpServe`, H2/H3).

Open points carried as preconditions (notes/dsv-craq.md, P5): a machine's codec registry at its
initial state (`codecFresh`: `codecUnset` and `codecMu`'s mutex, from net/rpc's initialization,
which Net has not proved), its mux at its initial state (`muxOwner []`, H4 open point 2), and
net/rpc's server variables (`srvEnv`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitProof
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.BindingsProof
public import Net.Proof.net.rpc.SetCodec

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.despreston.go_craq.examples.craqnet

open github_com.despreston.go_craq github_com.despreston.go_craq.netrpcP

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions]
variable [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF] [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

/-- A machine's codec registry at its initial state (net/rpc's initialization's; open point). -/
def codecFresh : IProp GF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) net.rpc.codecInv ∗ net.rpc.codecUnset)

/-- `Register()`: the kit's codec registered. -/
theorem wp_Register (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Register)) (Val #()))
    {{ RET #(); net.rpc.codecSet craqCodec }} := by
  unfold codecFresh
  wp_start as ⟨#Hmu, Hun⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a0»
  ipersist «$a0»
  wp_apply wp_SetCodec craqCodec _ $$ [Hun]
  · isplitr
    · iexact Hmu
    isplitl [Hun]
    · iexact Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      isplitr
      · iapply craqCodec_encOk
      isplitr
      · iapply craqCodec_decOk
      · iapply craqCodec_rcvOk
    · ipureintro; exact Hnn
  iintro #Hcs
  wp_auto
  iapply HΦ
  iexact Hcs

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
