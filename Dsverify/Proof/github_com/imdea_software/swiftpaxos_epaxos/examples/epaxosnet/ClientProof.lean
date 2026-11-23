/-
The EPaxos kit's client machines and orchestrator (kit.go's `Client`, `Orch`, `ClientAddrs`, `start`,
`attempt`), in paxos's shape (`paxosnet/KitProof.lean`): the callees' specs (`Op`, `ServerAddrs`,
`Model`, `Codec`, `Gen`, remote's `ServeClient` and `Check`, `time.Sleep`, `time.Now`,
`time.Since`) are theorem arguments,
discharged at the top level.

* `Client(c)`: remote's `newClient` returns the server addresses' slice (read-only, `tok sys`
  says which: a pure fact). `op` sleeps what is left of `start(c)` since `t0` (`Client`'s
  `time.Now()`, written once: read-only), then is `Op` on the slice; its update is
  remote's `lin` through `lin_opU`, and an answer's bytes are below `2 ^ 16` (`Op.spec`), so
  `epR_ov` applies.
* `Orch()`: remote's `Check`, whose premises on the store (`PendDec (epR γ) epS`, the outputs'
  bytes injective) are `ModelDefs.lean`'s `epS_pendDec`, `epR_encOut_inj`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.KitSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ModelDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.OpDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServerSpecs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Perennial.Spec.time.Sleep
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
  github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]
variable [net.rpc.Assumptions] [field_sem : net.FieldAssumptions] [π : NetProtoGS]
variable [master.Assumptions] [epaxos.Assumptions] [log.Assumptions] [net.http.Assumptions]
variable [ρ : RemoteGS] [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

set_option goose.wp.extras true

/-- `ClientAddrs()` returns a new slice of the client machines' addresses. -/
theorem wp_ClientAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ClientAddrs))
        (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* clientAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) clientAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `attempt()`: some duration. -/
theorem wp_attempt :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.attempt))
        (Val #()))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-- `start(c)`: some duration. -/
theorem wp_startDelay (c : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.start))
        (Val #c))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-! ## The orchestrator -/

theorem pendN_ep : (↑pendN : CoPset) ⊆ ⊤ \ epEop := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  rw [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, ?_⟩
  unfold epEop epN
  intro h
  exact ndot_ne_disjoint nroot (show "remote" ≠ "epaxos" by decide) p ⟨h1, h⟩

theorem lintestN_ep :
    (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (epEop ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · unfold epEop epN
    intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "epaxos" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

theorem pendCtx_epS (γ : EpNames) (γp : PendNames) :
    pendCtx (Gg := hG.goose_globalGS) (epR γ) (epS0 (GF := GF)) γp =
      pendCtx (Gg := hG.goose_globalGS) (epR γ) (epS (GF := GF)) γp := rfl

theorem pendLib_epS (γp : PendNames) :
    pendLib (Gg := hG.goose_globalGS) (epS0 (GF := GF)) γp (epS0 (GF := GF)).M.init =
      pendLib (Gg := hG.goose_globalGS) (epS (GF := GF)) γp (epS (GF := GF)).M.init := rfl

/-- **Orch**, from `remote.Check`'s spec, with its premises on the store `epR γ` and its model
`epS` (`ModelDefs.lean`'s `epS_pendDec`, `epR_encOut_inj`). -/
theorem Orch.wp_proof (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Check : github_com.mit_pdos.etcd_grove.examples.lib.remote.Check.spec (GF := GF) (hG := hG)
      (St := KvS) (I := EIn) (O := BStr)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γ γp hrb
  rw [pendCtx_epS, pendLib_epS]
  wp_start as ⟨#Hra, #Hmap, #Hpend, Hlib⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply wp_Model as %m #Hm
  wp_apply wp_ClientAddrs as %addrs Haddrs
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Haddrs with #Haddrs
  imodintro
  wp_apply (wp_Codec γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen' : sint.Z addrs.len = 10 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  wp_apply wp_Check (epR γ) epS γp m addrs clientAddrs cd _ _ d pendN_ep lintestN_ep
    (epS_pendDec γ) (epR_encOut_inj γ) (fun st => epR_timeless γ st) hrb (by rw [hlen']; decide)
    (by decide) (by rw [hlen']; decide) $$ [Hlib]
  · iframe #
    iframe Hlib
    iapply (show ⊢ EtcdGrove.lintest.genSpec (GF := GF)
        (functions github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Gen [])
        (fun x => iprop(∃ i, ⌜x = (epR (Gg := hG.goose_globalGS) γ).iv i⌝)) from wp_Gen)
  iapply HΦ
  itrivial

/-! ## The client machines -/

omit ρ bvi in
/-- A slot's update gives its `lin` (a read's persistently). -/
theorem slotUpd_lin (R : RBase GF KvS EIn BStr) (i : EIn) (Φ : BStr → IProp GF) :
    slotUpd (Gg := hG.goose_globalGS) R i Φ ⊢ lin (Gg := hG.goose_globalGS) R i Φ := by
  unfold slotUpd
  split
  · exact .rfl
  · exact BI.intuitionistically_elim


theorem Client.wp_proof (wp_Op : examples.epaxosnet.Op.spec (GF := GF) (hG := hG))
    (wp_ServerAddrs : ServerAddrs.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := GF) (hG := hG) (I := EIn) (O := BStr)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γ c hc
  wp_start as ⟨#Hci, #Hra, #Hmap⟩
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_ServerAddrs as %sl #Hsl
  wp_apply wp_Now as %t0 -
  ipersist t0
  ipersist c
  ipersist addrs
  ipersist newClient
  ipersist op
  wp_apply wp_ClientAddrs as %asl Hasl
  ihave %Hal := ownSlice_len _ _ _ $$ Hasl
  have hal : sint.Z asl.len = 10 := by
    have := Hal.1; simp only [clientAddrs, List.length_cons, List.length_nil] at this; word
  have hcn : uint.nat c < clientAddrs.length := by
    simp only [clientAddrs, List.length_cons, List.length_nil]; omega
  list_elem clientAddrs (uint.nat c) as a
  have hca : a = clientAddrs.getD (uint.nat c) [] := by
    simp [List.getD_eq_getElem?_getD, Ha_lookup]
  subst hca
  rw [ite_eq_left ⟨by word, by rw [hal]; word⟩]
  wp_apply wp_load_slice_index asl (sint.Z c) clientAddrs _ _ (by word) $$ [Hasl] with Hasl
  · iframe; ipureintro; rw [show (sint.Z c).toNat = uint.nat c by word]; exact Ha_lookup
  wp_apply (wp_Codec γ) as %cd #Hcd
  wp_apply wp_attempt as %d -
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (epR γ)) _ _ _ _ cd d
    (fun sys => iprop(⌜sys = interface.mkOk (go.GoType.SliceType go.string) #sl⌝)) $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · -- the operation: `start(c)`, then `Op` on the server addresses
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Ψ
    iintro !> %Φr ⟨%Hsys, Hupd⟩ HΦr
    subst Hsys
    ihave HU := slotUpd_lin _ i Ψ $$ Hupd
    ihave HU := lin_opU γ i Ψ $$ HU
    simp only [epR, ivE, inV, inE]
    wp_auto
    wp_apply wp_startDelay c as %dl -
    wp_apply wp_Since as %el -
    wp_if_destruct
    all_goals (try wp_apply wp_Sleep)
    all_goals
      wp_apply wp_Op γ sl c i.1 (fun o => Ψ (bnd (outBytes o))) i.2 hc $$ [HU] as %o Ho
      · iframe #
        iframe HU
      iapply HΦr
      isplitr
      · itrivial
      icases Ho with (%Ho | ⟨%r, %Hr, HΨ⟩)
      · subst Ho
        iright
        ipureintro; rfl
      · obtain ⟨rfl, hlen⟩ := Hr
        ileft
        iexists bnd (outBytes r)
        iframe HΨ
        ipureintro
        rw [bnd_of (by omega)]
        rfl
  · -- the client's system: the server addresses
    iintro !> %Φr - HΦr
    wp_auto
    iapply HΦr
    ipureintro; rfl

end proof

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
