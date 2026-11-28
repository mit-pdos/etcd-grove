/-
The proof of `Orch.spec`: `remote.Check` with `Model()` (`isModel cS`), `Codec()`, `Gen`
(`genSpec`), `Ops = 20` and `attempt()`; its premises: the masks (`pendN_syncN`,
`lintestN_disj`), `cS_pendDec`, the store's state timeless (`cR_timeless`), the bounds, and
`context`'s `isClosedchanInit` from the program's initialization.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Orch
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Model
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Codec
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Gen
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.attempt
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Perennial.Proof.context.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem Orch.wp_proof
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_attempt : attempt.spec (GF := GF) (hG := hG))
    (wp_Check : remote.Check.spec (GF := GF) (hG := hG) (St := w64) (I := Bool) (O := w64)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro γs γp addrs addrL hlen hrb
  wp_start as ⟨#Haddrs, #Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_auto
  wp_apply wp_Model as %m #Hm
  wp_apply (wp_Codec γs) as %cd #Hcd
  wp_apply wp_attempt as %d -
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hE : (↑pendN : CoPset) ⊆ ⊤ \ (cR (GF := GF) γs).Eop := pendN_syncN
  have hL : (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ ((cR (GF := GF) γs).Eop ∪ ↑pendN) :=
    lintestN_disj
  have hlen' : sint.Z addrs.len = 2 := by
    have := Hal.1; rw [hlen] at this; word
  wp_apply wp_Check (cR γs) cS γp m addrs addrL cd _ (W64 20) d hE hL (cS_pendDec γs) (cR_encOut_inj γs)
    (fun st => cR_timeless γs st) hrb (by rw [hlen']; decide) (by decide)
    (by rw [hlen']; decide) 60 (by decide) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
    iapply (show ⊢ EtcdGrove.lintest.genSpec (GF := GF)
        (functions github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Gen [])
        (fun x => iprop(∃ i, ⌜x = (cR (GF := GF) γs).iv i⌝)) from wp_Gen)
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
