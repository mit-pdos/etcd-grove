/-
Lean-first (no Rocq counterpart).

The proof of `Check` (D20 (c)): `Run`'s premises. The model is `Model()`'s (`isModel_of_step`
of `Model.spec`'s parts); the closure `func(input any) any { return Apply(cli, input) }` meets
`applySpec` from `Apply.spec`, its update passed through the closure's return (`Apply`'s mask
`linkvE`, disjoint from `lintestN`: `lintestN_linkvE`); `Gen` is `Gen.spec`'s; the clock is
`CounterClock()`'s, its invariant at `clockN`; the library starts at the model's `kvInit`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine go_etcd_io.etcd.server.v3.etcdserver

/-- The clock's invariant's namespace. -/
def clockN : Namespace := nroot .@ "linkv_clock"

/-- `Apply`'s mask is not `lintest`'s. -/
theorem lintestN_linkvE : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ linkvE := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  unfold linkvE at h'
  rcases Iris.Std.LawfulSet.mem_union.1 h' with h' | h'
  · rcases Iris.Std.LawfulSet.mem_union.1 h' with h' | h'
    · exact ndot_ne_disjoint nroot (by decide : "lintest" ≠ "raft_commit") p ⟨hp, h'⟩
    · exact ndot_ne_disjoint nroot (by decide : "lintest" ≠ "server_kv") p ⟨hp, h'⟩
  · exact ndot_ne_disjoint nroot (by decide : "lintest" ≠ "linkv") p ⟨hp, h'⟩

/-- The clock's mask is not `lintest`'s. -/
theorem lintestN_clockN : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑clockN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' =>
    ndot_ne_disjoint nroot (by decide : "lintest" ≠ "linkv_clock") p ⟨hp, h'⟩⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

theorem Check.wp_proof
    (wp_Run : lintest.Run.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Apply : Apply.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro _ γ cl ep V E γr cid mid clients ops dur hAs Hrb H0 H31 Hops Hmul
  wp_start as ⟨#Hcc, #Hcl, #Hone, #Hput, #Hrange, #Hinv, Hst⟩
  wp_auto
  ipersist cli
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #HA := wp_Apply γ cl ep V E γr cid mid hAs $$ Hpkg Pcli Hcl Hone Hput Hrange Hinv
  wp_apply wp_Model as %m ⟨%Hp, #Hinit, %Hsc, #Hstep, #Heh⟩
  ihave #Hm := isModel_of_step linkvS m $$ [Hinit Hstep Heh]
  · iframe Hinit Hstep Heh
    ipureintro; exact ⟨Hp, Hsc⟩
  wp_apply wp_CounterClock clockN Hrb as %clock ⟨%clockVal, #Hclk, Hc0⟩
  wp_apply wp_Run (KVSet GoString GoString) linkvS m _ _ clock linkvInOk (linkvState γ) clockVal
    (W64 0) linkvE ↑clockN clients ops dur lintestN_linkvE lintestN_clockN H0 H31 Hops Hmul
    $$ [Hst Hc0]
  · iframe Hc0 Hcc Hm Hclk
    isplitr
    · -- the closure: `Apply`'s update, passed through its return
      unfold lintest.applySpec
      iintro %i
      imodintro
      iintro %Φ' Hin HAU
      wp_auto
      wp_bind (App (App (Val _) (Val _)) (Val _))
      iapply HA $$ %i Hin
      inext
      imod HAU with ⟨%S, Hs, Hc⟩
      imodintro
      iexists S
      iframe Hs
      iintro %S' %o Hb
      imod Hc $$ Hb with HQ
      imodintro
      iintro Hio
      ihave HQ := HQ $$ Hio
      wp_auto
      iexact HQ
    isplitr
    · iapply wp_Gen
    · iExactEq Hst; rfl
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro; exact Hr

end proof

end linkv
end EtcdGrove
end Perennial
