/- Lean-first (no Rocq counterpart).

The proof of `Orch.spec`: `remote.Run` at the store `kvR γk` and porcupine's model `linkvtxnS`
(`Model()`'s `isModel`, `isModel_of_step`), with `Codec()` (`codecOk`), txnlin's `Gen` (its inputs
`GenIn`, so each is `iv` of a `VIn`), `ops` and `Attempt`; `Run`'s premises: the masks (`kvEop`,
`pendN`, `lintestN`: distinct names under `nroot`), `kvPendDec`, `kvR_hinj`, the store's state
timeless (`kvR_timeless`), the bounds (`kvOrchPre`), and `context`'s `isClosedchanInit` from the
program's initialization.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Orch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Codec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Gen
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Run
public import Perennial.Proof.context.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open EtcdGrove EtcdGrove.etcd_txnlin
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## Masks -/

theorem pendN_kvEop : (↑pendN : CoPset) ⊆ ⊤ \ kvEop := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  simp only [kvEop, CoPset.in_diff, CoPset.in_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · intro h
    exact ndot_ne_disjoint nroot (show "remote" ≠ "raft_commit" by decide) p ⟨h1, h⟩
  · intro h
    exact ndot_ne_disjoint nroot (show "remote" ≠ "server_kv" by decide) p ⟨h1, h⟩

theorem lintestN_kvEop : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ (kvEop ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  simp only [kvEop, CoPset.in_diff, CoPset.in_union, not_or]
  refine ⟨CoPset.mem_full, ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "raft_commit" by decide) p ⟨hp, h⟩
  · intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "server_kv" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem Orch.wp_proof
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Run : github_com.mit_pdos.etcd_grove.examples.lib.remote.Run.spec (GF := GF) (hG := hG) (St := MS) (I := VIn) (O := VOut)) :
    Orch.spec (GF := GF) (hG := hG) := by
  intro nodes ns ops tmo
  wp_start as ⟨#Hnodes, Hpre⟩
  iunfold kvOrchPre at Hpre
  icases Hpre with ⟨%γk, %γ, %Hb, #Hra, #Hmap, #Hpend, Hlib, Hbud⟩
  obtain ⟨hrb, hlen, hops, hprod⟩ := Hb
  ihave #Hcc : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_auto
  wp_apply wp_Model as %m ⟨%Hp, #Hi, %Hsc, #Hs, #Heh⟩
  ihave #Hm : github_com.anishathalye.porcupine.isModel (linkvtxnS (GF := GF)) m $$ []
  · iapply github_com.anishathalye.porcupine.isModel_of_step
    iframe Hi Hs Heh
    isplitr
    · ipureintro; exact Hp
    ipureintro; exact Hsc
  wp_apply (wp_Codec γk) as %cd #Hcd
  ihave #Hgen : lintest.genSpec (GF := GF)
      (functions github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Gen [])
      (fun x => iprop(∃ i, ⌜x = (kvR (GF := GF) γk).iv i⌝)) $$ []
  · ihave #Hg := (show ⊢ lintest.genSpec (GF := GF)
        (functions github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Gen []) linkvInOk from wp_Gen)
    iunfold lintest.genSpec at Hg
    iunfold lintest.genSpec
    iintro %id
    imodintro
    iintro %Φ %hid HΦ
    iapply Hg
    · ipureintro; exact hid
    inext
    iintro %x #Hx
    iapply HΦ
    imodintro
    ipure Hx
    obtain ⟨y, rfl, hy⟩ := Hx
    ipureintro
    exact ⟨⟨y, hy⟩, rfl⟩
  ihave %Hal := ownSlice_len _ _ _ $$ Hnodes
  have hlen' : sint.Z nodes.len = ns.length := by
    have := Hal.1; word
  wp_apply wp_Run (kvR γk) linkvtxnS γ m nodes ns cd _ ops _ tmo pendN_kvEop lintestN_kvEop
    (kvPendDec γk) (kvR_hinj γk) (fun st => kvR_timeless γk st) hrb (by rw [hlen']; omega) hops
    (by rw [hlen']; exact hprod) (sint.nat ops * readTries) (Nat.le_refl _) $$ [Hlib Hbud]
  · iframe #
    iframe Hlib Hbud
  iintro %r %hr
  wp_auto
  iapply HΦ
  ipureintro
  exact hr.1

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
