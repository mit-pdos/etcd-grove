/-
The proof of `Spec/go_etcd_io/bbolt/DB__Stats.lean` (U5, `notes/bbolt-proof-plan.md`): the
caller's `statlock` reader token, from the pool (`statSlot none`: the `threadTok`) or from its
read transaction's exclusive part (`statSlot (some …)`), around `RLock`/`RUnlock`.
-/
module

public import Spec.go_etcd_io.bbolt.DB__Stats
public import Proof.go_etcd_io.bbolt.Txn.StatSlot
public import Perennial.Proof.sync.Results
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.Stats.wp_proof : DB.Stats.spec (GF := GF) (hG := hG) := by
  intro _ _ _ db γ o
  wp_start as ⟨#Hdb, Hslot⟩
  unfold isBolt isBoltDef
  icases Hdb with ⟨%p, %sp, %t0, #Hb⟩
  by_cases hsp : sp = null
  · subst hsp
    unfold isBoltP isBoltCoreP dbFixed
    icases Hb with ⟨⟨-, -, -, #Hpkg, -, ⟨-, #Hsp, -⟩, -⟩, -⟩
    wp_auto
    iapply HΦ $$ Hslot
  imod statSlot_tok db γ o p sp t0 $$ [Hslot] with Htok
  · iframe Hb Hslot
  unfold isBoltP isBoltCoreP dbFixed
  icases Hb with ⟨⟨-, -, -, #Hpkg, -, ⟨-, #Hsp, -⟩, -⟩, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  icases Htok with ⟨Hst, Hcl⟩
  wp_if_destruct
  · contradiction
  wp_apply sync.RWMutex.wp_RLock $$ [$Hsync $Hst] as ⟨Hst, HP⟩
  unfold Ps
  simp only [hsp, ↓reduceIte]
  icases HP with ⟨%s, Hs⟩
  wp_auto
  wp_apply_core sync.RWMutex.wp_RUnlock $$ [Hst Hs] [HΦ Hcl «$res0» s]
  · iframe Hsync Hst; iexists s; iexact Hs
  iintro Hst
  imod Hcl $$ Hst with Hslot
  wp_auto
  iapply HΦ $$ Hslot

end proof

end bbolt
end EtcdGrove
end Perennial
