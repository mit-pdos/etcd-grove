/- Lean-first (no Rocq counterpart).

# The WAL's records do not depend on the generation (etcd-dist D6, T7, 2026-11-25)

`walRecsH` (`WalRecsH.lean`, sealed) names only the WAL's ghost state (`walDiskAtI`, the history's
authority, `walNamed`: global ghost names), none of a generation's local state; so the records the old
generation's durability invariant holds are the records at the new generation. T2's crash law
(`rnDurK_crash.law`) hands them to its callback at the old generation, and T5's `walRecsH_crash` reads them
at the new one (T7's `memberDur_crash`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsH
import all Proof.go_etcd_io.etcd.server.v3.storage.WalRecsH

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The records at one generation are the records at any other.** -/
theorem walRecsH_gen (L L' : GooseLocalGS GF) (h : WalH GF) (σ : StorContents) (Hs : WalHist)
    (sized : Bool) :
    walRecsH (hG := ⟨G, L⟩) h σ Hs sized ⊣⊢ walRecsH (hG := ⟨G, L'⟩) h σ Hs sized := by
  unfold walRecsH; exact .rfl

end gen

end EtcdGrove
end Perennial
