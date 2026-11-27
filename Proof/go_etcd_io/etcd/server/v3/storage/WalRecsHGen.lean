/- Lean-first (no Rocq counterpart).

# The WAL's history does not depend on the generation (etcd-dist D6, T7, 2026-11-25)

`walHistH` (`WalRecsH.lean`, sealed) names only the WAL's ghost state (`walDiskAtI`, the history's
authority, `walNamed`: global ghost names), none of a generation's local state; so the history the old
generation's durability invariant holds is the history at the new generation. T2's crash law
(`rnDurK_crash.law`) hands it to its callback at the old generation, and T5's `walHistH_crash` reads it
at the new one (T7's `memberDur_crash`). (P5 (b), 2026-11-26: until then of the records with their
history, `walRecsH`.)
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
variable [lctx : GoLocalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The history at one generation is the history at any other** (both at the Go context `lctx`, which
the program's instances are over). -/
theorem walHistH_gen (L L' : GooseLocalGS GF) (h : WalH GF) (Hs : WalHist) (sized : Bool) :
    walHistH (hG := ⟨G, { L with goose_go_local_context := lctx }⟩) h Hs sized ⊣⊢
      walHistH (hG := ⟨G, { L' with goose_go_local_context := lctx }⟩) h Hs sized := by
  unfold walHistH; exact .rfl

end gen

end EtcdGrove
end Perennial
