/-
`Report(addr, in, codec, d)`: one operation, of input `iv i`, at the node at `addr`, which serves the
service `S` (`svcAddr`), with the codec `cd` (`wireOk`: `S`'s encodings and decodings), in one attempt
(`attempt`). The caller hands the slot's update `S.upd i Φ` and one of the address's call units
(`budUnit a`); `Report` returns `true` only with an
answer that decoded: an output `ov o` with `Φ o`, or an answer to `i` that is not an output
(`S.unkAns i v`). With `false` (no answer that decodes) the update stays in the slot: the far side
may claim it later, or never. A request longer than `maxLen` is never sent (`Report` never returns).

For a report (`reportSvc W P Q`: the far side's loop, given `P i`, answers an output `o` with
`Q i o`, `reportOp_svcOp`) the caller hands `P i ∗ ∀ o, Q i o -∗ Φ o` and there is no other answer
(`unkAns` is `False`): with `Φ := Q i`, `Report` returns `true` only with an output `o` and
`Q i o`. Proved in `Net/Proof/.../lib/remote/Report.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev Report.spec : Prop :=
  ∀ (S : RSvc GF I O) (a : GoString) (i : I) (Φ : O → IProp GF) (cd : remote.Codec) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ mapCtx (Gg := hG.goose_globalGS) (I := I) ∗ svcAddr (Gg := hG.goose_globalGS) S a ∗
      wireOk S cd ∗ S.upd i Φ ∗ budUnit (Gg := hG.goose_globalGS) a }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.Report)) (Val #a)) (Val #(S.iv i))) (Val #cd)) (Val #d))
  {{ (v : GoInterface) (ok : Bool), RET (PairV #v #ok);
      ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ((∃ o, ⌜v = S.ov o⌝ ∗ Φ o) ∨ ⌜S.unkAns i v⌝)) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
