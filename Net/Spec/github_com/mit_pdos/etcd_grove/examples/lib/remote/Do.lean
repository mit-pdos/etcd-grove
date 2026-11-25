/-
`Do(addr, in, codec, d)`: one operation, of input `iv i`, at the node at `addr` (`remoteAddr`), with
the codec `cd` (`codecOk`). A write gets one attempt, a read `ReadTries`; `Do` returns the output
the far side answered, or `i`'s unknown output.

The caller hands the operation's update through a choice (`known`, `bs`), made before the first
attempt from `Do`'s prophecies (which attempt is answered with a known output, if any, and the bytes
`bs` of that answer): if one will be, a slot update `slotUpd R i Φb` (it goes to that attempt's slot:
a write's `lin`, committed at most once, a read's `□ lin`, which the far side may fire several times) and a way from
`Φb o` of the answered output, whose bytes are `bs`, to `Φ o` (`Do` returns the output with `Φ` of
it; a read commits at the first firing whose output's bytes are `bs`: `pend_choice`);
if none will be, `Ψ` and the update with no result (it goes to the one attempt's slot, a write's,
where the far side may fire it, once, or never), `Do` returning the unknown output with `Ψ`. A
read's other attempts get the read's update with no result, which the caller gives persistently
(it changes nothing: `reads_stay`). Each attempt spends one of `addr`'s call units: the caller
hands `readTries` (`budUnits`). A request longer than `maxLen` is never sent (`Do` never
returns). Proved in `Net/Proof/.../lib/remote/Do.lean`.
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
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev Do.spec : Prop :=
  ∀ {J : Type} (R : RBase GF St J I O) (a : GoString) (i : I) (Φ : O → IProp GF) (Ψ : IProp GF)
    (cd : remote.Codec) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ mapCtx (Gg := hG.goose_globalGS) (I := I) ∗ remoteAddr (Gg := hG.goose_globalGS) R a ∗
      codecOk R cd ∗ budUnits (Gg := hG.goose_globalGS) a readTries ∗ (if R.B.isWrite (R.mi i) then iprop(True) else □ lin (Gg := hG.goose_globalGS) R i (fun _ => iprop(True))) ∗
      (∀ (known : Bool) (bs : List w8), |={⊤}=> if known then
        (∃ Φb : O → IProp GF, slotUpd (Gg := hG.goose_globalGS) R i Φb ∗
          (∀ o, ⌜R.encOut (R.ov o) = bs⌝ -∗ Φb o -∗ £ 1 ={⊤}=∗ Φ o))
        else (Ψ ∗ lin (Gg := hG.goose_globalGS) R i (fun _ => iprop(True)))) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.Do)) (Val #a)) (Val #(R.iv i))) (Val #cd)) (Val #d))
  {{ (v : GoInterface), RET #v; (∃ o, ⌜v = R.ov o⌝ ∗ Φ o) ∨ (⌜v = R.unk i⌝ ∗ Ψ) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
