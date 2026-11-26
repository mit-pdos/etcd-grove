/-
`h.Get(key)` on a `textproto.MIMEHeader` map `h` (Go 1.27.3), `key` already canonical (`canonQuick`),
the map and `key`'s values `vs` read (any fractions; `vs` is `[]` when `key` has no entry): the first of
`vs`, `""` if none. Proved in `Net/Proof/net/textproto/MIMEHeader__Get.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.textproto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.textproto.Assumptions]

/-- `key`'s values in the map `ms`, read at `dv`: `vs` the slice's (`[]` if no entry). -/
def mimeVals (ms : GMap GoString GoSlice) (key : GoString) (dv : DFrac) (vs : List GoString) :
    IProp GF :=
  match ms !! key with
  | none => iprop(⌜vs = []⌝)
  | some s => iprop(s ↦*{dv} vs)

/-- See the file header. -/
abbrev MIMEHeader.Get.spec : Prop :=
  ∀ (h : Loc) (dq : DFrac) (ms : GMap GoString GoSlice) (key : GoString) (dv : DFrac)
    (vs : List GoString),
  {{ (⌜net.http.canonQuick key = true⌝ ∗ h ↦${dq} ms ∗ mimeVals ms key dv vs : IProp GF) }}
    (App (Val #(methods net.textproto.MIMEHeader.ty go!"Get" #h)) (Val #key))
  {{ RET #(vs.head?.getD []); h ↦${dq} ms ∗ mimeVals ms key dv vs }}

end spec

end net.textproto
end Perennial
