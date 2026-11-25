/-
`h.Get(key)` on an `http.Header` map `h` (`textproto.MIMEHeader(h).Get(key)`), `key` already canonical
(`canonQuick`): the value of `key`'s line (`hdrGetL`, `""` if none), over the lines `h` owns (`hdrOwn`,
`Header.Get.spec`) or reads (`hdrRO`, `Header.Get.spec_ro`). Proved in `Net/Proof/net/http/Header__Get.lean`.
Lean-first.
-/
module

public import Net.Proof.net.http.ProtoDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev Header.Get.spec : Prop :=
  ∀ (h : Loc) (hb : List HdrLine) (key : GoString), canonQuick key = true →
  {{ hdrOwn (GF := GF) h hb }}
    (App (Val #(methods net.http.Header.ty go!"Get" #h)) (Val #key))
  {{ RET #(hdrGetL hb key); hdrOwn h hb }}

/-- See the file header. -/
abbrev Header.Get.spec_ro : Prop :=
  ∀ (h : Loc) (hb : List HdrLine) (key : GoString), canonQuick key = true →
  {{ hdrRO (GF := GF) h hb }}
    (App (Val #(methods net.http.Header.ty go!"Get" #h)) (Val #key))
  {{ RET #(hdrGetL hb key); True }}

end spec
end net.http
end Perennial
