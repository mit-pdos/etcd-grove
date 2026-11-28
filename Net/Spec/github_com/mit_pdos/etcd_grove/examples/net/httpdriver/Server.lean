/- Lean-first (no Rocq counterpart).

`Server()`: a `ServeMux` with the handlers `/echo` and `/status` (`NewServeMux`, `HandleFunc`), frozen,
served at `Addr` (`net.Listen`, `http.Serve`) with the protocol `drvP` (`protoLis`). From the boot:
Go 1.22's matcher (`use121`), `maxSlice`'s value, the server's variables.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs
public import Net.Proof.net.http.MuxDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS RespSt)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev Server.spec : Prop :=
  ∀ (ms : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver ∗
      ⌜threadBound GF ≤ 2 ^ 30⌝ ∗ globalAddr net.http.use121 ↦□ false ∗
      globalAddr net.http.maxSlice ↦□ ms ∗ net.http.httpSrvEnv (GF := GF) ∗
      net.http.protoLis (Gg := hG.goose_globalGS) addrS drvP }}
    (App (Val (@! Server)) (Val #()))
  {{ RET #(); True }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
