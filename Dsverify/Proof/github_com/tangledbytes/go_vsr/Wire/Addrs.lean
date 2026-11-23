/-
The go-vsr addresses of the vr kit's machines (notes/dsv-vr.md): one list, `VsrWire.addrs`, what
the kit's `Addrs()` returns (`examples/vsrnet/KitLib.lean`, `wp_Addrs`); the wire's protocols
(`Wire/Basic.lean`) and `ipv4port`'s configured addresses (`Spec/ipv4port.lean`) are over it.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

noncomputable section

namespace VsrWire

open Perennial

/-- The go-vsr addresses of the machines (the kit's `Addrs()`, `kit.go`: machine `i` at
`127.0.0.1:(7500 + i)`; 0 the orchestrator (unused), client `c` on `1 + c`, then the servers); the lab's
`github_com.tangledbytes.go_vsr.addrs` (`VsrNetSpec.lean`, its `Addrs()`). -/
def addrs : List GoString :=
  [go!"127.0.0.1:7500", go!"127.0.0.1:7501", go!"127.0.0.1:7502",
   go!"127.0.0.1:7503", go!"127.0.0.1:7504", go!"127.0.0.1:7505",
   go!"127.0.0.1:7506", go!"127.0.0.1:7507", go!"127.0.0.1:7508",
   go!"127.0.0.1:7509", go!"127.0.0.1:7510", go!"127.0.0.1:7511"]

end VsrWire
